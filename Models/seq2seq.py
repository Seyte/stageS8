import torch
import os
import torch.nn as nn
import torch.optim as optim
import numpy as np
import random
import torch.nn.functional as F
import time
from torch.utils.tensorboard import SummaryWriter  # to print to tensorboard
from sklearn.model_selection import train_test_split

# Training hyperparameters
num_epochs = 100
learning_rate = 0.001
batch_size = 16
model_path = "model.pth"

class CustomDataset(torch.utils.data.Dataset):
    def __init__(self, input_sentences, output_sentences):
        self.input_sentences = input_sentences
        self.output_sentences = output_sentences

    def __getitem__(self, index):
        input_seq = self.input_sentences[index]
        output_seq = self.output_sentences[index]
        return input_seq, output_seq

    def __len__(self):
        return len(self.input_sentences)


    # Prétraitement des données (à adapter selon vos données)
# Load every .dot file content from ./data into an array
input_tokens = {}
output_tokens = {}

target_data = []
for file in os.listdir("./data"):
    if file.endswith(".dot"):
        # Open file and append content to array
        with open(os.path.join("./data", file), "r") as f:
            target_data.append(f.read())

# Load every .txt file content from ./data into an array
input_data = []
for file in os.listdir("./data"):
    if file.endswith(".txt"):
        # Open file and append content to array
        with open(os.path.join("./data", file), "r") as f:
            input_data.append(f.read())
# This is the reverse of input_tokens dictionary


# Traitement en tokens
# Traitement en tokens
for input_seq, target_seq in zip(input_data, target_data):
    for token in input_seq.split():
        if token not in input_tokens:
            input_tokens[token] = len(input_tokens)
    for token in target_seq.split():
        if token not in output_tokens:
            output_tokens[token] = len(output_tokens)

# Conversion des phrases en tokens
input_sequences = []
for input_seq in input_data:
    tokens = input_seq.split()
    sequence = [input_tokens[token] for token in tokens]
    input_sequences.append(sequence)

output_sequences = []
for target_seq in target_data:
    tokens = target_seq.split()
    sequence = [output_tokens[token] for token in tokens]
   
output_tokens["<SOS>"] = len(output_tokens)
output_tokens["<EOS>"] = len(output_tokens)
output_tokens["<PAD>"] = len(output_tokens)
input_tokens["<PAD>"] = len(input_tokens)
input_tokens["<SOS>"] = len(input_tokens)
input_tokens["<EOS>"] = len(input_tokens)
print("len output_tokens: ", len(output_tokens))
print("len input_tokens: ", len(input_tokens))
# Conversion des phrases en tokens
input_sequences = []
for input_seq in input_data:
    tokens = input_seq.split()
    sequence = [input_tokens.get(token) for token in tokens]
    input_sequences.append([input_tokens["<SOS>"]] + sequence + [input_tokens["<EOS>"]])
    
output_sequences = []
for target_seq in target_data:
    tokens = target_seq.split()
    sequence = [output_tokens[token] for token in tokens]
    output_sequences.append([output_tokens["<SOS>"]] + sequence + [output_tokens["<EOS>"]])

# get the length of the longest sequence in input sequences or output sequences
max_len = max([len(seq) for seq in input_sequences + output_sequences])
print("max_len: ", max_len)

input_token_to_word = {v: k for k, v in input_tokens.items()}
output_token_to_word = {v: k for k, v in output_tokens.items()}
# Fonction utilisée pour la création des batchs
def collate_fn(batch):
    # Ensure that batch contains tuples of input and output sequences
    assert all(isinstance(item, tuple) and len(item) == 2 for item in batch), "Each item in the batch must be a tuple of (input_sequence, output_sequence)"

    # Separate input and output sequences
    # dimension : (batch_size, sequence length)
    input_seqs = [item[0] for item in batch]
    output_seqs = [item[1] for item in batch]

    # Pad sequences within each batch
    input_tensor = torch.nn.utils.rnn.pad_sequence(
        [torch.tensor(seq, dtype=torch.long) for seq in input_seqs], batch_first=True,
        padding_value=input_tokens["<PAD>"]
    )
    output_tensor = torch.nn.utils.rnn.pad_sequence(
        [torch.tensor(seq, dtype=torch.long) for seq in output_seqs],
        batch_first=True,
        padding_value=output_tokens["<PAD>"]
    )

    # Transpose the tensors to make sequence length the first dimension
    input_tensor = input_tensor.transpose(0, 1)
    output_tensor = output_tensor.transpose(0, 1)
    # array dimensions : (sequence length, batch_size) (these are the dimension needed for the model)
    
    return input_tensor, output_tensor

# Split data into training and test sets
input_train, input_test, output_train, output_test = train_test_split(
    input_sequences, output_sequences, test_size=0.2, random_state=random.randint(0, 99))
# Create training dataset
train_dataset = CustomDataset(input_train, output_train)
train_loader = torch.utils.data.DataLoader(train_dataset, batch_size=batch_size, shuffle=True, collate_fn=collate_fn)

# Create test dataset
test_dataset = CustomDataset(input_test, output_test)
test_loader = torch.utils.data.DataLoader(test_dataset, batch_size=batch_size, shuffle=False, collate_fn=collate_fn)

def calculate_accuracy(output, target):
    ## print the sentences converted into words
    #output_words = [output_token_to_word[i.item()] for i in output]
    #target_words = [output_token_to_word[i.item()] for i in target]
    #print("output_words: ", output_words)
    #print("target_words: ", target_words)
    ## jump 10 lines
    #print("\n" * 10)
    # Iterate through the output and target sequences
    # until the EOS token is encountered
    num_correct = 0
    for i in range(1,min(len(output), len(target))-1):
        # +1 because the first index of the output is always the <SOS> token
        if output[i] == output_tokens["<EOS>"]:
            break
        if output[i] == target[i]:
            num_correct += 1
    accuracy = num_correct / len(target[:i+1])
    return accuracy

# Encodeur : # couche d'embedding + rnn

class Encoder(nn.Module):
    def __init__(self, input_size, embedding_size, hidden_size, num_layers, p):
        super(Encoder, self).__init__()
        self.dropout = nn.Dropout(p)
        self.hidden_size = hidden_size
        self.num_layers = num_layers

        self.embedding = nn.Embedding(input_size, embedding_size)
        self.rnn = nn.LSTM(embedding_size, hidden_size, num_layers, dropout=p)

    def forward(self, x):
        # x shape: (seq_length, N) where N is batch size
        
        embedding = self.dropout(self.embedding(x))
        # embedding shape: (seq_length, N, embedding_size)

        outputs, (hidden, cell) = self.rnn(embedding)
        # outputs shape: (seq_length, N, hidden_size)

        return hidden, cell

# Décodeur : Embedding + LSTM + lineaire pour prediction du mot
class Decoder(nn.Module):
    def __init__(
        self, input_size, embedding_size, hidden_size, output_size, num_layers, p
    ):
        super(Decoder, self).__init__()
        self.dropout = nn.Dropout(p)
        self.hidden_size = hidden_size
        self.num_layers = num_layers

        self.embedding = nn.Embedding(input_size, embedding_size)
        self.rnn = nn.LSTM(embedding_size, hidden_size, num_layers, dropout=p)
        self.fc = nn.Linear(hidden_size, output_size)

    def forward(self, x, hidden, cell):
        # x shape: (N) where N is for batch size, we want it to be (1, N), seq_length
        # is 1 here because we are sending in a single word and not a sentence
        x = x.unsqueeze(0)

        embedding = self.dropout(self.embedding(x))
        # embedding shape: (1, N, embedding_size)

        outputs, (hidden, cell) = self.rnn(embedding, (hidden, cell))
        # outputs shape: (1, N, hidden_size)

        predictions = self.fc(outputs)

        # predictions shape: (1, N, length_target_vocabulary) to send it to
        # loss function we want it to be (N, length_target_vocabulary) so we're
        # just gonna remove the first dim
        predictions = predictions.squeeze(0)

        return predictions, hidden, cell


class Seq2Seq(nn.Module):
    def __init__(self, encoder, decoder):
        super(Seq2Seq, self).__init__()
        self.encoder = encoder
        self.decoder = decoder

    def forward(self, source, target, teacher_force_ratio=0.90):
        # shape of source : ( seq_length )
        batch_size = source.shape[1]
        # shape of target : ( seq_length )
        target_len = len(target)
        target_vocab_size = len(output_tokens)

        outputs = torch.zeros(target_len, batch_size, target_vocab_size).to(device)
        outputs[0, :, output_tokens["<SOS>"]] = 1  # Set the first character to <SOS>

        hidden, cell = self.encoder(source)

        # Grab the first input to the Decoder which will be <SOS> token
      # Grab the first input to the Decoder which will be <SOS> token
        x = target[0]

        for t in range(1, target_len):
            output, hidden, cell = self.decoder(x, hidden, cell)

            outputs[t] = output
            best_guess = output.argmax(1)

            # Check if the previous token was <EOS> or <PAD>
            is_end = (target[t-1] == output_tokens["<EOS>"]) | (target[t-1] == output_tokens["<PAD>"])

            # If the previous token was <EOS> or <PAD>, set x to <PAD>
            x = torch.where(is_end, torch.tensor(output_tokens["<PAD>"], device=device), best_guess)

            # Use actual next token if teacher forcing, else use the predicted token
            x = target[t] if random.random() < teacher_force_ratio else x

        return outputs


### We're ready to define everything we need for training our Seq2Seq model ###

# Model hyperparameters
load_model = False
device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
input_size_encoder = len(input_tokens)
input_size_decoder = len(output_tokens)
output_size = len(output_tokens)
encoder_embedding_size = 300
decoder_embedding_size = 300
hidden_size = 1024  # Needs to be the same for both RNN's
num_layers = 2
enc_dropout = 0.5
dec_dropout = 0.5

# Tensorboard to get nice loss plot
writer = SummaryWriter(f"runs/loss_plot")
step = 0

encoder_net = Encoder(
    input_size_encoder, encoder_embedding_size, hidden_size, num_layers, enc_dropout
).to(device)

decoder_net = Decoder(
    input_size_decoder,
    decoder_embedding_size,
    hidden_size,
    output_size,
    num_layers,
    dec_dropout,
).to(device)

model = Seq2Seq(encoder_net, decoder_net).to(device)
optimizer = optim.Adam(model.parameters(), lr=learning_rate)

criterion = nn.CrossEntropyLoss(ignore_index=output_tokens["<PAD>"])

for epoch in range(num_epochs):
    print(f"[Epoch {epoch+1}/{num_epochs}]")
    
    model.train()
    total_loss = 0

    for batch_idx, batch in enumerate(train_loader):
        start_time = time.time()
        # shape : ( seq_length, batch_size )
        inp_data = batch[0].to(device)
        # shape : ( seq_length, batch_size )
        target = batch[1].to(device)

        optimizer.zero_grad()
        output = model(inp_data, target)
        output = output[1:].reshape(-1, output.shape[2])
        target = target[1:].reshape(-1)
        
        loss = criterion(output, target)
        total_loss += loss.item()

        loss.backward()
        torch.nn.utils.clip_grad_norm_(model.parameters(), max_norm=1)
        optimizer.step()

        if batch_idx % 3 == 0:
            print(f"  Batch {batch_idx + 1}/{len(train_loader)} Loss: {loss.item():.4f} in {time.time()-start_time:.4f} sec")
    
    #
    model.eval()
    total_accuracy = 0
    nb_tests = 0

    with torch.no_grad():
        for batch in test_loader:
            input_data = batch[0].to(device)
            target = batch[1].to(device)

            output = model(input_data, target, teacher_force_ratio=0)  # No teacher forcing during evaluation

            # Get the predicted tokens
            _, predicted = output.max(dim=2)

            # Calculate accuracy for each sequence in the batch
            for i in range(predicted.size(1)):
                # print target and predicted back into words
                target_sentence = [output_token_to_word[idx.item()] for idx in target[:, i]]
                predicted_sentence = [output_token_to_word[idx.item()] for idx in predicted[:, i]]
                print(f"Target: {target_sentence}")
                print(f"Predicted: {predicted_sentence}")
                print("\n"*3)
                accuracy = calculate_accuracy(predicted[:, i], target[:, i])
                total_accuracy += accuracy
                nb_tests += 1

    avg_accuracy = total_accuracy / nb_tests
    print(f"  Average Accuracy: {avg_accuracy:.4f}")
    avg_loss = total_loss / len(train_loader)
    print(f"  Average Loss: {avg_loss:.4f}")

