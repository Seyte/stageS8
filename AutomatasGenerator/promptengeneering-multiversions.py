import openai
import os
from filecomparator import compare_files
from datagenerator import generate_files
import time
import matplotlib.pyplot as plt
NB_NODES_TO_TEST = 10
NB_TEST_PER_NODE = 25
NB_GENERATIONS_PER_PROMPT = 5  # number of generations per prompt
PRICE_PER_TOKEN = 0.002/1000

percentage_of_wrong_lines = [0]*NB_NODES_TO_TEST
API_KEY = open(str(os.path.dirname(os.path.abspath(__file__))) + "/openai_key.txt", "r").read()
FIRST_PROMPT = open(str(os.path.dirname(os.path.abspath(__file__))) + "/first_prompt_generateKnowledge.txt", "r").read()
openai.api_key = API_KEY
credits = 0
PATH_TO_DATA = str(os.path.dirname(os.path.abspath(__file__))) + "/../data"
has_succedded = [0]*NB_NODES_TO_TEST
has_one_succedded = [0]*NB_NODES_TO_TEST  # For tracking at least one correct generation

for i in range (2, NB_NODES_TO_TEST + 2):
    print("doing",i,has_one_succedded)
    generate_files(i, NB_TEST_PER_NODE, 1)
    for j in range (1, NB_TEST_PER_NODE + 1):
        PATH_TO_DATA_FILE = PATH_TO_DATA + "/exemple" + str(j) + "/requirement1.txt"
        FILE_TO_TRANSFORM = open(PATH_TO_DATA_FILE, "r").read()
        response = None
        while(response == None):
            try:
                response = openai.ChatCompletion.create(
                    model = "gpt-3.5-turbo",
                    messages = [
                        {"role": "user", "content": FIRST_PROMPT},
                        {"role": "assistant", "content": "Waiting for any prompt."},
                        {"role": "user", "content": "Q:\n" + FILE_TO_TRANSFORM}
                    ],
                    n = NB_GENERATIONS_PER_PROMPT  # number of versions to generate
                )
            except openai.error.RateLimitError:
                print("Rate limit error, waiting 10 seconds...")
                time.sleep(10)
            except openai.error.ServiceUnavailableError:
                print("Service unavailable, waiting for 30 seconds...")
                time.sleep(30)
            except openai.error:
                print("Unknown openai error, waiting for 10 seconds...")
                time.sleep(10)
        credits += response['usage']['total_tokens']
        one_success_in_this_input = False
        for choice in response.choices:
            with open("tmp.txt", "w") as f:
                f.write(choice.message.content)
            comparation = compare_files("tmp.txt", PATH_TO_DATA + "/exemple" + str(j) +"/fsm.dot")
            comparation_lines = comparation.splitlines()
            percentage_of_wrong_lines[i-2] += (len(comparation_lines)-1)/2/len(FILE_TO_TRANSFORM.splitlines())
            if (comparation == "SUCCESS"):
                has_succedded[i-2] += 1
                one_success_in_this_input = True
            os.remove("tmp.txt")
        if one_success_in_this_input:
            has_one_succedded[i-2] += 1

print(has_succedded)
print("In total i used "+ str(credits) + " tokens which corresponds to "+str(float(credits)*PRICE_PER_TOKEN) + " e.")
percentage_of_success = [0]*NB_NODES_TO_TEST
for i in range (0, NB_NODES_TO_TEST):
    percentage_of_success[i] = has_succedded[i]/(NB_TEST_PER_NODE * NB_GENERATIONS_PER_PROMPT)

percentage_of_one_success = [0]*NB_NODES_TO_TEST
for i in range (0, NB_NODES_TO_TEST):
    percentage_of_one_success[i] = has_one_succedded[i]/NB_TEST_PER_NODE

print(percentage_of_wrong_lines)
for i in range (0, NB_NODES_TO_TEST):
    percentage_of_wrong_lines[i]  = percentage_of_wrong_lines[i]/(NB_TEST_PER_NODE * NB_GENERATIONS_PER_PROMPT)
print(percentage_of_wrong_lines)
plt.plot(range(2, NB_NODES_TO_TEST + 2), percentage_of_wrong_lines)
plt.xticks(range(2, NB_NODES_TO_TEST + 2), map(int, range(2, NB_NODES_TO_TEST + 2)))
plt.xlabel("Number of nodes")
plt.ylabel("Percentage of lines with at least one error")
plt.title("Percentage of lines with at least one error for each number of nodes ("+  str(NB_TEST_PER_NODE) +" tests per node)")
plt.savefig('plot.png')
plt.show()

plt.plot(range(2, NB_NODES_TO_TEST + 2), percentage_of_one_success)
plt.xticks(range(2, NB_NODES_TO_TEST + 2), map(int, range(2, NB_NODES_TO_TEST + 2)))
plt.xlabel("Number of nodes")
plt.ylabel("Percentage of at least one good answer per input")
plt.title("Percentage of at least one good answer per input for each number of nodes ("+  str(NB_TEST_PER_NODE) +" tests per node)")
plt.savefig('plot_one_success.png')
plt.show()
