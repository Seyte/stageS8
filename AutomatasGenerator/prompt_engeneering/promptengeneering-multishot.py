import openai
import os
from filecomparator import compare_files
from datagenerator import generate_files
import time
import matplotlib.pyplot as plt

NB_NODES_TO_TEST = 10
NB_TEST_PER_NODE = 25
PRICE_PER_TOKEN = 0.002/1000

percentage_of_wrong_lines = [0]*NB_NODES_TO_TEST

API_KEY = open(str(os.path.dirname(os.path.abspath(__file__))) + "/openai_key.txt", "r").read()

PROMPT_PATHS = [str(os.path.dirname(os.path.abspath(__file__))) + "/prompt1.txt",
                str(os.path.dirname(os.path.abspath(__file__))) + "/prompt2.txt",
                str(os.path.dirname(os.path.abspath(__file__))) + "/prompt3.txt"]  
PROMPT_FILES = [open(path, "r").read() for path in PROMPT_PATHS]

openai.api_key = API_KEY
credits = 0
PATH_TO_DATA = str(os.path.dirname(os.path.abspath(__file__))) + "/../data"
has_succedded = [0]*NB_NODES_TO_TEST

for i in range (2, NB_NODES_TO_TEST + 2):
    generate_files(i, NB_TEST_PER_NODE, 1)
    for j in range (1, NB_TEST_PER_NODE + 1):
        f = open("tmp.txt", "w")
        time.sleep(20)
        PATH_TO_DATA_FILE = PATH_TO_DATA + "/exemple" + str(j) + "/requirement1.txt"
        FILE_TO_TRANSFORM = open(PATH_TO_DATA_FILE, "r").read()
        response = None
        user_ai_prompts = [{'role': 'user', 'content': PROMPT_FILES[i % len(PROMPT_FILES)]} if i % 2 == 0 else 
                           {'role': 'assistant', 'content': PROMPT_FILES[i % len(PROMPT_FILES)]} for i in range(len(PROMPT_FILES))]
        user_ai_prompts.append({"role": "user", "content": "Q:\n" + FILE_TO_TRANSFORM})
        while(response == None):
            try:
                response = openai.ChatCompletion.create(
                    model = "gpt-3.5-turbo",
                    messages = user_ai_prompts
                )
            except openai.error.RateLimitError:
                print("Rate limit error, waiting 10 seconds...")
                time.sleep(10)
        credits += response['usage']['total_tokens']
        f.write(response.choices[-1].message.content)
        f.close()
        comparation = compare_files("tmp.txt", PATH_TO_DATA + "/exemple" + str(j) +"/fsm.dot")
        comparation_lines = comparation.splitlines()
        percentage_of_wrong_lines[i-2] += (len(comparation_lines)-1)/2/len(FILE_TO_TRANSFORM.splitlines())
        if (comparation == "SUCCESS"):
            has_succedded[i-2] += 1
        os.remove("tmp.txt")

print(has_succedded)
print("In total i used "+ str(credits) + " tokens which corresponds to "+str(float(credits)*PRICE_PER_TOKEN) + " e.")

percentage_of_success = [0]*NB_NODES_TO_TEST
for i in range (0, NB_NODES_TO_TEST):
    percentage_of_success[i] = has_succedded[i]/NB_TEST_PER_NODE

for i in range (0, NB_NODES_TO_TEST):
    percentage_of_wrong_lines[i] = percentage_of_wrong_lines[i]/NB_TEST_PER_NODE

plt.plot(range(2, NB_NODES_TO_TEST + 2), percentage_of_wrong_lines)
plt.xticks(range(2, NB_NODES_TO_TEST + 2), map(int, range(2, NB_NODES_TO_TEST + 2)))
plt.xlabel("Number of nodes")
plt.ylabel("Percentage of lines with at least one error")
plt.title("Percentage of lines with at least one error for each number of nodes ("+  str(NB_TEST_PER_NODE) +" tests per node)")
plt.savefig('plot.png')
plt.show()
