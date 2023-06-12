import openai
import os
from filecomparator import compare_files
from datagenerator import generate_files
import time
import matplotlib.pyplot as plt
NB_NODES_TO_TEST = 5
NB_TEST_PER_NODE = 20
PRICE_PER_TOKEN = 0.002/1000
# won't work if you don't have a file named openai_key.txt in the same directory as this file
# it should contain your openai key
API_KEY = open(str(os.path.dirname(os.path.abspath(__file__))) + "/openai_key.txt", "r").read() # unsafe but convenient, I used a new free account for this demo.
FIRST_PROMPT = open(str(os.path.dirname(os.path.abspath(__file__))) + "/first_prompt_QandA.txt", "r").read()
openai.api_key = API_KEY
credits = 0
PATH_TO_DATA = str(os.path.dirname(os.path.abspath(__file__))) + "/../data"
# for the graph we will need to know how many times the test has succedded
has_succedded = [0]*NB_NODES_TO_TEST


for i in range (2, NB_NODES_TO_TEST + 2):
    generate_files(i, NB_TEST_PER_NODE, 1)
    for j in range (1, NB_TEST_PER_NODE + 1):
        f = open("tmp.txt", "w")
        # wait 20 seconds to avoid rate limit error
        # this error occurs when you use too much tokens in a short period of time
        # there is a small limit for free accounts
        time.sleep(20)
        PATH_TO_DATA_FILE = PATH_TO_DATA + "/exemple" + str(j) + "/requirement1.txt"
        FILE_TO_TRANSFORM = open(PATH_TO_DATA_FILE, "r").read()
        response = None
        # we will try to send the request until it works (the rate limit error is handled)
        while(response == None):
            try:
                response = openai.ChatCompletion.create(
                    model = "gpt-3.5-turbo",
                    messages = [
                        {"role": "user", "content": FIRST_PROMPT},
                        {"role": "assistant", "content": "Waiting for any prompt."},
                        {"role": "user", "content": "Q:\n" + FILE_TO_TRANSFORM}
                    ]
                )
            except openai.error.RateLimitError:
                print("Rate limit error, waiting 10 seconds...")
                time.sleep(10)
        '''        
        print(response)
        print("GPT : " + response.choices[-1].message.content)
        print("I used " + str(response['usage']['total_tokens']) + " tokens which corresponds to "+str(float(response['usage']['total_tokens'])*PRICE_PER_TOKEN) + " e.")
        '''
        credits += response['usage']['total_tokens']
        # write the result in a file tmp.txt
        f.write(response.choices[-1].message.content)
        f.close()
        # compare the result with the original file
        print("Comparing the files...")
        # if the files are the same, the test has succedded
        comparation = compare_files("tmp.txt", PATH_TO_DATA + "/exemple" + str(j) +"/fsm.dot")
        if (comparation == "SUCCESS"):
            print(i)
            has_succedded[i-2] += 1
        os.remove("tmp.txt")
# delete the tmp file
print(has_succedded)
print("In total i used "+ str(credits) + " tokens which corresponds to "+str(float(credits)*PRICE_PER_TOKEN) + " e.")
# now we will use matplotlib to see the % of success for each node
percentage_of_success = [0]*NB_NODES_TO_TEST
for i in range (0, NB_NODES_TO_TEST):
    percentage_of_success[i] = has_succedded[i]/NB_TEST_PER_NODE

plt.plot(range(2, NB_NODES_TO_TEST + 2), percentage_of_success)
plt.xlabel("Number of nodes")
plt.ylabel("Percentage of success")
plt.title("Percentage of success for each number of nodes ("+  str(NB_TEST_PER_NODE) +" tests per node)")
plt.savefig('plot.png')
plt.show()
