import os

# This function will explore a folder and return a set of all the characters
def explore_folder(folder_path,suffix):
    vocabulary = set()
    for filename in os.listdir(folder_path):
        if filename.endswith(suffix):
            file_path = os.path.join(folder_path, filename)
            with open(file_path, 'r') as file:
                content = file.read()
                vocabulary.update(content)
    return vocabulary

if __name__ == "__main__":
    result = explore_folder("./data/",".dot")
    print(result)
