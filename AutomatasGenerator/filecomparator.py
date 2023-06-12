# This file contains the function compare_files that compares two files and returns a string with the result of the
# comparison. The function receives two paths to the files to be compared and returns a string with the result of the
# comparison. The result can be "SUCCESS" if the files are equal or "ERROR" if the files are different. If the files
# are different, the string will contain the lines that are in one file but not in the other.
def compare_files(file1_path, file2_path):
    try:
        with open(file1_path, 'r') as file1, open(file2_path, 'r') as file2:
            # remove empty lines
            lines_file1 = set(line.strip() for line in file1 if line.strip())
            lines_file2 = set(line.strip() for line in file2 if line.strip())
            # remove all lines that start with #
            lines_file1 = set(line for line in lines_file1 if not line.startswith('#'))
            lines_file2 = set(line for line in lines_file2 if not line.startswith('#'))

            missing_lines_file1 = lines_file1 - lines_file2
            missing_lines_file2 = lines_file2 - lines_file1
            
            if missing_lines_file1 or missing_lines_file2:
                txt = "ERROR:\n"
                for line in missing_lines_file1:
                    txt += line + " not found in second file\n"
                for line in missing_lines_file2:
                    txt += line + " not found in first file\n"
                return txt
            else:
                return "SUCCESS"
    except FileNotFoundError:
        return "ERROR: File not found."


# Example usage
if __name__ == '__main__' :
    file1_path = input("Enter the path of the first file: ")
    file2_path = input("Enter the path of the second file: ")
    print(compare_files(file1_path, file2_path))
