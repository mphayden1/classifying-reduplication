import os
import ast

import classifier

input_folder = "FST"
output = "results.txt"

with open(output, "w") as out:
	for filename in sorted(os.listdir(input_folder)):
		filepath = os.path.join(input_folder, filename)
		with open(filepath) as f:
			line = f.readline().strip()
		transitions = ast.literal_eval(line.split("=", 1)[1].strip())
		print(f"Processing {filename}...\n")
		classifier.transitions = transitions
		result = classifier.main()
		out.write(f"{filename} results:\n")
		out.write(f"{result}\n\n")
