import random
import os
import time
from subprocess import Popen, PIPE, STDOUT
from type_leak_attack import attack

for i in range(10):
    random_number = random.randrange(-5, 5, 1)
    print("Program input: ", random_number)

    start = time.time()
    project = os.path.join("MiniC", "MiniC.csproj")

    p = Popen(["dotnet", "run", "--project", project, "sectype", "type-leak.mc"], stdout=PIPE, stdin=PIPE, stderr=PIPE)
    stdout_data = p.communicate(input=str(random_number).encode())[0]
    elapsed = (time.time() - start)
    print("Program output: ", stdout_data.decode())

    your_output = attack(stdout_data, elapsed)
    print("Your output:", your_output)

    if (random_number > 0 and your_output != "Greater than zer0") or \
        (random_number == 0 and your_output != "Equal to zer0") or \
            (random_number < 0 and your_output != "Less than zer0"):
            print("Try again!")
            exit()
    
print("Congratulations! Attack successful")
