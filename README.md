This is my code for the paper submitted to PAAMS 

The project was a part of the course Dynamic Epistemic Learning at ILLC

Robert White (Shuai Wang): ai.robert.wangshuai@gmail.com

In case of confusion:

The number of preconditon is named demand;
The number of postcondition is named active;

To use:

1) You need BuDDy.

2) Compile Smodels using 
	
	make

	make install

2) Go to the ./mas directory and type:

	make main
	
3) For precondition free action learning, type:

	./main 1 100 (for a domain of 100 propositions)
or

	./main 1 1000 (for a domain of 1000 propositions)

4) For conditional action learning, type:

	./main 2 100 (for a domain of 100 propositions)
or  

	./main 2 1000 (for a domain of 1000 propositions)

and for demand-oriented testings, type:

	./main 3 (the domain is hard-coded to 100)