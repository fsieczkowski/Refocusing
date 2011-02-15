all: main case_studies
lang:
	coqc -I ../utils refocusing_lang
sig: lang
	coqc -I ../utils refocusing_trace_signatures
main: sig
	coqc -I ../utils refocusing_trace_substitutions
case_studies: main
	coqc -I ../utils simple_arith_trace
clean:
	rm *~ *.vo *.glob; echo "Directory cleaned"
