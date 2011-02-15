all: main case_studies
lang:
	coqc -I ../utils refocusing_lang
sig: lang
	coqc -I ../utils refocusing_signatures
main: sig
	coqc -I ../utils refocusing_substitutions
case_studies: main
	coqc -I ../utils simple_arith
	coqc -I ../utils call_by_value_sub
	coqc -I ../utils call_by_name_sub
	coqc -I ../utils miniml
clean:
	rm *~ *.vo *.glob; echo "Directory cleaned"