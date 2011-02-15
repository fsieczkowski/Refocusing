all: main case_studies
lang:
	coqc -I ../utils refocusing_lang_env
sig: lang
	coqc -I ../utils refocusing_signatures_env
main: sig
	coqc -I ../utils refocusing_environments
case_studies: main
	coqc -I ../utils call_by_name_environments
	coqc -I ../utils call_by_value_environments
clean:
	rm *~ *.vo *.glob; echo "Directory cleaned"
