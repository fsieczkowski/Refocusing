all: main case_studies
lang:
	coqc -I ../utils refocusing_lang_env_cs
sig: lang
	coqc -I ../utils refocusing_signatures_env_cs
main: sig
	coqc -I ../utils refocusing_environments_cs
case_studies: main
	coqc -I ../utils call_by_value_rtl_environments
clean:
	rm *~ *.vo *.glob
