all: main
lang:
	coqc -I ../utils refocusing_lang_env_cs
sig: lang
	coqc -I ../utils refocusing_signatures_env_cs
main: sig
	coqc -I ../utils refocusing_environments_cs
clean:
	rm *~ *.vo *.glob
#	coqc -I ../utils call_by_name_environments
#	coqc -I ../utils call_by_value_environments
