all: main
lang:
	coqc -I ../utils refocusing_lang_env_state
sig: lang
	coqc -I ../utils refocusing_signatures_env_state
main: sig
	coqc -I ../utils refocusing_environments_state
clean:
	rm *.vo *.glob *~
#	coqc -I ../utils call_by_name_environments
#	coqc -I ../utils call_by_value_environments
