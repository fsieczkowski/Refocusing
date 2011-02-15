all: main case_studies
lang:
	coqc -I ../utils refocusing_lang_cs
sig: lang
	coqc -I ../utils refocusing_signatures_cs
main: sig
	coqc -I ../utils refocusing_substitutions_cs
case_studies: main
	coqc -I ../utils call_by_value_callcc_sub
	coqc -I ../utils call_by_name_callcc_sub
clean:
	rm *~ *.vo *.glob; echo "Directory cleaned"