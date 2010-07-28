all: sub sub_cs sub_tr env
util:
	cd utils && coqc Util
sub: util
	cd substitutions && make
sub_cs: util
	cd substitutions_cs && make
sub_tr: util
	cd substitutions_trace && make
env: util
	cd environments && make
