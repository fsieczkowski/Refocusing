cur: env_cs env_cs_state
all: sub sub_cs sub_tr env env_cs env_cs_state
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
env_cs: util
	cd environments_cs && make
env_cs_state: util
	cd environments_cs_state && make
clean:
	cd utils && rm *~ *.glob *.vo
	cd environments_cs_state && make clean
	cd environments_cs && make clean
