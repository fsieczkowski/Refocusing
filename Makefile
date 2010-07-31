all: sub sub_cs sub_tr env
util:
	cd utils && make
sub: util
	cd substitutions && make
sub_cs: util
	cd substitutions_cs && make
sub_tr: util
	cd substitutions_trace && make
env: util
	cd environments && make
clean:
	cd utils && make clean
	cd substitutions && make clean
	cd substitutions_cs && make clean
	cd substitutions_trace && make clean
	cd environments && make clean