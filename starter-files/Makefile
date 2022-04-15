SRC=bridge.dfy \
		prime.dfy \
		README.md \
		mini-c/def.dfy \
		mini-c/proofs.dfy \
		mini-c/security-types.dfy \
		mini-c/taint-tracking.dfy \
		mini-c/type-leak.mc \
		mini-c/type_leak_attack.py \
		mini-c/taint-leak.mc \
		mini-c/taint_leak_attack.py

all: handin.tar

handin.tar: $(SRC)
	rm -f handin.tar
	tar -cvf handin.tar $(SRC)

clean:
	rm -f handin.tar
