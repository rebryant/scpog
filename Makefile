
# Installation possibilities

# Default: Linux
install:
	cd cake_scpog ; make cake_scpog
	cd cpog ; make all
	cd d4v2-modified ; make all -f Makefile-compile MACHINE=linux


# x86 Mac
install-mac:
	cd cake_scpog ; make cake_scpog
	cd cpog ; make all
	cd d4v2-modified ; make all -f Makefile-compile MACHINE=mac


# ARM Mac
install-arm:
	cd cake_scpog ; make cake_scpog_arm8
	cd cpog ; make all
	cd d4v2-modified ; make all -f Makefile-compile MACHINE=arm

clean:
	cd test ; make clean
	cd benchmark ; make clean

superclean: clean
	cd cake_scpog ; make clean
	cd cpog ; make clean
	cd d4v2-modified ; make clean -f Makefile-compile

test:
	cd test ; make test

benchmark:
	cd benchmark ; make run
