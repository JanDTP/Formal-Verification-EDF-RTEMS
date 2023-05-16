# Formal Verification of EDF Scheduler in RTEMS
This repository contains the files to reproduce the results of the master thesis:
_Formal Verification of EDF Scheduler in RTEMS_

## Functionlist

## Enviroment Setup
The contracts are tested with Frama-C 25 and Alt-Ergo 2.4.2
RTEMS 5.1 is needed for verification.

### Frama-C
Follow the instructions to install Frama-C https://frama-c.com/html/get-frama-c.html:
1. Install opam (OCaml package manager): Use the package manager based on your distribution

2. Initialize opam (install an OCaml compiler)
```
opam init --compiler 4.14.1 # may take a while
eval $(opam env)
```

3. Install Frama-C (and its dependencies):
```
opam install frama-c
```

4. Configuring provers for Frama-C/WP
```
why3 config detect
```

### RTEMS 5.1
Follow the instructions here to setup RTEMS 5.1: https://ftp.rtems.org/pub/rtems/releases/5/5.1/docs/html/user.html#document-start/index
Installation files: https://ftp.rtems.org/pub/rtems/releases/5/5.1/

#### 2.4 Install the Tool Suite:
For our case, we need the x86_64 tool suite. The name of the architecture for it is rtems-x84_64.
Example (replace it with your local paths):
```
../source-builder/sb-set-builder --prefix=$HOME/Thesis/RTEMS/rtems_x86_64 5/rtems-x86_64
```
#### 2.6.2 Manual BSP Build:
Use step 2.6.2 instead and do a manual BSP build. Create the corresponding folders like in the tutorial.
Our target BSP is AMD64, change the directory to the one you created and configute the builder (remember to export your PATH):
```
$HOME/Thesis/RTEMS/src/rtems-5.1/configure \
    --prefix=$HOME/Thesis/RTEMS/rtems_x86_64 \
    --enable-maintainer-mode \
    --target=x86_64-rtems5 \
    --enable-rtemsbsp=amd64
```
```
make
make install
```


