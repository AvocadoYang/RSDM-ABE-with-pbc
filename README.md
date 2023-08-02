# pbc docker template

## Pre Requirement Installation

- gmp library
- m4
- libtool
- automake
- autoconf

> expect aclocal, autoheader are dependencies of automake

### macOS (osX)
```bash
# install basic cmake automatic tools
brew install libtool
brew install automake autoconf autoconf-archive

# install gmp library
brew install gmp
```

### Linux (ubuntu)
```bash
# install basic cmake automatic tools
sudo apt-get install make libtool
sudo apt-get install automake autoconf autoconf-archive

# install gmp library and dependencies
sudo apt-get install libgmp3-dev flex bison -y
```

```bash
# create symbolic link for gmp header file & binary files
sudo mkdir -p /usr/local/include
sudo mkdir -p /usr/local/lib
gmp_header=$(find /usr /opt -name "gmp.h" -type f 2>/dev/null | head -n 1)
sudo ln -s $gmp_header /usr/local/include/gmp.h
gmp_bin=$(find /usr /opt -name "libgmp.a" -type f 2>/dev/null)
sudo ln -s $gmp_bin /usr/local/lib/libgmp.a

# install pbc library
# run autoconfig, automake to generate configure and makefile
./setup
./configure
make
sudo make install

# check dependencies working good
ls /usr/local/include | grep -e gmp.h -e pbc # suppose to see gmp.h & pbc both
ls /usr/local/lib | grep -e '^lib.*\.a$' # suppose to see libgmp.a and libpbc.a
```


## Compile And Run

```
# for linux
gcc file -lgmp -lpbc
# for mac
clang file -lgmp -lpbc
```

[pbc library](https://crypto.stanford.edu/pbc/manual/)