# Naproche

[![Build Status](https://travis-ci.com/anfelor/Naproche-SAD.svg?branch=master)](https://travis-ci.com/anfelor/Naproche-SAD)

Proof Checking of Natural Mathematical Documents, with optional support
for [Isabelle][isabelle] Prover IDE (Isabelle/PIDE – Isabelle/jEdit).


**NOTE:** The subsequent explanations are for **development** of the tool, not
for end-users!


## Isabelle/Naproche Prover IDE

### Prerequisites

Ensure that `curl`, `git`, and `hg` (Mercurial) are installed:

  * Linux: e.g. `sudo apt install curl git mercurial`

  * macOS: e.g. `brew install mercurial` or download from
    <https://www.mercurial-scm.org>

  * Windows: use Cygwin64 with packages `curl`, `git`, and
    `mercurial` (via [`Cygwin setup-x86_64.exe`][cygwin64])


### Repository management

Commands below assume the same current directory: repository clones
`isabelle_naproche` and `naproche` are put side-by-side.

* initial clone:

  ```sh
  hg clone https://isabelle.in.tum.de/repos/isabelle isabelle_naproche
  git clone https://github.com/naproche/naproche.git naproche

  isabelle_naproche/Admin/init -I Isabelle_Naproche -V ./naproche/Isabelle
  isabelle_naproche/bin/isabelle components -u ./naproche
  ```

* later updates:

  ```sh
  git --git-dir="./naproche/.git" pull
  isabelle_naproche/Admin/init -V ./naproche/Isabelle
  ```


### Development

* Isabelle executable: there is no need to have `isabelle_naproche/bin/isabelle`
  in the PATH, but it is convenient to put it into a standard place once, e.g.:

  ```sh
  isabelle_naproche/bin/isabelle install "$HOME/bin"
  ```

* Build and test:

  - Shutdown Isabelle/jEdit before building Isabelle/Naproche as follows:

    ```sh
    isabelle naproche_build
    ```

  - Run some tests as follows (make sure that your current directory is the root
    of the Naproche repository):

    ```sh
    isabelle naproche_build && isabelle naproche_test -j2

    isabelle naproche_test -o naproche_server_debugging
    ```

  - Package the Isabelle/Naproche component as follows:

    ```sh
    isabelle naproche_build && isabelle naproche_component -P
    ```

    The result is for the current repository version, and the underlying
    HW + OS platform. The following reference platforms (x86_64) are
    used for Isabelle2022:

      - Ubuntu Linux 16.04 LTS
      - macOS 10.14 Mojave
      - Windows 10

* Isabelle Prover IDE

    - Open ForTheL examples in Isabelle/jEdit, e.g.

      ```sh
      isabelle jedit examples/cantor.ftl
      ```

    - Open Isabelle development environment with ForTheL examples, e.g.

      ```sh
      isabelle jedit -l Pure Isabelle/Test.thy
      ```


## Low-level command-line tool (without Isabelle)

### Prerequisites

  * Supported OS platforms: Linux, macOS, Windows (e.g. with [Cygwin][cygwin]
    terminal)

  * The [Haskell Tool Stack][stack]

  * Install the [E Theorem Prover][eprover] (supported versions: 2.0 to 2.5) and
    set the environment variable `NAPROCHE_EPROVER` to its executable path.

    Note: the E prover executable bundled with Isabelle can be located like
    this:

    ```sh
    isabelle getenv -b NAPROCHE_EPROVER
    ```

  * A [Haskell][haskell] IDE (optional):

    - [Haskell][haskell-ide-vscode] (within [VSCode][vscode])

    - [IDE-Haskell][haskell-ide-pulsar] (within [Pulsar][pulsar])

    - [Intellij-Haskell][haskell-ide-intellij] (within [IntelliJ][intellij])


### Build and test

```sh
cd .../naproche  #repository

stack clean

stack build

stack test
```


### Manual checking of proof files

```sh
stack exec Naproche-SAD -- OPTIONS FILE
```

It may be necessary to allow the E Prover more time by appending
`-t SECONDS`


## Documentation

You can use the tool [Haddock][haddock] to automatically generate documentation
of Naproche's source code.
Just run the following command:

```sh
stack haddock
```

To access this documentation via a local [Hoogle][hoogle] server, proceed the
following steps:

  1.  Generate a local Hoogle database.

      ```sh
      stack hoogle -- generate --local
      ```

  2.  Start a local Hoogle server.

      ```sh
      stack hoogle -- server --local --port=8080
      ```

Now you can access the documentation with your favourite web browser at
<http://localhost:8080>.

If you are developing Naproche and want to add Haddock annotations to the source files, have a look at this guide:
<https://haskell-haddock.readthedocs.io/en/latest/markup.html>


## Reference

This program is based on the [System for Automated Deduction (SAD)][sad] by
Andrei Paskevich.

You can find more resources in our [CONTRIBUTING.md](CONTRIBUTING.md).


[cygwin]: <https://cygwin.com/>
[cygwin64]: <https://cygwin.com/setup-x86_64.exe>
[eprover]: <https://wwwlehre.dhbw-stuttgart.de/~sschulz/E/E.html>
[haddock]: <https://haskell-haddock.readthedocs.io/en/latest/>
[haskell]: <https://www.haskell.org/>
[haskell-ide-intellij]: <https://plugins.jetbrains.com/plugin/8258-intellij-haskell>
[haskell-ide-pulsar]: <https://web.pulsar-edit.dev/packages/ide-haskell>
[haskell-ide-vscode]: <https://marketplace.visualstudio.com/items?itemName=haskell.haskell>
[hoogle]: <https://wiki.haskell.org/Hoogle>
[intellij]: <https://www.jetbrains.com/idea/>
[isabelle]: <https://isabelle.in.tum.de/>
[pulsar]: <https://pulsar-edit.dev/>
[sad]: <https://github.com/tertium/SAD>
[stack]: <https://www.haskellstack.org>
[vscode]: <https://code.visualstudio.com/>
