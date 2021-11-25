This folder contains theories and examples for animation of RoboChart.

# Installation
1. Download and install [Isabelle2021](https://isabelle.in.tum.de/index.html).
2. Install GHC for Haskell, see [here](https://www.haskell.org/platform/) for details.
2. Clone the following repositories inside a folder (for example, `/path/to/repos`).
- [Mirror AFP 2021](https://github.com/isabelle-utp/mirror-afp-2021)
- [Z Toolkit](https://github.com/isabelle-utp/Z_Toolkit)
- [Shallow Expressions](https://github.com/isabelle-utp/Shallow-Expressions)
- [Interaction Trees (robochart branch)](https://github.com/isabelle-utp/interaction-trees/tree/robochart)

3. Create a `ROOTS` file in `/path/to/repos` with content below.
```
mirror-afp-2021/thys
Z_Toolkit/
Shallow-Expressions/
Shallow-Expressions/Z/
interaction-trees/
```

4. Load Isabelle/jedit
```
$ /path/to/Isabelle2021/bin/isabelle jedit -d /path/to/repos
```

# Animate RoboChart
General steps are shown below. Please see instructions in each specific example for further considerations.

1. Open the main theory file for a RoboChart model, such as `RoboChart_basic.thy` for the model in `examples/RoboChart_basic.thy/`
2. Go to a line starting with command **export_code**, which exports generated Haskell code.
3. Click the `Output` window and you will see **See theory exports**, then double click the area **theory exports**, and now the exported code will be displayed on `File Browser`. Use `File Browser` to copy the generated files to the local physical file system, such as `/path/to/simulation`.
4. Go to a line starting with command **export_generated_files**, which exports two raw Haskell files `simulation.hs` and `main.hs`.
5. Click the `Output` window and you will see **See theory exports**, then double click the area **theory exports**, and now the two exported files will be displayed on `File Browser`. Use `File Browser` to copy the generated files to the local physical file system `/path/to/simulation`.
6. Open a terminal and cd to `/path/to/simulation`.
```
$ cd /path/to/simulation
```
7. Use GHCi for animation and load the `main.hs`, then run `main`.
```
$ ghci main.hs
*Main> main
```
8. Or use GHC to compile generated code, then run executable.
```
$ ghc -g main.hs
$ ./main
```
