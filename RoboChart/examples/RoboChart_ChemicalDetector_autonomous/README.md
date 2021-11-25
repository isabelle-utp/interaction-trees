# Animate RoboChart
General steps are shown below. Please see instructions in each specific example for further considerations.

1. Open `RoboChart_ChemicalDetector_autonomous.thy`.
2. Go to a line starting with command **export_code**, which exports generated Haskell code.
3. Click the `Output` window and you will see **See theory exports**, then double click the area **theory exports**, and now the exported code will be displayed on `File Browser`. Use `File Browser` to copy the generated files to the local physical file system, such as `/path/to/simulation`.
4. Go to a line starting with command **export_generated_files**, which exports a raw Haskell file `Simulate.hs`.
5. Click the `Output` window and you will see **See theory exports**, then double click the area **theory exports**, and now the exported file will be displayed on `File Browser`. Use `File Browser` to copy the generated file to the local physical file system `/path/to/simulation`.
6. Modify "RoboChart_ChemicalDetector_autonomous.hs" based on the instructions given in `Simulate.hs`
7. Open a terminal and cd to `/path/to/simulation`.
```
$ cd /path/to/simulation
```
8. Use GHCi for animation and load the `main.hs`, then run `main`.
```
$ ghci RoboChart_ChemicalDetector_autonomous.hs
*RoboChart_ChemicalDetector_autonomous> main
```
9. Or use GHC to compile generated code, then run executable.
```
$ ghc -g main.hs
$ ./main
```
