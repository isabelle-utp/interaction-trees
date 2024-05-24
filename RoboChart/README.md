This folder contains theories and examples for animation of RoboChart.

# Animate RoboChart
## Prebuild-image
Load the theory `examples/RoboChart_basic_v1/RoboChart_basic_v1_1.thy` for animation, then move your cursor to a line `animate1 D_PatrolMod_p_sim` to animate. When the cursor stops there, code generator starts to generate Haskell code, and compile. Usually, we will see below on the `Output` window.
```
See theory exports 
Compiling animation... 
See theory exports 
Start animation
```
Then click `Start animation`.

## Standard
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
