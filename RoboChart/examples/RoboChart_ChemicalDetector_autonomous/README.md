# Animate the chemical detector RoboChart model

1. Open `RoboChart_ChemicalDetector_autonomous.thy`.
2. Go to a line starting with command **export_code**, which exports generated Haskell code.
3. Click the `Output` window and you will see **See theory exports**, then double click the area **theory exports**, and now the exported code will be displayed on `File Browser`. Use `File Browser` to copy the generated files to the local physical file system, such as `/path/to/simulation`.
4. Go to a line starting with command **export_generated_files**, which exports two raw Haskell files `Simulate.hs` and `Main.hs`.
5. Click the `Output` window and you will see **See theory exports**, then double click the area **theory exports**, and now the exported files will be displayed on `File Browser`. Use `File Browser` to copy the generated files to the local physical file system `/path/to/simulation`.
6. Modify "RoboChart_ChemicalDetector_autonomous.hs" to include simulation in this module
- Add `, simulate` on line 5 after `d_ChemicalDetector` (export the function)
- Insert two imports below into the line after import of Prelude (line 13)
```
import qualified Data.List.Split;
import qualified Data.List;
```
- Copy the content of file `Simulate.hs` into the line before the last line (})
7. Open a terminal and cd to `/path/to/simulation`.
```
$ cd /path/to/simulation
```
8. Use GHCi for animation and load the `Main.hs`, then run `main`.
```
$ ghci Main.hs
*Main> main
```
9. Or use GHC to compile generated code, then run executable.
```
$ ghc -g main.hs
$ ./main
```
