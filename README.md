# Interaction Trees

[Interactions Trees](https://github.com/DeepSpec/InteractionTrees) (ITrees) are coinductive structures used to represent interactions between a system and its environment in the style of a process algebra.
This repository contains a mechanisation of ITrees in Isabelle/HOL, for the purpose of verifying reactive systems and generating code for animation purposes.
You can find a number of examples under ``examples/``, and in particular the Haskell code can be executed in [GHCi](https://www.haskell.org/ghc/) for animation purposes.

# RoboChart
RoboChart theories and examples are under `RoboChart` and `RoboChart/examples`. There are also instructions and documents inside the folder. The latest development of RoboChart related theories is in the branch [robochart_nondeterminism_resolving](https://github.com/isabelle-utp/interaction-trees/tree/robochart_nondeterminism_resolving).

# Installation

The theories have been developed in [Isabelle2021-1](https://isabelle.in.tum.de/). This instruction is based on Ubuntu/Linux. It would be similar on other operation systems.

Steps:
- Install GHC for Haskell, see [here](https://www.haskell.org/platform/) for details,
- [Clone this repository](#clone-this-repository),  and 
- use [Isabelle/UTP distributions with prebuild heap images on Linux](#isabelleutp-distributions-with-prebuild-heap-images-on-linux) or [Standard](#standard) procedure to install Isabelle/HOL.

The prebuilt version comes with a patched Isabelle/HOL to have a console for animation, which is more convenient.

## Clone this repository
1. Clone and enter the folder of this probabilistic relations
```
/path/to/yourfolder $ git clone https://github.com/isabelle-utp/interaction-trees.git
/path/to/yourfolder $ cd interaction-trees
```
We use `/path/to/interaction-trees/` to denote the path to this particular directory.

## Isabelle/UTP distributions with prebuild heap images on Linux

1. Download Isabelle/UTP distributions from [here](https://isabelle-utp.york.ac.uk/download) and choose `Isabelle2021-1 on Linux (January 26th 2023)`, it is `Isabelle2021-1-CyPhyAssure-20230126.tar.bz2` in this case
2. Uncompress it inside a folder, such as "/path/to/yourfolder":
```
/path/to/yourfolder $ tar -xvjf Isabelle2021-1-CyPhyAssure-20230126.tar.bz2
/path/to/yourfolder $ cd Isabelle2021-1-CyPhyAssure/
```
3. Launch Isabelle/UTP with session `ITree_VCG`
```
/path/to/yourfolder/Isabelle2021-1-CyPhyAssure/ $ ./bin/isabelle jedit -l ITree_VCG
```

## Standard
1. Download **Isabelle2021-1_linux.tar.gz** from [here](https://isabelle.in.tum.de/website-Isabelle2021-1/index.html).
2. Uncompress it inside a folder, such as "/path/to/yourfolder":
```
/path/to/yourfolder $ tar zxvf Isabelle2021-1_linux.tar.gz
``` 
3. Clone CyPhyAssure meta-repository (which is updated periodically to sync and try to keep in a stable state) from [here](https://github.com/isabelle-utp/CyPhyAssure) and checkout all submodules
```
/path/to/yourfolder $ git clone https://github.com/isabelle-utp/CyPhyAssure.git
/path/to/yourfolder $ cd CyPhyAssure
/path/to/yourfolder/CyPhyAssure (main) $ git submodule update --init --recursive
```
4. Launch Isabelle/UTP with session `ITree_VCG`
```
/path/to/yourfolder $ ./Isabelle2021-1/bin/isabelle jedit -d CyPhyAssure -l ITree_VCG
```

# Animation
With the prebuild version, animation would be simpler. 

## Prebuild-image
Load the theory for animation, then move your cursor to a line starting with `animate`, such as `animate D_PatrolMod_p_sim` to animate a definition `D_PatrolMod_p_sim`. When the cursor stops there, code generator starts to generate Haskell code, and compile. Usually, we will see below on the `Output` window.
```
See theory exports 
Compiling animation... 
See theory exports 
Start animation
```

Then click `Start animation`.

## Standard
General steps are shown below. Please see instructions in each specific example for further considerations.

1. Open the main theory file for a model
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