section \<open>Build and test exported program with GHC\<close>

theory RoboChart_ChemicalDetector_autonomous_simulate
imports RoboChart_ChemicalDetector_autonomous
begin

(* _ means all generated files in Fib *)
compile_generated_files
  _ (in RoboChart_ChemicalDetector_autonomous_microcontroller)
  export_files 
    \<open>code/RoboChart_ChemicalDetector/Simulate.hs\<close>
    \<open>code/RoboChart_ChemicalDetector/Main.hs\<close>
  where \<open>fn dir =>
    let
      val exec = Generated_Files.execute 
        (Path.append (Path.append dir (Path.basic "code")) (Path.basic "RoboChart_ChemicalDetector"));
      val cmd = (File.bash_path \<^path>\<open>/opt/homebrew/bin/ghc\<close> ^ " -g Main.hs");
      val log = exec \<open>Compilation\<close> (cmd);
      val log1 = exec \<open>Test\<close> "./Main";
    in writeln (log ^ log1)
end\<close>

(* _ means all generated files in Fib *)
compile_generated_files
  _ (in RoboChart_ChemicalDetector_autonomous)
  export_files 
    \<open>code/RoboChart_ChemicalDetector/Simulate.hs\<close>
    \<open>code/RoboChart_ChemicalDetector/Main.hs\<close>
  where \<open>fn dir =>
    let
      val exec = Generated_Files.execute 
        (Path.append (Path.append dir (Path.basic "code")) (Path.basic "RoboChart_ChemicalDetector"));
      val cmd = (File.bash_path \<^path>\<open>/opt/homebrew/bin/ghc\<close> ^ " -g Main.hs");
      val log = exec \<open>Compilation\<close> (cmd);
      val _ = exec \<open>Test\<close> "./Main";
    in writeln log
end\<close>

end