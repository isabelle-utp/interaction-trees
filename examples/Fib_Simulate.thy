section \<open>Build and test exported program with MLton\<close>

theory Fib_Simulate
imports Fib
begin

(* _ means all generated files in Fib *)
compile_generated_files
  _ (in Fib)
  (* export_files \<open>code/Fib/Fib.hs\<close> *)
  where \<open>fn dir =>
    let
      val exec = Generated_Files.execute 
        (Path.append (Path.append dir (Path.basic "code")) (Path.basic "Fib"));
      val cmd = (File.bash_path \<^path>\<open>/usr/bin/ghci\<close> ^
            " simulate.hs Fib.hs");
      val log = exec \<open>Simulate\<close> (cmd);
    in writeln log
end\<close>

end