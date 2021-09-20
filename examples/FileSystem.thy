theory FileSystem
  imports "../ITree_Extraction"
begin 


lit_vars

type_synonym Key = integer
type_synonym Data = integer

definition "Key = set [0,1,2,3]"
definition "Data = set [0,1,2,3]"

schema File =
  contents :: "Key \<Zpfun> Data"

record_default File

definition "FileInit = [contents \<leadsto> 0]"

chantype fchan =
  addFile :: "Key \<times> Data"
  readFile :: "Key"
  deleteFile :: "Key"
  fileContent :: "Data"
  writeFile :: "Key \<times> Data"

(*
definition Read\<^sub>0 :: "('e, integer, integer, File) procedure" where
"Read\<^sub>0 = (proc (k :: integer). \<questiondown>k \<in> pdom contents? \<Zcomp> return (contents k))"

term "operation readFile fileContent Read\<^sub>0"
*)

definition Read\<^sub>0 :: "(fchan, File) htree" where
"Read\<^sub>0 = readFile?(k):(pdom contents) \<rightarrow> fileContent!(contents k) \<rightarrow> Skip"

definition Write\<^sub>0 :: "(fchan, File) htree" where
"Write\<^sub>0 = writeFile?(k, d):(pdom contents \<times> Data) \<rightarrow> contents := contents \<oplus> {k \<mapsto> d}\<^sub>p"

definition Add\<^sub>0 :: "(fchan, File) htree" where
"Add\<^sub>0 = addFile?(k, d):((Key - pdom contents) \<times> Data) \<rightarrow> contents := contents \<oplus> {k \<mapsto> d}\<^sub>p"

definition Delete\<^sub>0 :: "(fchan, File) htree" where
"Delete\<^sub>0 = deleteFile?(k):(pdom contents) \<rightarrow> contents := {k} \<Zndres> contents"

definition "SingleFile = process FileInit (loop (Read\<^sub>0 \<box> Write\<^sub>0 \<box> Add\<^sub>0 \<box> Delete\<^sub>0))"

export_code SingleFile in Haskell module_name SingleFile (string_classes)

type_synonym Name = integer

chantype schan = 
  fileOp :: "Name \<times> fchan"

schema System = 
  "file" :: "Name \<Zpfun> File"
  "open" :: "Name set"
  where "open \<subseteq> pdom file"


term Read\<^sub>0

(*
term "promote_proc Read\<^sub>0 (\<lambda> i. collection_lens i ;\<^sub>L file)"
*)

definition "SystemInit = [file \<leadsto> {}\<^sub>p]"

text \<open> We need to promote both the state and events to lift the file operations to the system.
  The latter is effectively a renaming operation, I think. \<close>

end