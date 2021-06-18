subsection \<open> ITree Code Generation Support \<close>

theory ITree_Extraction
  imports ITree_Circus Record_Default_Instance Enum_Type
begin

instantiation set :: (type) default
begin
definition "default_set = ({} :: 'a set)"
instance ..
end

instantiation pfun :: (type, type) default
begin
definition "default_pfun = ({}\<^sub>p :: ('a, 'b) pfun)"
instance ..
end

end