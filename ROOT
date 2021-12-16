session "Interaction_Trees" = "Shallow-Expressions-Z" +
  options [timeout = 600, document = pdf, document_output = "output"]
  theories
    ITrees
  document_files
    "root.tex"

session "ITree_Simulation" in "simulation" = "Interaction_Trees" +
  options [timeout = 600, document = false]
  theories
    ITree_Simulation

session "ITree_UTP" in "UTP" = "Interaction_Trees" +
  options [timeout = 600, document = false]
  theories
    ITree_UTP
    ITree_VCG
  