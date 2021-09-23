session "Interaction_Trees_temp" = "Shallow-Expressions-Z" +
  options [timeout = 600, document = pdf, document_output = "output"]
  theories
    ITrees
  document_files
    "root.tex"

session "ITree_UTP_temp" in "UTP" = "Interaction_Trees_temp" +
  options [timeout = 600, document = false]
  theories
    ITree_UTP

session "ITree_RoboChart" in "RoboChart" = "ITree_UTP_temp" +
  options [timeout = 600, document = pdf, document_output = "output"]
  theories
    ITree_RoboChart
  document_files
    "root.tex"

session "RoboChart_basic" in "examples/RoboChart/RoboChart_basic" = "ITree_RoboChart" +
  options [timeout = 600, document = pdf, document_output = "output"]
  sessions
    "ITree_RoboChart"
  theories
    RoboChart_basic 
  document_files
    "root.tex"
    "images/system.pdf"

session "RoboChart_ChemicalDetector_autonomous" in "examples/RoboChart/RoboChart_ChemicalDetector_autonomous" = "ITree_RoboChart" +
  options [timeout = 600, document = pdf, document_output = "output"]
  sessions
    "ITree_RoboChart"
  theories
    RoboChart_ChemicalDetector_autonomous 
  document_files
    "root.tex"
