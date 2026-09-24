session Grammar_Command = Context_Free_Grammar +
  options  [document = pdf, document_output = "output", document_bibliography]
  theories [document = false]
    Token
    Indentation_Sensitive
  theories
    Grammar_Command
  document_files
    "root.bib"
    "root.tex"

session LR_Parser in "lr" = Grammar_Command +
  theories
    LR
    LR_Driver
    LR_Det
    LR_Simple
    LR_Parser

session Grammar_Tests in "tests" = LR_Parser + theories Regression_Tests