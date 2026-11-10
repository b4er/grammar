session Grammar_Model = Context_Free_Grammar +
  theories [document = false]
    Token
    Indentation_Sensitive
    Grammar_Base

session LR_Core in "lr" = Grammar_Model +
  theories
    LR
    LR_Driver
    LR_Fast
    LR_Sparse
    LR_Vec
    LR_Det
    LR_Simple
    LR_Int
    LR_Trie
    LR_Tok
    LR_Prod
    LR_Loop
    LR_Plain
    LR_Diag
    LR_Recover
    LR_Restrict
    LR_Prec

session LR_Parser in "command" = LR_Core +
  options  [document_output = "../output", document_bibliography]
  theories
    Grammar_Command
    LR_Parser
    LR_Prec_Parse
  document_files (in "../document")
    "root.bib"
    "root.tex"

session Grammar_Tests in "tests" = LR_Parser +
  theories Parser_Check Regression_Tests Diag_Tests Reach_Tests Prec_Tests Prec_Surface_Tests Compose_Tests Param_Tests Span_Tests Ast_Tests
    Same_Terms

session Grammar_Tests_Slow in "tests/slow" = Grammar_Tests +
  theories Recover_Tests Repair_Tests Repair_Code_Tests
