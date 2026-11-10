session TIGER_Token in "token" = HOL +
  description "Spans, positions, and the token record standalone"
  options [timeout = 60, document = false]
  theories Token

session TIGER_Grammar in "grammar/model" = Context_Free_Grammar +
  sessions TIGER_Token
  theories [document = false]
    Indentation_Sensitive
    Grammar_Base

session TIGER_LR in "grammar" = TIGER_Grammar +
  options  [document_output = "../output", document_bibliography]
  directories "lr"
  theories [document = false]
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
  theories
    Grammar_Command
    LR_Parser
    LR_Prec_Parse
  document_files (in "../document")
    "root.bib"
    "root.tex"

session TIGER_Tests in "grammar/tests" = TIGER_LR +
  theories Parser_Check Regression_Tests Diag_Tests Reach_Tests Prec_Tests Prec_Surface_Tests Compose_Tests Param_Tests Span_Tests Ast_Tests
    Same_Terms

session TIGER_Tests_Slow in "grammar/tests/slow" = TIGER_Tests +
  theories Recover_Tests Repair_Tests Repair_Code_Tests
