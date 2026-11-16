chapter AFP

session TIGER_Token in "token" = HOL +
  description "Spans and the token record: the interface between lexer and parser."
  options [document = false, timeout = 300]
  theories TIGER_Token
  document_files (in "../document")
    "root.bib"

session TIGER_Grammar_Model in "grammar/model" = Context_Free_Grammar +
  description "The indentation-sensitive grammar model (Adams) and its parse trees."
  options [document = false, timeout = 300]
  sessions TIGER_Token
  theories
    Indentation_Sensitive
    Grammar_Base
  document_files (in "../../document")
    "root.bib"

session TIGER_Grammar in "grammar" = TIGER_Grammar_Model +
  description "The LR construction and drivers, and the grammar and parser commands."
  options [document = false, timeout = 600]
  directories "lr"
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
    LR_Arr
    LR_Diag
    LR_Recover
    LR_Restrict
    LR_Prec
    LR_Lab
    LR_Fuse
    LR_Kern
    Grammar_Command
    LR_Parser
    LR_Prec_Parse
  document_files (in "../document")
    "root.bib"

session TIGER_Grammar_Tests in "grammar/tests" = TIGER_Grammar +
  options [document = false, timeout = 1200]
  theories Parser_Check Regression_Tests Diag_Tests Reach_Tests Prec_Tests Prec_Surface_Tests Compose_Tests Param_Tests Span_Tests Ast_Tests Provider_Tests
    Same_Terms
  document_files (in "../../document")
    "root.bib"

session TIGER_Grammar_Tests_Slow in "grammar/tests/slow" = TIGER_Grammar_Tests +
  options [document = false, timeout = 600]
  theories Recover_Tests Repair_Tests Repair_Code_Tests
  document_files (in "../../../document")
    "root.bib"

session TIGER_Lexer in "lexer" = TIGER_Token +
  description
    "Symbolic regexes and their derivatives, the inductive lexer specification, the DFA
     table generator and the runner, and the pattern and lexer commands."
  options [document = false, timeout = 300]
  sessions "Regular-Sets" "HOL-Library"
  directories "core"
  theories
    TIGER_Lexed TIGER_Regex TIGER_Pred_Algebra TIGER_Intervals TIGER_Spec TIGER_Gen TIGER_Lexer
    TIGER_Driver TIGER_Tables TIGER_Codepoints
    TIGER_Pattern TIGER_Rules Lexer_Command Lexer_Check
  document_files (in "../document")
    "root.bib"

session TIGER_Lexer_Tests in "lexer/tests" = TIGER_Lexer +
  options [document = false, timeout = 300]
  theories Intervals_Tests Tables_Tests Driver_Tests Codepoint_Tests Pattern_Tests
    Lexer_Command_Tests Lexer_Table_Tests Stress_Lexer_Tests
  document_files (in "../../document")
    "root.bib"

session TIGER_Bridge in "bridge" = TIGER_Grammar +
  description "Lexers as terminal providers of the grammar command."
  options [document = false, timeout = 300]
  sessions TIGER_Lexer
  theories TIGER_Bridge
  document_files (in "../document")
    "root.bib"

session TIGER_Bridge_Tests in "bridge/tests" = TIGER_Bridge +
  options [document = false, timeout = 300]
  sessions TIGER_Grammar_Tests
  theories Bridge_Tests
  document_files (in "../../document")
    "root.bib"

session TIGER_Lexer_Parser = TIGER_Bridge +
  description "Lexers and indentation-sensitive LR parsers together."
  options [timeout = 300, document_bibliography]
  theories TIGER
  document_files (in "document")
    "root.bib"
    "root.tex"
