;; abella-syntax.el --- Proof General instance for Abella - syntax file
;;
;; Copyright (C) 2011-2013 INRIA
;;
;; Authors: Clement Houtmann <Clement.Houtmann@inria.fr>
;;          Kaustuv Chaudhuri <kaustuv.@chaudhuri.info>
;;

(require 'font-lock)

(defconst abella-core-font-lock-keywords
  '(
    ("\\(=>\\||-\\|[][{}]\\)"            . font-lock-builtin-face)
    ;; (regexp-opt '("->" ":=" ":" ";" "." "," "/\\" "\\/" "=" "\\"))
    ("\\(?:->\\|/\\\\\\|:=\\|\\\\/\\|[,.:;=\\]\\)"
       . font-lock-builtin-face)
    ("\\<\\(kind\\|type\\|forall\\|exists\\|nabla\\|true\\|pi\\)\\>"
       . font-lock-keyword-face))
  "Abella core language font-lock keywords")

(defconst abella-reasoning-font-lock-keywords
  '(;; (regexp-opt '("Set" "Query" "Show") 'words)
    ("\\<\\(Query\\|S\\(?:et\\|how\\)\\)\\>"     . font-lock-builtin-face)
    ("\\<\\(Import\\|Specification\\)\\>"        . font-lock-builtin-face)
    ("\\<\\(Type\\|Kind\\|Close\\)\\>"           . font-lock-keyword-face)
    ("\\<\\(\\(?:Co\\)?Define\\|Schema\\|Inductive\\|by\\)\\>" . font-lock-keyword-face)
    ("\\<\\(Theorem\\|Split\\)\\>"               . font-lock-keyword-face)
    ("\\<\\(skip\\|undo\\|abort\\)\\>"           . font-lock-warning-face)
    ;; (regexp-opt '("{" "}" "|-" "[" "]" "=>"))
    ;; (regexp-opt '("abbrev" "all" "apply" "assert" "backchain" "case" "clear" "coinduction" "cut" "induction" "inst" "intros" "keep" "left" "monotone" "on" "permute" "rename" "right" "search" "split" "split*" "to" "unabbrev" "unfold" "with" "witness") 'words)
    ("\\<\\(a\\(?:bbrev\\|ll\\|pply\\|ssert\\)\\|backchain\\|c\\(?:ase\\|lear\\|oinduction\\|ut\\)\\|in\\(?:duction\\|st\\|tros\\)\\|keep\\|left\\|monotone\\|on\\|permute\\|r\\(?:ename\\|ight\\)\\|s\\(?:earch\\|plit\\*?\\)\\|to\\|un\\(?:abbrev\\|fold\\)\\|wit\\(?:h\\|ness\\)\\)\\>" . font-lock-function-name-face)
    )
  "Abella reasoning level font-lock keywords")

(defconst abella-script-font-lock-keywords
  (append abella-core-font-lock-keywords
          abella-reasoning-font-lock-keywords))

(defconst abella-goals-font-lock-keywords
  (list
    (cons "\\<\\(Subgoal\\)\\>" font-lock-keyword-face))
  "Default highlighting for Abella Goals mode")

(defconst abella-response-font-lock-keywords
  (list
    (cons "\\<\\(Proof completed\\.\\)\\>" font-lock-function-name-face))
  "Default highlighting for Abella Response mode")

(defconst abella-mode-syntax-table-entries
  (append '(?_ "w")
          '(?' "w")
          '(?% "< b")
          '(?\n "> b")
          '(?/ ". 14n")
          '(?* ". 23n")
          '(?. ".")
          '(?+ ".")
          '(?= ".")
          '(?- ".")
          '(?> ".")
          '(?< ".")
          '(?# ".")
          '(?\ ".")
          '(?\" "\"")))

(provide 'abella-syntax)
