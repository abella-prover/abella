;; Emacs mode for Lambda Prolog module files.
;;
;; Based on tutorial at:
;;   http://two-wugs.net/emacs/mode-tutorial.html
;;

(defvar lprolog-mode-hook nil)

(defvar lprolog-program nil)

(add-to-list 'auto-mode-alist '("\\.mod\\'" . lprolog-mode))
(add-to-list 'auto-mode-alist '("\\.sig\\'" . lprolog-mode))

(defun make-regex (&rest args)
  (concat "\\<\\(" (regexp-opt args) "\\)\\>"))

(require 'font-lock)
(defvar lprolog-font-lock-keywords
  (list
   (cons (make-regex "false" "true") font-lock-constant-face)
   (cons (make-regex "pi" "sigma") font-lock-keyword-face)
   (cons (make-regex "type" "kind") font-lock-keyword-face)
   (cons (make-regex "module" "sig") font-lock-type-face)
   (cons "\\<[A-Z][A-Za-z0-9'/]*" font-lock-variable-name-face))
  "Default highlighting for Lprolog mode")

(setq xemacsp (and (boundp 'xemacsp) xemacsp))

(defvar lprolog-mode-syntax-table
  (let ((lprolog-mode-syntax-table (make-syntax-table)))
    (modify-syntax-entry ?_ "w"     lprolog-mode-syntax-table)
    (modify-syntax-entry ?' "w"     lprolog-mode-syntax-table)
    (modify-syntax-entry ?/ (if xemacsp "w 14" "w 14n")
                         lprolog-mode-syntax-table)
    (modify-syntax-entry ?* (if xemacsp ". 23" ". 23n")
                         lprolog-mode-syntax-table)
    (modify-syntax-entry ?% "< b"   lprolog-mode-syntax-table)
    (modify-syntax-entry ?\n "> b"  lprolog-mode-syntax-table)
    (modify-syntax-entry ?. "."     lprolog-mode-syntax-table)
    (modify-syntax-entry ?+ "."     lprolog-mode-syntax-table)
    (modify-syntax-entry ?- "."     lprolog-mode-syntax-table)
    (modify-syntax-entry ?= "."     lprolog-mode-syntax-table)
    (modify-syntax-entry ?> "."     lprolog-mode-syntax-table)
    (modify-syntax-entry ?< "."     lprolog-mode-syntax-table)
    (modify-syntax-entry ?# "."     lprolog-mode-syntax-table)
    (modify-syntax-entry ?\ "."     lprolog-mode-syntax-table)
    lprolog-mode-syntax-table)
  "Syntax table for lprolog-mode")

(defun lprolog-mode ()
  "Major mode for editing Lambda Prolog files"
  (interactive)
  (kill-all-local-variables)
  (set-syntax-table lprolog-mode-syntax-table)
  (set (make-local-variable 'font-lock-defaults)
       '(lprolog-font-lock-keywords))
  (set (make-local-variable 'comment-start) "%")
  (setq major-mode 'lprolog-mode)
  (setq mode-name "Lambda Prolog")
  (run-hooks 'lprolog-mode-hook))

(provide 'lprolog-mode)
