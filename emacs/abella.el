;; Emacs mode for Abella theorem files.
;;
;; Based on tutorial at:
;;   http://two-wugs.net/emacs/mode-tutorial.html
;;

(defvar abella-mode-hook nil)

(add-to-list 'auto-mode-alist '("\\.thm\\'" . abella-mode))

(defun make-regex (&rest args)
  (concat "\\<" (regexp-opt args) "\\>"))

(defvar abella-font-lock-keywords
  (list
    (cons (make-regex "Define" "Theorem \\W*" "Axiom") font-lock-keyword-face)
;   (cons (make-regex "true" "false") font-lock-constant-face)
;   (cons (make-regex "forall" "exists" "nabla") font-lock-keyword-face)
;   (cons (make-regex "intros" "apply" "case" "induction" "search"
;                     "to" "on" "inst" "with" "cut" "unfold"
;                     "assert" "exists" "split" "split*" "clear")
   font-lock-keyword-face)
  "Default highlighting for Abella major mode")

(defvar abella-mode-syntax-table
  (let ((abella-mode-syntax-table (make-syntax-table)))
    (modify-syntax-entry ?_ "w" abella-mode-syntax-table)
    (modify-syntax-entry ?' "w" abella-mode-syntax-table)
    (modify-syntax-entry ?/ "w" abella-mode-syntax-table)
    (modify-syntax-entry ?% "<" abella-mode-syntax-table)
    (modify-syntax-entry ?\n ">" abella-mode-syntax-table)
    (modify-syntax-entry ?. "." abella-mode-syntax-table)
    (modify-syntax-entry ?+ "." abella-mode-syntax-table)
    (modify-syntax-entry ?- "." abella-mode-syntax-table)
    (modify-syntax-entry ?* "." abella-mode-syntax-table)
    (modify-syntax-entry ?= "." abella-mode-syntax-table)
    (modify-syntax-entry ?> "." abella-mode-syntax-table)
    (modify-syntax-entry ?< "." abella-mode-syntax-table)
    (modify-syntax-entry ?# "." abella-mode-syntax-table)
    (modify-syntax-entry ?\ "." abella-mode-syntax-table)
    abella-mode-syntax-table)
  "Syntax table for Abella major mode")

;; Proof navigation
(defvar abella-mode-keymap
  (let ((abella-mode-keymap (make-keymap)))
    (define-key abella-mode-keymap "\C-c\C-e" 'abella-previous-command)
    (define-key abella-mode-keymap "\C-c\C-n" 'abella-foward-command)
    (define-key abella-mode-keymap "\C-c\C-p" 'abella-backward-command)
    abella-mode-keymap)
  "Keymap for Abella major mode")

(defun abella-previous-command ()
  (interactive)
  (backward-sentence)
  (abella-foward-command))

(defun abella-foward-command ()
  (interactive)
  (let ((beg (point))
        str)
    (forward-sentence)
    (setq str (buffer-substring beg (point)))
    (other-window 1)
    (switch-to-buffer "*shell*")
    (end-of-buffer)
    (insert str)
    (comint-send-input)
    (other-window -1)))

(defun abella-backward-command ()
  (interactive)
  (backward-sentence)
  (other-window 1)
  (switch-to-buffer "*shell*")
  (end-of-buffer)
  (insert "undo.")
  (comint-send-input)
  (other-window -1))

(defun abella-mode ()
  "Major mode for editing abella theorem files"
  (interactive)
  (kill-all-local-variables)
  (set-syntax-table abella-mode-syntax-table)
  (use-local-map abella-mode-keymap)
  (set (make-local-variable 'font-lock-defaults)
       '(abella-font-lock-keywords))
;  (set (make-local-variable 'indent-line-function) 'abella-indent-line)
  (setq major-mode 'abella-mode)
  (setq mode-name "Abella")
  (run-hooks 'abella-mode-hook))

(provide 'abella-mode)
