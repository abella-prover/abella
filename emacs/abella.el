;; Emacs mode for Abella theorem files.
;;
;; Based on tutorial at:
;;   http://two-wugs.net/emacs/mode-tutorial.html
;;

(defvar abella-mode-hook nil)

(add-to-list 'auto-mode-alist '("\\.thm\\'" . abella-mode))

(defun make-regex (&rest args)
  (concat "\\<\\(" (regexp-opt args) "\\)\\>"))

(defun make-command-regex (&rest args)
  (concat "\\<\\(" (regexp-opt args) "\\)[^.]*."))

(require 'font-lock)
(defvar abella-font-lock-keywords
  (list
    (cons (make-command-regex "Set" "Query") font-lock-type-face)
    (cons (make-regex "Import" "Specification") font-lock-variable-name-face)
    (cons (make-command-regex "Type" "Kind" "Close") font-lock-keyword-face)
    (cons (make-command-regex "Define" "CoDefine") font-lock-keyword-face)
    (cons (make-command-regex "Theorem" "Split") font-lock-function-name-face)
    (cons (make-regex "skip") font-lock-warning-face))
  "Default highlighting for Abella major mode")

(setq xemacsp (and (boundp 'xemacsp) xemacsp))

(defvar abella-mode-syntax-table
  (let ((abella-mode-syntax-table (make-syntax-table)))
    (modify-syntax-entry ?_ "w"     abella-mode-syntax-table)
    (modify-syntax-entry ?' "w"     abella-mode-syntax-table)
    (modify-syntax-entry ?/ (if xemacsp "w 14" "w 14n")
                         abella-mode-syntax-table)
    (modify-syntax-entry ?* (if xemacsp ". 23" ". 23n")
                         abella-mode-syntax-table)
    (modify-syntax-entry ?% "< b"   abella-mode-syntax-table)
    (modify-syntax-entry ?\n "> b"  abella-mode-syntax-table)
    (modify-syntax-entry ?. "."     abella-mode-syntax-table)
    (modify-syntax-entry ?+ "."     abella-mode-syntax-table)
    (modify-syntax-entry ?- "."     abella-mode-syntax-table)
    (modify-syntax-entry ?= "."     abella-mode-syntax-table)
    (modify-syntax-entry ?> "."     abella-mode-syntax-table)
    (modify-syntax-entry ?< "."     abella-mode-syntax-table)
    (modify-syntax-entry ?# "."     abella-mode-syntax-table)
    (modify-syntax-entry ?\ "."     abella-mode-syntax-table)
    abella-mode-syntax-table)
  "Syntax table for Abella major mode")

;; Proof navigation
(defvar abella-mode-keymap
  (let ((abella-mode-keymap (make-keymap)))
    (define-key abella-mode-keymap "\C-c\C-e" 'abella-previous-command-send)
    (define-key abella-mode-keymap "\C-c\C-n" 'abella-forward-command-send)
    (define-key abella-mode-keymap "\C-c\C-p" 'abella-backward-command-send)
    abella-mode-keymap)
  "Keymap for Abella major mode")

(defun abella-forward-command ()
  (interactive)
  (search-forward-regexp "%\\|\\.")
  (if (equal (match-string 0) "%")
      (progn (beginning-of-line)
             (next-line 1)
             (abella-forward-command))))


(defun abella-backward-command ()
  (interactive)
  (backward-char 1)
  (abella-backward-command-rec)
  (if (not (bobp))
    (forward-char 1)))

(defun abella-backward-command-rec ()
  (interactive)
  (while (search-backward "%" (point-at-bol) t))
  (if (not (search-backward "." (point-at-bol) t))
      (progn
        (beginning-of-line 1)
        (if (not (bobp))
            (progn (end-of-line 0)
                   (abella-backward-command-rec))))))

(defun abella-previous-command-send ()
  (interactive)
  (abella-backward-command)
  (abella-forward-command-send))

(defun abella-forward-command-send ()
  (interactive)
  (let ((beg (point))
        str)
    (abella-forward-command)
    (setq str (buffer-substring beg (point)))
    (other-window 1)
    (switch-to-buffer "*shell*")
    (end-of-buffer)
    (insert str)
    (comint-send-input)
    (other-window -1)))

(defun abella-backward-command-send ()
  (interactive)
  (abella-backward-command)
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
  (set (make-local-variable 'comment-start) "%")
;  (set (make-local-variable 'indent-line-function) 'abella-indent-line)
  (setq major-mode 'abella-mode)
  (setq mode-name "Abella")
  (run-hooks 'abella-mode-hook))

(provide 'abella-mode)
