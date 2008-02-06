;; Emacs mode for Lambda Prolog module files.
;;
;; Based on tutorial at:
;;   http://two-wugs.net/emacs/mode-tutorial.html
;;

(defvar lprolog-mod-mode-hook nil)

(defvar lprolog-mod-program nil)

(add-to-list 'auto-mode-alist '("\\.mod\\'" . lprolog-mod-mode))

(defun make-regex (&rest args)
  (concat "\\<" (regexp-opt args) "\\>"))

(defvar lprolog-mod-font-lock-keywords
  (list
   (cons (make-regex "false" "true") font-lock-constant-face)
   (cons (make-regex "pi" "sigma") font-lock-keyword-face)
   (cons (make-regex "print") font-lock-keyword-face)
   (cons (make-regex "module") font-lock-keyword-face)
   (cons "\\<[A-Z][A-Za-z0-9'/]*" font-lock-variable-name-face))
  "Default highlighting for Lprolog-Mod mode")

(defun lprolog-mod-indent-line ()
  "Indent current line as Lprolog-Mod code"
  (interactive)
  (beginning-of-line)
  (let (cur-indent)
    (save-excursion
      (while (null cur-indent)
        (forward-line -1)
        (cond
         ((bobp) (setq cur-indent 0))
         ((looking-at "^%"))
         ((looking-at "^\\W*$"))
         ((looking-at "^.*\\.\\W*$") (setq cur-indent 0))
         ((looking-at "^.*:-") (setq cur-indent default-tab-width))
         (t (if (> (current-indentation) 0)
                (setq cur-indent (current-indentation))
              (progn
                (let ((start (point)))
                  (forward-word 1)
                  (setq cur-indent (1+ (- (point) start))))))))))
    (indent-line-to cur-indent)))

(defvar lprolog-mod-mode-syntax-table
  (let ((lprolog-mod-mode-syntax-table (make-syntax-table)))
    (modify-syntax-entry ?_ "w" lprolog-mod-mode-syntax-table)
    (modify-syntax-entry ?' "w" lprolog-mod-mode-syntax-table)
    (modify-syntax-entry ?/ "w" lprolog-mod-mode-syntax-table)
    (modify-syntax-entry ?% "<" lprolog-mod-mode-syntax-table)
    (modify-syntax-entry ?\n ">" lprolog-mod-mode-syntax-table)
    (modify-syntax-entry ?. "." lprolog-mod-mode-syntax-table)
    (modify-syntax-entry ?+ "." lprolog-mod-mode-syntax-table)
    (modify-syntax-entry ?- "." lprolog-mod-mode-syntax-table)
    (modify-syntax-entry ?* "." lprolog-mod-mode-syntax-table)
    (modify-syntax-entry ?= "." lprolog-mod-mode-syntax-table)
    (modify-syntax-entry ?> "." lprolog-mod-mode-syntax-table)
    (modify-syntax-entry ?< "." lprolog-mod-mode-syntax-table)
    (modify-syntax-entry ?# "." lprolog-mod-mode-syntax-table)
    (modify-syntax-entry ?\ "." lprolog-mod-mode-syntax-table)
    lprolog-mod-mode-syntax-table)
  "Syntax table for lprolog-mod-mode")

(defun lprolog-mod-mode ()
  "Major mode for editing Lambda Prolog module files"
  (interactive)
  (kill-all-local-variables)
  (set-syntax-table lprolog-mod-mode-syntax-table)
  (set (make-local-variable 'font-lock-defaults)
       '(lprolog-mod-font-lock-keywords))
  (set (make-local-variable 'indent-line-function) 'lprolog-mod-indent-line)
  (setq major-mode 'lprolog-mod-mode)
  (setq mode-name "Lambda Prolog module")
  (run-hooks 'lprolog-mod-mode-hook))

(provide 'lprolog-mod-mode)
