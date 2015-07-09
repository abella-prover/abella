;; abella.el --- Proof General instance for Abella
;;
;; Copyright (C) 2011-2013 INRIA
;;
;; Authors: Clement Houtmann <Clement.Houtmann@inria.fr>
;;          Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>

(eval-and-compile
  (require 'proof-site)                 ; compilation for abella
  (proof-ready-for-assistant 'abella))

(require 'proof)
(require 'proof-easy-config)            ; easy configure mechanism
(require 'abella-syntax)

;; broken : callback for handling specific output
(defvar abella-shell-handle-output
  '(lambda (cmd string)
      (when (string-match "Proof \\(completed\\|aborted\\)\." string)
  (proof-clean-buffer proof-goals-buffer)
)))

(proof-easy-config
 'abella "Abella"
 proof-prog-name                "abella"
 proof-terminal-string          "."
 proof-script-comment-start-regexp      "%"
 proof-script-fly-past-comments t
 proof-script-comment-end-regexp        "\n"
 ;proof-script-comment-end-regexp       "^[^ *%]"
 ;; for clearing goals -> broken
 ;proof-shell-clear-goals-regexp   "Proof \\(completed\\|aborted\\)\."
 ;proof-shell-eager-annotation-start "Proof \\(completed\\|aborted\\)\."
 ;proof-shell-eager-annotation-end ""
 ;; for grouping proofs -> broken
 ;proof-goal-command-regexp    "Theorem .*\."
 ;proof-shell-proof-completed-regexp   "Proof completed\."
 proof-goal-command-regexp proof-no-regexp
 proof-shell-proof-completed-regexp proof-no-regexp
 proof-completed-proof-behaviour 'closeany
 proof-assistant-home-page       "http://abella-prover.org"
 proof-shell-annotated-prompt-regexp "^.* < $"
 proof-shell-quit-cmd            "Quit."
 proof-shell-start-goals-regexp  "<<"
 proof-shell-end-goals-regexp    ">>"
 proof-shell-restart-cmd         "#reset."
 proof-shell-error-regexp        "Error:.*\\|\\(Syntax\\|Typing\\|Unification\\|Unknown\\) error\."
 proof-shell-strip-crs-from-input nil
 proof-save-command-regexp      proof-no-regexp
 proof-find-and-forget-fn   'abella-find-and-forget-fn
 proof-script-syntax-table-entries  abella-mode-syntax-table-entries
 proof-script-font-lock-keywords  abella-script-font-lock-keywords
 proof-goals-font-lock-keywords  abella-goals-font-lock-keywords
 proof-response-font-lock-keywords  abella-response-font-lock-keywords
 proof-shell-handle-output-system-specific abella-shell-handle-output
 ;proof-non-undoables-regexp    "undo\\|Back\\|Reset\\|abort\\|[a-z].*"
)

(provide 'abella)

(defun abella-count (span)
  (setq next (next-span span 'name))
  (if (eq next nil)
    1
    (+ 1 (abella-count next))))

(defun abella-find-and-forget-cmd (span)
  (setq cmd (span-property span 'cmd))
  (cond
    ((eq cmd nil) "") ; comment
    ;; ((string-match "Specification.*" cmd) "Reset.")
    ;; ((string-match "Theorem.*" cmd) "abort.")
    ;; ((string-match
    ;;   "\\(Define\\|CoDefine\\|Kind\\|Type\\|Split\\|Close\\).*"
    ;;   cmd) "Back.")
    ;; (t "undo."))
    (t "#back."))
  )

(defun abella-find-and-forget-fn (span)
  (setq ans ())
  (while span
    (setq typ (span-property span 'type))
    (if (not (eq typ 'comment))
      (let ((current-cmd (abella-find-and-forget-cmd span)))
        (setq ans (cons current-cmd ans))))
    (setq span (next-span span 'type)))
  ans)

;;; abella.el ends here
