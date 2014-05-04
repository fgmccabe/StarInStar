;; 
;; SMIE grammar for Star
;;

(require 'smie)

(defconst star-basic-grammar
  (smie-prec2->grammar
   (smie-merge-prec2s
    (smie-bnf->prec2
     '(
