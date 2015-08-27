module Propositional(dis_intro_p,
                     dis_del,
                     dis_intro) where

import ProofChecker
import Syntax
import Type

dis_intro_p p =
  in_mp (ax_impp $ thmTerm p) p

dis_del pop =
  in_mp (ax_disp $ thmTerm pop) pop

dis_intro p q =
  let pt = thmTerm p
      qt = thmTerm q
      t = ax_rm_dis pt qt pt
      pp_imp_rq = in_mp (in_mp t p) q in
   in_mp pp_imp_rq (dis_intro_p p)

