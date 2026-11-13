; Inductive strengthening exported from the RTL proof: the exclusive monitor
; is cleared by the store that silently upgrades E to M.
(declare-const cache_line_q (_ BitVec 2))
(declare-const excl_mon_q (_ BitVec 1))
(assert (not (and (= cache_line_q #b11) (= excl_mon_q #b1))))
