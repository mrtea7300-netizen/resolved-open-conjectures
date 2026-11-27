import Kellner

/-! Prints the axioms each final theorem depends on. Run with `lake env lean Axioms.lean`. -/

-- Theorem 1 (Kellner's conjecture and its variants); hypotheses `AxlerLower`, `AxlerUpper`
#print axioms Kellner.kellner
#print axioms Kellner.kellner_partB
#print axioms Kellner.kellner_partC
#print axioms Kellner.kellner_partD
-- no hypotheses
#print axioms Kellner.kellner_sharp
#print axioms Kellner.kellner_exceptions
-- Corollary A (A094960); hypotheses `AxlerLower`, `AxlerUpper`
#print axioms Kellner.A094960_complete
#print axioms Kellner.not_derivIntegral_of_ge
-- no hypotheses
#print axioms Kellner.A094960_upto_192
-- the same from Axler 2016 Corollary 3.5 and Axler 2018 Theorem 2 as published
#print axioms Kellner.axlerLower_of_cor35
#print axioms Kellner.axlerUpper_of_thm2
#print axioms Kellner.kellner_of_axler
#print axioms Kellner.kellner_partD_of_axler
#print axioms Kellner.A094960_complete_of_axler
-- the pieces
#print axioms Kellner.lemma3
#print axioms Kellner.card_failing_le
#print axioms Kellner.prop6
#print axioms Kellner.prop7
#print axioms Kellner.windowOK_of_lt
#print axioms Kellner.partC_small
#print axioms Kellner.partD_small
#print axioms Kellner.lemma1

-- The cross-check with `native_decide` (NOT used by anything above):
#print axioms Kellner.Native.windowOK_of_lt
#print axioms Kellner.Native.partC_small
#print axioms Kellner.Native.partD_small
