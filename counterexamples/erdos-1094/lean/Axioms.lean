import Erdos1094

/-! Prints the axioms each final theorem depends on. Run with `lake env lean Axioms.lean`. -/

-- Lucas digit-dominance engine
#print axioms Erdos1094.not_dvd_choose_iff_forall_digit_le
#print axioms Erdos1094.not_dvd_choose_of_digitsLeFuel
#print axioms Erdos1094.dvd_choose_of_hasCarryFuel
#print axioms Erdos1094.minFac_choose_eq

-- Sanity anchor: the four classical exceptional pairs of [ELS93] p. 222
#print axioms Erdos1094.minFac_choose_62_6
#print axioms Erdos1094.minFac_choose_959_56
#print axioms Erdos1094.minFac_choose_474_66
#print axioms Erdos1094.minFac_choose_284_28
#print axioms Erdos1094.classical_four_summary

-- The six new exceptional pairs with least prime factor > 17
#print axioms Erdos1094.minFac_choose_57074_22050
#print axioms Erdos1094.minFac_choose_57075_22050
#print axioms Erdos1094.minFac_choose_57077_22052
#print axioms Erdos1094.minFac_choose_31152939_1772289
#print axioms Erdos1094.minFac_choose_32634047_2143377
#print axioms Erdos1094.minFac_choose_32634223_2143531

-- Disproof of [ELS93] Conjecture 2 (p. 222)
#print axioms Erdos1094.els93_conjecture2_counterexample
#print axioms Erdos1094.els93_conjecture2_false
#print axioms Erdos1094.els93_conjecture2_false_rat

-- Disproof of [ELS93] Conjecture 1 (p. 222)
#print axioms Erdos1094.els93_conjecture1_counterexample
#print axioms Erdos1094.els93_conjecture1_false
#print axioms Erdos1094.els93_conjecture1_six_new_counterexamples

-- Eleven missing p = 17, k ≤ 12000 exceptional pairs and the (13277, 900) misprint
#print axioms Erdos1094.missing_p17_le_12000
#print axioms Erdos1094.misprint_13277_900_and_14277_900
