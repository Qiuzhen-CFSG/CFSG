module

public import Theory.SpecificGroups.MacWilliams.UnitaryQuadraticScalar

/-!
# Exhaustive scalar weight-ten certificate

The 168 scalar quadratic codes below include every code whose sixteen-value
truth table has weight ten. The finite check uses an explicit list of all 1,024
codes and kernel reduction; the public theorem extracts membership from it.
This is the scalar prerequisite to the balanced unitary coverage certificate.

Source: MacWilliams, Trans. AMS 150 (1970),
DOI 10.1090/S0002-9947-1970-0276324-3.
-/

namespace MacWilliamsSylow.QuadraticCertificate

@[expose] public def scalarCandidates : List (Fin 1024) :=
  [
    198, 199, 201, 203, 205, 206, 214, 215, 217, 219, 220, 223,
    230, 231, 233, 234, 237, 239, 246, 247, 248, 251, 253, 255,
    293, 295, 298, 299, 301, 302, 309, 311, 314, 315, 316, 319,
    357, 359, 361, 362, 366, 367, 373, 375, 376, 379, 382, 383,
    421, 422, 426, 427, 429, 431, 436, 439, 442, 443, 445, 447,
    453, 454, 457, 459, 462, 463, 468, 471, 473, 475, 478, 479,
    531, 535, 539, 540, 541, 542, 563, 567, 570, 572, 573, 575,
    595, 599, 601, 604, 606, 607, 627, 631, 632, 637, 638, 639,
    659, 662, 667, 668, 669, 671, 690, 695, 699, 700, 701, 703,
    707, 710, 713, 717, 718, 719, 738, 743, 745, 749, 750, 751,
    787, 789, 795, 796, 798, 799, 803, 805, 810, 813, 814, 815,
    849, 855, 859, 860, 862, 863, 865, 871, 874, 877, 878, 879,
    915, 916, 923, 925, 926, 927, 930, 933, 939, 941, 942, 943,
    961, 966, 971, 973, 974, 975, 1008, 1015, 1019, 1021, 1022, 1023
  ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem scalar_candidates_checks :
    ((List.finRange 1024).all fun a =>
      if scalarWeight a = 10 then scalarCandidates.any fun b => decide (a = b) else true) = true :=
  by decide +kernel

public theorem scalar_candidates_cover : ∀ a : Fin 1024,
    scalarWeight a = 10 → a ∈ scalarCandidates := by
  intro a ha
  have h := List.all_eq_true.mp scalar_candidates_checks a (List.mem_finRange a)
  rw [if_pos ha] at h
  obtain ⟨b, hb, he⟩ := List.any_eq_true.mp h
  exact of_decide_eq_true he ▸ hb

end MacWilliamsSylow.QuadraticCertificate



