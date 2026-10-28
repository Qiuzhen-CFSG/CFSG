/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianNormTripleArithmetic.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianNormDiscriminant

/-!
# IcosianNormTripleArithmetic

Three totally positive golden-integer norms summing to four have four
possible unordered patterns when a zero coordinate forces evenness.
Discriminant bounds reduce the proof to bounded integer cases.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianNormTripleArithmetic.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

namespace Atlas.Algebra
open scoped QuadraticAlgebra Matrix

/-- The four unordered quaternionic root norm patterns. -/
def IcosianRootNormShape (n : Fin 3 → GoldenInteger) : Prop :=
  List.Perm [n 0,n 1,n 2] [0,0,4] ∨
  List.Perm [n 0,n 1,n 2] [0,2,2] ∨
  List.Perm [n 0,n 1,n 2] [1,1,2] ∨
  List.Perm [n 0,n 1,n 2] [1,⟨1,1⟩,⟨2,-1⟩]

/-- A bounded integer consequence of total positivity. -/
theorem icosianNorm_pair_bound (a b : ℤ) (ha : 0≤a) (ha4 : a≤4)
    (h : 0≤a^2+a*b-b^2) : -2≤b ∧ b≤6 := by
  interval_cases a <;> constructor <;> nlinarith

/-- Only the four norm patterns satisfy the small positive norm sum and the
rank-one reduction obstruction when a coordinate vanishes. -/
theorem icosianNorm_triple_arithmetic (a b c d e f : ℤ)
    (ha : 0≤a) (hc : 0≤c) (he : 0≤e)
    (hA : 0≤a^2+a*b-b^2) (hC : 0≤c^2+c*d-d^2) (hE : 0≤e^2+e*f-f^2)
    (hs : a+c+e=4) (ht : b+d+f=0)
    (hz : a=0 ∨ c=0 ∨ e=0 → 2∣a ∧ 2∣b ∧ 2∣c ∧ 2∣d ∧ 2∣e ∧ 2∣f) :
    IcosianRootNormShape ![⟨a,b⟩,⟨c,d⟩,⟨e,f⟩] := by
  have ha4 : a≤4 := by omega
  have hc4 : c≤4 := by omega
  have he4 : e≤4 := by omega
  obtain ⟨hb0,hb1⟩ := icosianNorm_pair_bound a b ha ha4 hA
  obtain ⟨hd0,hd1⟩ := icosianNorm_pair_bound c d hc hc4 hC
  obtain ⟨hf0,hf1⟩ := icosianNorm_pair_bound e f he he4 hE
  interval_cases a <;> interval_cases c <;> interval_cases e <;> try omega
  all_goals try (norm_num at hz)
  all_goals interval_cases b <;> norm_num at hA
  all_goals interval_cases d <;> norm_num at hC
  all_goals (interval_cases f <;> try omega)
  all_goals unfold IcosianRootNormShape
  all_goals decide +kernel

end Atlas.Algebra
