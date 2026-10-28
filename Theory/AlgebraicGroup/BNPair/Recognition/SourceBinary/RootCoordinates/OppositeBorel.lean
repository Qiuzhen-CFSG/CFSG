module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.AlternatingLength
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.EndpointIndices

/-!
# The longest Borel is opposite to the original Borel

An increasing-length Bruhat product excludes the lower cell. Consequently
`B ∩ B^(s*w) ≤ B ∩ B^w` at every left ascent. The marked finite dihedral
ascent chain reaches the unique longest element from every Weyl class;
saturation therefore gives `B ∩ B^w₀ = H`. The finite split Sylow and odd
torus then give `B ∩ U^w₀ = 1`, with the entire original Borel retained.

All conjugations are right conjugations, `A^n = n⁻¹ A n`, and all lifts
belong to the supplied N. These are Carter Propositions 2.5.3–2.5.5 in
`refs/KGroup/GLS3/Chapter2Ca2.tex`. The argument reconstructs the corrupted
OCR ascent display using the literal multiplication order; it requires no
root system, prescribed dihedral order, perfectness or model recognition.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {X : Type*} [Group X] {T : TitsSystem (X := X)}

/-- The conjugate of the original Borel by a Weyl class. -/
@[expose] def borelConjugate (w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) : Subgroup X :=
  rightConjugate T.B (representative w : X)

theorem borelConjugate_eq (w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N)
    (n : T.N) (hn : QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) n = w) :
    borelConjugate w = rightConjugate T.B (n : X) :=
  rightConjugate_eq_of_quotient_eq T.B (inf_le_left.trans T.B.le_normalizer)
    (representative w) n ((representative_spec w).trans hn.symm)

/-- Carter 2.5.3 with the literal right-conjugation convention. -/
theorem ascent_conjugate_intersection_le
    {s w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N} (hs : s ∈ T.S)
    (hlen : T.wordLength w ≤ T.wordLength (s*w))
    (ns nw : T.N)
    (hns : QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) ns = s)
    (hnw : QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) nw = w) :
    rightConjugate T.B (ns : X) ⊓ rightConjugate T.B ((nw : X)⁻¹) ≤ T.B := by
  intro x hx
  have hnsP : (ns : X) ∈ T.standardParabolic {s} :=
    T.bruhatCell_subset_standardParabolic_of_mem (Set.mem_singleton s)
      (T.representative_mem_bruhatCell s ns hns)
  have hxP : x ∈ T.standardParabolic {s} := by
    have h := (T.standardParabolic {s}).mul_mem
      ((T.standardParabolic {s}).mul_mem ((T.standardParabolic {s}).inv_mem hnsP)
        (T.B_le_standardParabolic {s} hx.1)) hnsP
    change (ns : X)⁻¹ * ((ns : X) * x * (ns : X)⁻¹) * (ns : X) ∈
      T.standardParabolic {s} at h
    simpa only [inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using h
  have hxcell : x ∈ (T.B : Set X) ∪ T.bruhatCell s :=
    singleton_parabolic_cells hs ▸ hxP
  rcases hxcell with hxB | hxS
  · exact hxB
  · exfalso
    have hprod : x * (nw : X) ∈ T.bruhatCell (s*w) :=
      T.bruhatCell_mul_bruhatCell_subset_of_wordLength_le hs w hlen
        ⟨x, hxS, nw, T.representative_mem_bruhatCell w nw hnw, rfl⟩
    have hsame : x * (nw : X) ∈ T.bruhatCell w := by
      have hmem := mul_mem_doubleCoset T.B T.N w T.B.one_mem hx.2
        (T.representative_mem_bruhatCell w nw hnw)
      change 1 * (nw : X) * ((nw : X)⁻¹ * x * ((nw : X)⁻¹)⁻¹) ∈ T.bruhatCell w at hmem
      simpa only [inv_inv, one_mul, mul_inv_cancel_left, mul_assoc] using hmem
    have he := T.doubleCoset_index_unique hprod hsame
    exact (T.involutions s hs).1 (mul_right_cancel (he.trans (one_mul w).symm))

/-- Carter 2.5.4: a left ascent shrinks the Borel intersection. -/
theorem borel_intersection_ascent_le
    {s w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N} (hs : s ∈ T.S)
    (hlen : T.wordLength w ≤ T.wordLength (s*w)) :
    T.B ⊓ borelConjugate (s*w) ≤ T.B ⊓ borelConjugate w := by
  let ns := representative s
  let nw := representative w
  have hns := representative_spec s
  have hnw := representative_spec w
  rw [borelConjugate_eq (s*w) (ns*nw) (by rw [map_mul, hns, hnw])]
  intro x hx
  refine ⟨hx.1, ?_⟩
  change (nw : X) * x * (nw : X)⁻¹ ∈ T.B
  apply ascent_conjugate_intersection_le hs hlen ns nw hns hnw
  constructor
  · change (ns : X) * ((nw : X) * x * (nw : X)⁻¹) * (ns : X)⁻¹ ∈ T.B
    have h := hx.2
    change ((ns : X) * (nw : X)) * x * ((ns : X) * (nw : X))⁻¹ ∈ T.B at h
    simpa only [mul_inv_rev, mul_assoc] using h
  · change (nw : X)⁻¹ * ((nw : X) * x * (nw : X)⁻¹) * ((nw : X)⁻¹)⁻¹ ∈ T.B
    simpa only [inv_inv, inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using (show x ∈ T.B from hx.1)

variable {P : Fin 2 → Subgroup X} (d : MarkedQuotient P)

/-- The longest intersection is contained in every Borel intersection. -/
theorem longest_borel_intersection_le (w : Weyl d) :
    d.tits.B ⊓ borelConjugate (longest d) ≤ d.tits.B ⊓ borelConjugate w := by
  generalize hn : rotationOrder d - d.tits.wordLength w = n
  induction n using Nat.strong_induction_on generalizing w with
  | h n ih =>
    by_cases hw : w = longest d
    · rw [hw]
    · obtain ⟨i, hi⟩ := exists_left_ascent d hw
      have hle := wordLength_le_rotationOrder d w
      have hle' := wordLength_le_rotationOrder d (d.simple i*w)
      exact (ih (rotationOrder d - d.tits.wordLength (d.simple i*w)) (by omega)
        (d.simple i*w) rfl).trans
          (borel_intersection_ascent_le (d.simple_mem i) (by omega))

/-- Saturation and the ascent chain identify the opposite Borel exactly. -/
theorem borel_inf_opposite (split : SplitData d.tits) :
    d.tits.B ⊓ borelConjugate (longest d) = d.tits.B ⊓ d.tits.N := by
  apply le_antisymm
  · rw [← split.saturation]
    apply le_iInf
    intro n
    have h := (longest_borel_intersection_le d
      (QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) n)).trans inf_le_right
    rwa [borelConjugate_eq _ n rfl] at h
  · apply le_inf inf_le_left
    intro x hx
    change x ∈ rightConjugate d.tits.B (representative (longest d) : X ⧸ d.D)
    have h := (torus_conjugate (representative (longest d))).symm ▸ hx
    exact h.1

/-- The entire original Borel meets the opposite unipotent subgroup trivially. -/
theorem borel_inf_opposite_unipotent (split : SplitData d.tits) :
    d.tits.B ⊓ unipotentConjugate split (longest d) = ⊥ := by
  apply eq_bot_iff.mpr
  have hB : unipotentConjugate split (longest d) ≤ borelConjugate (longest d) :=
    comap_mono split.U_le
  have hH : d.tits.B ⊓ unipotentConjugate split (longest d) ≤ d.tits.B ⊓ d.tits.N := by
    rw [← borel_inf_opposite d split]
    exact inf_le_inf_left _ hB
  have hU : d.tits.B ⊓ unipotentConjugate split (longest d) ≤ split.U := by
    rw [unipotentConjugate, borel_inf_unipotent_conjugate split]
    exact inf_le_left
  exact (le_inf hU (hH.trans inf_le_right)).trans (le_of_eq split.unipotent_inf_N)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
