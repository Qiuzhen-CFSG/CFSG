module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.Row12.Geometry
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.GraphBound.Odd
public import Mathlib.GroupTheory.Index

/-!
# An upper bound for the row-12 normalizer

The ten-point configuration has exactly two vertices of induced degree nine.
Thus its graph stabilizer preserves their pair. A checked word transports the
reference pair to this pair, and the existing four-point graph-base certificates
bound its stabilizer by 2 · 256 · 36. An already certified odd symmetry preserves
the configuration, so its even stabilizer has at most 9216 elements.

Source: the literal Held graph and ATLAS words, GLS3 Table 5.3p.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.Row12
open Subgroup NormalizerGraph NormalizerGraph.CardBound

private def centralPair : Finset (Fin 2058) := {480, 1444}
private def degree (x : Fin 2058) : ℕ := (fixedVertices.filter (Adj x)).card

set_option maxRecDepth 8192 in
private theorem centralPair_check : ∀ x : Fin 2058,
    x ∈ centralPair ↔ x ∈ fixedVertices ∧ degree x = 9 := by
  apply Held.TwoLocalCandidates.Cores.allLetters
  decide +kernel

private theorem degree_invariant (σ : Equiv.Perm (Fin 2058))
    (hσ : σ ∈ graphStabilizer) (x : Fin 2058) : degree (σ x) = degree x := by
  symm
  apply Finset.card_equiv σ
  intro y
  simp only [Finset.mem_filter, hσ.2 y, hσ.1 x y]

private theorem centralPair_invariant (σ : Equiv.Perm (Fin 2058))
    (hσ : σ ∈ graphStabilizer) (x : Fin 2058) :
    σ x ∈ centralPair ↔ x ∈ centralPair := by
  rw [centralPair_check, centralPair_check, hσ.2 x, degree_invariant σ hσ]

private abbrev S1 (K : Subgroup (Equiv.Perm (Fin 2058))) :=
  ↥(MulAction.stabilizer K (0 : Fin 2058))
private abbrev S2 (K : Subgroup (Equiv.Perm (Fin 2058))) :=
  ↥(MulAction.stabilizer (S1 K) (2 : Fin 2058))
private abbrev S3 (K : Subgroup (Equiv.Perm (Fin 2058))) :=
  ↥(MulAction.stabilizer (S2 K) (3 : Fin 2058))

private theorem fix2 {K : Subgroup (Equiv.Perm (Fin 2058))}
    (hp : ∀ σ : K, σ.val 1 = 0 ∨ σ.val 1 = 1) (g : S1 K) :
    Fixes 2 g.val.val := by
  have h0 : g.val.val 0 = 0 := g.property
  have h1 : g.val.val 1 = 1 := (hp g.val).resolve_left (by
    intro h
    have he := g.val.val.injective (h.trans h0.symm)
    norm_num at he)
  intro x hx
  have hc : x = 0 ∨ x = 1 := by
    have hx0 : x.val = 0 ∨ x.val = 1 := by omega
    exact hx0.imp Fin.ext Fin.ext
  rcases hc with rfl | rfl
  · exact h0
  · exact h1

private theorem fix3 {K : Subgroup (Equiv.Perm (Fin 2058))}
    (hp : ∀ σ : K, σ.val 1 = 0 ∨ σ.val 1 = 1) (g : S2 K) :
    Fixes 3 g.val.val.val := by
  intro x hx
  by_cases h : x.val < 2
  · exact fix2 hp g.val x h
  · have he : x = 2 := Fin.ext (by omega)
    subst x
    exact g.property

private theorem fix4 {K : Subgroup (Equiv.Perm (Fin 2058))}
    (hp : ∀ σ : K, σ.val 1 = 0 ∨ σ.val 1 = 1) (g : S3 K) :
    Fixes 4 g.val.val.val.val := by
  intro x hx
  by_cases h : x.val < 3
  · exact fix3 hp g.val x h
  · have he : x = 3 := Fin.ext (by omega)
    subst x
    exact g.property

private theorem reference_pair_card_le (K : Subgroup (Equiv.Perm (Fin 2058)))
    (hK : K ≤ preservingGroup)
    (hp : ∀ σ : K, ∀ i : Fin 2058, i = 0 ∨ i = 1 → σ.val i = 0 ∨ σ.val i = 1) :
    Nat.card K ≤ 18432 := by
  have h3 : Nat.card (S3 K) = 1 := by
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨1, fun g => ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact four_fixed_eq_one _ (hK g.val.val.val.property)
      (fix4 (fun σ => hp σ 1 (Or.inr rfl)) g)
  have h2 : Nat.card (S2 K) ≤ 36 * Nat.card (S3 K) :=
    orbit_upper (3 : Fin 2058) (fun x => weight33 x.val)
      (fun g x => invariant33 _ (hK g.val.val.property)
        (fix3 (fun σ => hp σ 1 (Or.inr rfl)) g) x) cell3_card.le
  have h1 : Nat.card (S1 K) ≤ 256 * Nat.card (S2 K) :=
    orbit_upper (2 : Fin 2058) (fun x => weight22 x.val)
      (fun g x => invariant22 _ (hK g.val.property)
        (fix2 (fun σ => hp σ 1 (Or.inr rfl)) g) x) cell2_card.le
  have h0 : Nat.card (MulAction.orbit K (0 : Fin 2058)) ≤ 2 := by
    have hc : Nat.card {x : Fin 2058 // x = 0 ∨ x = 1} = 2 := by
      rw [Nat.card_eq_fintype_card]
      decide +kernel
    rw [← hc]
    apply Nat.card_le_card_of_injective
      (fun x : MulAction.orbit K (0 : Fin 2058) =>
        (⟨x.val, ?_⟩ : {x : Fin 2058 // x = 0 ∨ x = 1}))
      (fun x y h => Subtype.ext (congrArg
        (fun z : {x : Fin 2058 // x = 0 ∨ x = 1} => z.val) h))
    obtain ⟨g, hg⟩ := x.property
    rw [← hg]
    exact hp g 0 (Or.inl rfl)
  have he := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K (0 : Fin 2058))
  rw [Nat.card_prod] at he
  have hb : Nat.card K ≤ 2 * Nat.card (S1 K) := by
    rw [← he]
    exact Nat.mul_le_mul_right _ h0
  omega

private def transporter : He :=
  (List.map (fun i : ℕ => if i = 1 then a else b)
    [2,1,2,1,2,2,1,2,2,1,2,1,2,1,2,2,2,2,1,2,2,2,2,1,2]).prod

set_option maxRecDepth 4096 in
private theorem transporter_images :
    representation transporter 0 = 480 ∧ representation transporter 1 = 1444 := by
  decide +kernel

private theorem conjugated_pair (t : Equiv.Perm (Fin 2058))
    (ht : t 0 = 480 ∧ t 1 = 1444) (σ : Equiv.Perm (Fin 2058))
    (hσ : σ ∈ graphStabilizer) (i : Fin 2058) (hi : i = 0 ∨ i = 1) :
    t.symm (σ (t i)) = 0 ∨ t.symm (σ (t i)) = 1 := by
  have hx : t i ∈ centralPair := by
    rcases hi with rfl | rfl <;> simp [ht, centralPair]
  have hm := (centralPair_invariant σ hσ _).mpr hx
  simp only [centralPair, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hm | hm
  · left
    rw [hm, ← ht.1]
    exact t.symm_apply_apply 0
  · right
    rw [hm, ← ht.2]
    exact t.symm_apply_apply 1

private theorem graphStabilizer_card_le_of_transporter (t : Equiv.Perm (Fin 2058))
    (ht : t ∈ preservingGroup) (himages : t 0 = 480 ∧ t 1 = 1444) :
    Nat.card graphStabilizer ≤ 18432 := by
  let e := MulAut.conj t⁻¹
  let K := graphStabilizer.map e.toMonoidHom
  have hK : K ≤ preservingGroup := by
    rintro _ ⟨σ, hσ, rfl⟩
    exact mul_mem (mul_mem (inv_mem ht) hσ.1) (inv_mem (inv_mem ht))
  have hp (σ : K) (i : Fin 2058) (hi : i = 0 ∨ i = 1) :
      σ.val i = 0 ∨ σ.val i = 1 := by
    obtain ⟨τ, hτ, he⟩ := σ.property
    rw [← he]
    change (t⁻¹ * τ * (t⁻¹)⁻¹) i = 0 ∨ (t⁻¹ * τ * (t⁻¹)⁻¹) i = 1
    rw [inv_inv]
    exact conjugated_pair t himages τ hτ i hi
  have hc : Nat.card K = Nat.card graphStabilizer := card_map_of_injective e.injective
  rw [← hc]
  exact reference_pair_card_le K hK hp

set_option maxRecDepth 4096 in
/-- The full graph stabilizer of the ten-point set has at most 18432 elements. -/
public theorem graphStabilizer_card_le : Nat.card graphStabilizer ≤ 18432 :=
  graphStabilizer_card_le_of_transporter (representation transporter)
    (Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup transporter.property)
    transporter_images

private theorem odd_mem_graphStabilizer :
    LocalPairs.SylowGeometry.Calculations.InnerNormalizer.GraphBound.oddPermutation ∈
      graphStabilizer := by
  refine ⟨LocalPairs.SylowGeometry.Calculations.InnerNormalizer.GraphBound.odd_mem.1, ?_⟩
  change ∀ x : Fin 2058,
    LocalPairs.SylowGeometry.Calculations.InnerNormalizer.GraphBound.oddPermutation x ∈
      fixedVertices ↔ x ∈ fixedVertices
  apply Held.TwoLocalCandidates.Cores.allLetters
  set_option maxRecDepth 8192 in
    decide +kernel

/-- Parity halves the preceding bound; the odd element is independently certified. -/
public theorem evenGraphStabilizer_card_le : Nat.card evenGraphStabilizer ≤ 9216 := by
  let E := evenGraphStabilizer.subgroupOf graphStabilizer
  have hproper : E ≠ ⊤ := by
    intro he
    have hm : (⟨_, odd_mem_graphStabilizer⟩ : graphStabilizer) ∈ E :=
      he ▸ Subgroup.mem_top _
    have hodd : Equiv.Perm.sign
        LocalPairs.SylowGeometry.Calculations.InnerNormalizer.GraphBound.oddPermutation ≠ 1 := by
      rw [LocalPairs.SylowGeometry.Calculations.InnerNormalizer.GraphBound.odd_sign]
      decide +kernel
    exact hodd hm.2
  have hi : 2 ≤ E.index := E.one_lt_index_of_ne_top hproper
  have he : Nat.card E = Nat.card evenGraphStabilizer :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show evenGraphStabilizer ≤ graphStabilizer from inf_le_left)).toEquiv
  have hb : Nat.card evenGraphStabilizer * 2 ≤ Nat.card graphStabilizer := by
    rw [← he, ← E.card_mul_index]
    exact Nat.mul_le_mul_left _ hi
  have hu := graphStabilizer_card_le
  omega

public theorem normalizer_card_le : Nat.card (normalizer (ambient 12 : Set He)) ≤ 9216 :=
  normalizer_card_le_evenGraphStabilizer.trans evenGraphStabilizer_card_le

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.Row12
