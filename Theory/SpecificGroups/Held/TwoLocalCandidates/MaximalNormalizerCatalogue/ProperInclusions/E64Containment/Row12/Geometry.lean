module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ElementaryWords
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralWord
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.WordTests
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.TwoGroup.Tables
public import Theory.SpecificGroups.Held.Model.Perfect

/-!
# The ten common fixed vertices of Held catalogue row 12

The four literal generators fix exactly the displayed ten vertices. This is
checked using the previously certified permutation tables, and closure gives
the common fixed set of the actual ambient subgroup. Every element of its
normalizer therefore preserves this set. Graph preservation and perfectness
embed that normalizer in the even graph stabilizer defined below.

Source: the unchanged ATLAS degree-2058 action and catalogue words;
GLS3 Table 5.3p. This is one finite reduction toward condition E of
Aschbacher–Smith, printed pp.3–4 and 481–482, not a classification of two-locals.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.Row12
open Subgroup LocalPairs.SylowGeometry.Calculations
open LocalPairs.SylowGeometry.Calculations.TwoGroup.Tables

/-- The literal ten-point configuration attached to catalogue row 12. -/
@[expose] public def fixedVertices : Finset (Fin 2058) :=
  {480, 557, 719, 892, 944, 1016, 1444, 1672, 1877, 1937}

@[expose] public def tableGen : Fin 4 → Equiv.Perm (Fin 2058)
  | 0 => g0
  | 1 => g1
  | 2 => g2
  | 3 => g3

@[expose] public def tableWord (w : List ℤ) : Equiv.Perm (Fin 2058) :=
  (w.map (fun k => if k < 0 then (tableGen (Fin.ofNat 4 (k.natAbs - 1)))⁻¹
    else tableGen (Fin.ofNat 4 (k.natAbs - 1)))).prod

public theorem tableGen_eq (i : Fin 4) : tableGen i = representation (generator i) := by
  fin_cases i
  · exact g0_eq
  · exact g1_eq
  · exact g2_eq
  · exact g3_eq

public theorem tableWord_eq (w : List ℤ) : tableWord w = representation (word w : He) := by
  change tableWord w = (representation.comp representative.subtype) (word w)
  simp only [tableWord, word, map_list_prod, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro n _
  simp only [letter]
  split_ifs <;> simp only [map_inv, MonoidHom.coe_comp, Function.comp_apply,
    tableGen_eq] <;> rfl

set_option maxRecDepth 8192 in
private theorem fixedVertices_check : ∀ x : Fin 2058,
    x ∈ fixedVertices ↔ ∀ w ∈ generatorWords 12, tableWord w x = x := by
  apply Held.TwoLocalCandidates.Cores.allLetters
  decide +kernel

/-- The displayed configuration is exactly the common fixed set, with no
assumption about the subgroup order or elementary abelianness. -/
public theorem mem_fixedVertices_iff (x : Fin 2058) :
    x ∈ fixedVertices ↔ ∀ g ∈ ambient 12, representation g x = x := by
  have hw : x ∈ fixedVertices ↔
      ∀ w ∈ generatorWords 12, representation (word w : He) x = x := by
    simpa only [tableWord_eq] using fixedVertices_check x
  exact hw.trans (ProperInclusions.ambient_le_iff 12 (MulAction.stabilizer He x)).symm

/-- All permutations preserving the ten-point set. -/
@[expose] public def setwiseGroup : Subgroup (Equiv.Perm (Fin 2058)) where
  carrier := {σ | ∀ x, σ x ∈ fixedVertices ↔ x ∈ fixedVertices}
  one_mem' := by intro x; rfl
  mul_mem' := by
    intro σ τ hσ hτ x
    exact (hσ (τ x)).trans (hτ x)
  inv_mem' := by
    intro σ hσ x
    change σ.symm x ∈ fixedVertices ↔ x ∈ fixedVertices
    simpa only [Equiv.apply_symm_apply] using (hσ (σ.symm x)).symm

/-- The full graph stabilizer, without an ambient Held-membership restriction. -/
@[expose] public def graphStabilizer : Subgroup (Equiv.Perm (Fin 2058)) :=
  NormalizerGraph.preservingGroup ⊓ setwiseGroup

/-- Its even subgroup. -/
@[expose] public def evenGraphStabilizer : Subgroup (Equiv.Perm (Fin 2058)) :=
  graphStabilizer ⊓ Equiv.Perm.sign.ker

private theorem normalizer_maps_fixedVertices (g : He)
    (hg : g ∈ normalizer (ambient 12 : Set He)) (x : Fin 2058)
    (hx : x ∈ fixedVertices) : representation g x ∈ fixedVertices := by
  rw [mem_fixedVertices_iff] at hx ⊢
  intro a ha
  have hc : g⁻¹ * a * g ∈ ambient 12 := by
    apply (hg (g⁻¹ * a * g)).mpr
    simpa only [SetLike.mem_coe, mul_assoc, mul_inv_cancel, mul_one,
      mul_inv_cancel_left] using ha
  have hf := hx _ hc
  change a • (g • x) = g • x
  calc
    a • (g • x) = g • ((g⁻¹ * a * g) • x) := by
      simp only [mul_smul, smul_inv_smul]
    _ = g • x := congrArg (g • ·) hf

/-- Arbitrary elements of the actual normalizer preserve the configuration. -/
public theorem normalizer_mem_setwiseGroup (g : He)
    (hg : g ∈ normalizer (ambient 12 : Set He)) : representation g ∈ setwiseGroup := by
  intro x
  constructor
  · intro hx
    have h := normalizer_maps_fixedVertices g⁻¹ (inv_mem hg) (representation g x) hx
    change g⁻¹ • (g • x) ∈ fixedVertices at h
    simpa only [inv_smul_smul] using h
  · exact normalizer_maps_fixedVertices g hg x

set_option maxRecDepth 4096 in
/-- No simplicity, Sylow or global Held order assertion is needed for this embedding. -/
public theorem normalizer_mem_evenGraphStabilizer (g : He)
    (hg : g ∈ normalizer (ambient 12 : Set He)) :
    representation g ∈ evenGraphStabilizer := by
  refine ⟨⟨?_, normalizer_mem_setwiseGroup g hg⟩, ?_⟩
  · exact Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup g.property
  · exact hom_to_commGroup_trivial (Equiv.Perm.sign.comp representation) g

public theorem normalizer_card_le_evenGraphStabilizer :
    Nat.card (normalizer (ambient 12 : Set He)) ≤ Nat.card evenGraphStabilizer := by
  apply Nat.card_le_card_of_injective
    (fun g : normalizer (ambient 12 : Set He) =>
      (⟨representation g.val, normalizer_mem_evenGraphStabilizer g.val g.property⟩ :
        evenGraphStabilizer))
  intro g h he
  apply Subtype.ext
  apply representation_injective
  exact congrArg (fun z : evenGraphStabilizer => z.val) he

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.Row12
