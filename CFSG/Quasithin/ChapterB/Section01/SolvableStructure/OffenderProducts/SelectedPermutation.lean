module
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.NaturalModels

/-!
# Conjugation on a normal selected factor product

Independence detects membership of a factor in a selected product. When
that product is normal, ambient conjugation restricts to a permutation of
the selected indices, transporting the actual natural supports as well.
This proves the permutation clause needed in B.2.16(2), printed p.79.
-/

public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SolvableFFFactors
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (d : SolvableFFFactors ρ)

theorem factor_mem_selection_iff (I : Set (Fin d.count)) (j : Fin d.count) :
    d.factor j ≤ ⨆ i ∈ I, d.factor i ↔ j ∈ I := by
  constructor
  · intro h
    by_contra hj
    have hle : (⨆ i ∈ I, d.factor i) ≤ ⨆ i ≠ j, d.factor i :=
      iSup_le fun i => iSup_le fun hi => le_iSup_of_le i (le_iSup_of_le
        (fun he => hj (he ▸ hi)) le_rfl)
    have hd := (d.factors_independent j).mono_right hle
    have hz : d.factor j = ⊥ := hd.eq_bot_of_le h
    exact d.support_ne_bot j (by rw [hz]; simp [subspaceCommutator])
  · exact fun h => le_iSup_of_le j (le_iSup_of_le h le_rfl)

theorem selection_invariant (I : Set (Fin d.count))
    (hn : (⨆ i ∈ I, d.factor i : Subgroup G).Normal) (g : G) (i : Fin d.count) :
    d.factorConjugation g i ∈ I ↔ i ∈ I := by
  let L := (⨆ i ∈ I, d.factor i : Subgroup G)
  have h (g : G) {i : Fin d.count} (hi : i ∈ I) : d.factorConjugation g i ∈ I := by
    apply (d.factor_mem_selection_iff I _).mp
    rw [← d.factor_map_conj]
    rintro _ ⟨x,hx,rfl⟩
    exact hn.conj_mem x ((d.factor_mem_selection_iff I i).mpr hi hx) g
  constructor
  · intro hi
    simpa using h g⁻¹ hi
  · exact h g

noncomputable def selectedPermutation (I : Set (Fin d.count))
    (hn : (⨆ i ∈ I, d.factor i : Subgroup G).Normal) (g : G) : Equiv.Perm I where
  toFun i := ⟨d.factorConjugation g i,(d.selection_invariant I hn g i).mpr i.property⟩
  invFun i := ⟨d.factorConjugation g⁻¹ i,(d.selection_invariant I hn g⁻¹ i).mpr i.property⟩
  left_inv i := Subtype.ext (by simp)
  right_inv i := Subtype.ext (by simp)

@[simp] theorem selectedPermutation_apply (I : Set (Fin d.count))
    (hn : (⨆ i ∈ I, d.factor i : Subgroup G).Normal) (g : G) (i : I) :
    (d.selectedPermutation I hn g i).val = d.factorConjugation g i.val := by rfl

theorem support_map_conj (g : G) (i : Fin d.count) :
    (subspaceCommutator ρ ⊤ (d.factor i)).map (ρ g) =
      subspaceCommutator ρ ⊤ (d.factor (d.factorConjugation g i)) := by
  apply le_antisymm
  · rintro _ ⟨v,hv,rfl⟩
    exact d.action_mem_factor_support g i hv
  · intro v hv
    refine ⟨ρ g⁻¹ v,?_,?_⟩
    · simpa using d.action_mem_factor_support g⁻¹ (d.factorConjugation g i) hv
    · simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]
end CFSG.Quasithin.ChapterB.SolvableFFFactors
