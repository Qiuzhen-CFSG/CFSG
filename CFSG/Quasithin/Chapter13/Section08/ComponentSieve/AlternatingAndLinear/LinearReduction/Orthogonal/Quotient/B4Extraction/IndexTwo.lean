module

public import Theory.Representation.Clifford
public import Mathlib.GroupTheory.Index

open Representation

/-!
# The reducible restriction in the orthogonal quotient argument

An irreducible module restricted to a normal subgroup of index two is either
irreducible or a sum of two irreducible submodules interchanged by an element
outside that subgroup. We construct the actual submodules and both exchange
identities: an atom and its conjugate span the module by Clifford theory,
and index two leaves at most these two conjugates.

This is the restriction step needed before applying B.4 in Aschbacher–Smith,
combined manuscript (1 March 2004), proof of 13.8.25, printed pp.959–960.
The proof uses the conjugate-span part of Isaacs, Character Theory, Theorem 6.5.
No classification of the two summands is asserted here.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient.B4Extraction

variable {F H U : Type*} [Field F] [Group H] [AddCommGroup U] [Module F U]
  (ρ : Representation F H U) (K : Subgroup H) [K.Normal]

private theorem conjugate_eq_of_mem (I : Subrepresentation (ρ.comp K.subtype))
    {k : H} (hk : k ∈ K) : conjugateSubrepresentationOrderIso ρ K k I = I := by
  apply Subrepresentation.toSubmodule_injective
  rw [conjugateSubrepresentationOrderIso_toSubmodule]
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact I.apply_mem_toSubmodule ⟨k, hk⟩ hv
  · intro v hv
    refine ⟨ρ k⁻¹ v, I.apply_mem_toSubmodule ⟨k⁻¹, K.inv_mem hk⟩ hv, ?_⟩
    simp [← Module.End.mul_apply, ← map_mul]

/-- The two actual summands of a reducible index-two restriction. -/
structure RestrictionSplit where
  left : Subrepresentation (ρ.comp K.subtype)
  right : Subrepresentation (ρ.comp K.subtype)
  left_atom : IsAtom left
  right_atom : IsAtom right
  complementary : IsCompl left right
  swapper : H
  outside : swapper ∉ K
  map_left : left.toSubmodule.map (ρ swapper) = right.toSubmodule
  map_right : right.toSubmodule.map (ρ swapper) = left.toSubmodule

theorem exists_restrictionSplit [FiniteDimensional F U]
    (hindex : K.index = 2) (hi : ρ.IsIrreducible)
    (hr : ¬ IsIrreducible (ρ.comp K.subtype)) : Nonempty (RestrictionSplit ρ K) := by
  classical
  let : ρ.IsIrreducible := hi
  let : Nontrivial U := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨I, hIirr⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (ρ.comp K.subtype)
  have hI : IsAtom I := (Subrepresentation.irreducible_iff_isAtom I).mp hIirr
  have hItop : I ≠ ⊤ := by
    intro he
    apply hr
    exact isSimpleOrder_iff_isAtom_top.mpr (he ▸ hI)
  obtain ⟨t, ht, _⟩ := K.index_eq_two_iff_exists_notMem_and.mp hindex
  let J := conjugateSubrepresentationOrderIso ρ K t I
  have hJ : IsAtom J := ((conjugateSubrepresentationOrderIso ρ K t).isAtom_iff I).mpr hI
  have htop : I ⊔ J = ⊤ := by
    apply top_unique
    rw [← iSup_conjugateSubrepresentations_eq_top ρ K hi I hIirr]
    refine iSup_le fun g => ?_
    rw [show conjugateSubrepresentation ρ K I g =
      conjugateSubrepresentationOrderIso ρ K g⁻¹ I by simp]
    by_cases hg : g⁻¹ ∈ K
    · rw [conjugate_eq_of_mem ρ K I hg]
      exact le_sup_left
    · have hm : t⁻¹ * g⁻¹ ∈ K :=
        (K.mul_mem_iff_of_index_two hindex).mpr
          (iff_of_false (by simpa using ht) hg)
      have he : conjugateSubrepresentationOrderIso ρ K g⁻¹ I = J := by
        have hh := conjugateSubrepresentationOrderIso_mul ρ K t (t⁻¹ * g⁻¹) I
        rw [conjugate_eq_of_mem ρ K I hm] at hh
        simpa only [mul_inv_cancel_left] using hh
      rw [he]
      exact le_sup_right
  have hne : I ≠ J := by
    intro he
    exact hItop (by simpa only [← he, sup_idem] using htop)
  refine ⟨⟨I, J, hI, hJ, ⟨hI.disjoint_of_ne hJ hne, codisjoint_iff.mpr htop⟩,
    t, ht, ?_, ?_⟩⟩
  · exact (conjugateSubrepresentationOrderIso_toSubmodule ρ K t I).symm
  · rw [← conjugateSubrepresentationOrderIso_toSubmodule]
    change (conjugateSubrepresentationOrderIso ρ K t
      (conjugateSubrepresentationOrderIso ρ K t I)).toSubmodule = I.toSubmodule
    rw [← conjugateSubrepresentationOrderIso_mul,
      conjugate_eq_of_mem ρ K I (K.mul_self_mem_of_index_two hindex t)]

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient.B4Extraction
