module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates

/-!
# A large elementary two-subgroup in the actual J₄ model

The certified 2¹¹ kernel in the fixed maximal-local word subgroup is
mapped into J₄ by the literal subgroup inclusion. Its elementary structure
and cardinality are preserved by this injection. No ambient order or
simplicity theorem for J₄ is needed.

Source: the ATLAS J4G1-max1W1 certificates reused in
`Janko4.Model.LocalStructure.Mathieu`, and GLS3 Table 5.3i.
Application: Aschbacher–Smith, E2(iii), p.1170, and Lemma 16.4.5, p.1184.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.EvenParameter
open Subgroup

/-- The explicit local binary kernel supplies a subgroup of order greater than four. -/
theorem janko4_large_elementary :
    ∃ E : Subgroup Janko4.Model, IsElementaryAbelian 2 E ∧ 4 < Nat.card E := by
  let K := Janko4.Cardinality.localKernel Janko4.matrixA_mul_self Janko4.matrixB_pow_four
  let M := Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four
  let _ : IsElementaryAbelian 2 K := Janko4.LocalStructure.localKernel_elementary _ _
  refine ⟨K.map M.subtype, IsElementaryAbelian.map M.subtype, ?_⟩
  rw [Nat.card_congr (K.equivMapOfInjective M.subtype M.subtype_injective).symm.toEquiv]
  have h := Janko4.Cardinality.localKernel_card Janko4.matrixA_mul_self Janko4.matrixB_pow_four
  change 4 < Nat.card K
  change Nat.card K = 2048 at h
  omega

/-- Transport the witness through the actual E2 carrier equivalence. -/
theorem janko4_model_large_elementary {S : Type*} [Group S]
    (h : Nonempty (S ≃* Janko4.Model)) :
    ∃ E : Subgroup S, IsElementaryAbelian 2 E ∧ 4 < Nat.card E := by
  obtain ⟨e⟩ := h
  obtain ⟨E, hE, hc⟩ := janko4_large_elementary
  let _ := hE
  refine ⟨E.map e.symm.toMonoidHom, IsElementaryAbelian.map _, ?_⟩
  rwa [← Nat.card_congr (E.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).toEquiv]

end CFSG.Quasithin.Chapter16.Intersections.EvenParameter
