module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne.FiniteConditions
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne.Normalization
public import Theory.SpecificGroups.Janko1.Model.Certification.InvolutionFusion
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.CyclicNormalOddQuotient

/-!
# Reducing the J₁ outer-group assertion to two finite matrix checks

Conjugation first normalizes the image of the order-three generator `b`.
The previously certified involution fusion and the finite family's closure then
place the image of `a` in that family. The two generator relations reduce its
possible images to the orbit of `a` under the centralizer of `b`. Generation
identifies the resulting automorphism with conjugation by an actual element.

The statements here are conditional on `OrbitClosed` and
`GeneratorImageRigid`. Their proofs are independent obligations; this module
does not claim the completed `Out(J₁) = 1` entry of GLS3, Table 5.3f.
Aschbacher–Smith uses that entry on printed pp.504 and 510.
-/

namespace Janko1.OuterCertificate

open OrderCertificate

private theorem a_inv_eq : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using a_pow_two)

private theorem b_inv_eq : b⁻¹ = b ^ 2 :=
  by
  apply inv_eq_of_mul_eq_one_right
  exact (pow_succ' b 2).symm.trans b_pow_three

private theorem image_a : matrixValue a = matrixA := rfl
private theorem image_b : matrixValue b = matrixB := rfl

/-- Generator closure and the already certified involution fusion cover every involution. -/
public theorem involution_mem_orbit (hc : OrbitClosed) (x : Model) (hx : orderOf x = 2) :
    ∃ i : Fin 1463, matrixValue x = orbitMatrix i := by
  let T : Set Model := {y | ∃ i : Fin 1463, matrixValue y = orbitMatrix i}
  have ha : a ∈ T := ⟨0, image_a.trans orbitMatrix_zero.symm⟩
  have hna : a ∈ Subgroup.normalizer T := by
    apply Subgroup.mem_normalizer_fintype
    rintro y ⟨i, hi⟩
    obtain ⟨j, hj⟩ := hc.1 i
    refine ⟨j, ?_⟩
    simpa only [map_mul, a_inv_eq, hi, image_a] using hj
  have hnb : b ∈ Subgroup.normalizer T := by
    apply Subgroup.mem_normalizer_fintype
    rintro y ⟨i, hi⟩
    obtain ⟨j, hj⟩ := hc.2 i
    refine ⟨j, ?_⟩
    simpa only [map_mul, b_inv_eq, map_pow, hi, pow_two, image_b] using hj
  have hn : Subgroup.normalizer T = ⊤ := by
    apply top_unique
    rw [← closure_pair_eq_top]
    apply (Subgroup.closure_le _).mpr
    rintro y (rfl | hy)
    · exact hna
    · exact Set.mem_singleton_iff.mp hy ▸ hnb
  obtain ⟨g, hg⟩ := involution_fusion_of_card card_model x hx
  have hgN : g ∈ Subgroup.normalizer T := by rw [hn]; trivial
  apply (Subgroup.mem_set_normalizer_iff.mp hgN x).mpr
  simpa only [hg] using ha

/-- Fixing `b` reduces an automorphism to the two finite matrix checks. -/
public theorem aut_fixing_b_inner (hc : OrbitClosed) (hr : GeneratorImageRigid)
    (f : MulAut Model) (hf : f b = b) : ∃ g : Model, MulAut.conj g = f := by
  obtain ⟨i, hi⟩ := involution_mem_orbit hc (f a) ((f.orderOf_eq a).trans orderOf_a)
  have h7 : (orbitMatrix i * matrixB) ^ 7 = 1 := by
    have h := congrArg (matrixValue ∘ f) ab_pow_seven
    simpa only [Function.comp_apply, map_pow, map_mul, map_one, hf, hi, image_b] using h
  have h19 : (orbitMatrix i * matrixB * orbitMatrix i * matrixB ^ 2) ^ 19 = 1 := by
    have h := congrArg (matrixValue ∘ f) abab_sq_pow_nineteen
    simpa only [Function.comp_apply, map_pow, map_mul, map_one, hf, hi, image_b] using h
  obtain ⟨g, hga, hgb⟩ := hr i h7 h19
  refine ⟨g, ?_⟩
  apply MulEquiv.toMonoidHom_injective
  apply hom_ext
  · exact matrixValue_injective (hga.trans hi.symm)
  · exact hgb.trans hf.symm

/-- The certified finite checks imply that every automorphism is inner. -/
public theorem aut_inner_of_matrix_certificates (hc : OrbitClosed) (hr : GeneratorImageRigid)
    (f : MulAut Model) : ∃ g : Model, MulAut.conj g = f := by
  obtain ⟨g, hg⟩ := order_three_fusion (f b) ((f.orderOf_eq b).trans orderOf_b)
  let f' : MulAut Model := MulAut.conj g * f
  have hf' : f' b = b := hg
  obtain ⟨h, hh⟩ := aut_fixing_b_inner hc hr f' hf'
  refine ⟨g⁻¹ * h, ?_⟩
  rw [map_mul, map_inv, hh]
  exact inv_mul_cancel_left _ _

/-- The actual outer quotient is trivial once the two matrix checks are supplied. -/
public theorem outer_subsingleton_of_matrix_certificates
    (hc : OrbitClosed) (hr : GeneratorImageRigid) : Subsingleton (MulAut.Outer Model) := by
  have hi : MulAut.innerSubgroup Model = ⊤ :=
    MonoidHom.range_eq_top.mpr (aut_inner_of_matrix_certificates hc hr)
  change Subsingleton (MulAut Model ⧸ MulAut.innerSubgroup Model)
  rw [hi]
  exact QuotientGroup.subsingleton_quotient_top

end Janko1.OuterCertificate
