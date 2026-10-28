module
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.HermitianTensorThree.UnipotentRadicals
public import Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer
public import Theory.Representation.HermitianTensorThree.ImageOuter.OuterRank
public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.InvolutionConjugacy
import all Theory.Representation.HermitianTensorThree.UnipotentRadicals

/-!
# Involution codimensions in the Hermitian tensor normalizer

Sylow conjugacy places an inner involution in the faithful unitriangular
image. Its lift is an involution, so the concrete SL₃ root conjugacy puts
it in the class of the marked highest root. The existing root calculation
therefore gives codimension 4n for every inner involution. The proved outer
conjugacy and field-involution calculation give codimension 3n outside the
component. Both statements retain n = 1 and apply to each literal overgroup.

The implementation import reuses the internal Sylow conjugator from
UnipotentRadicals without changing that module's public boundary. The
Chapter 12 HermitianInitialBounds consumer applies the dichotomy to the
original automizer, then derives its local minimum and initial global bounds.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the dimension
clauses of H.4.4(2,6) and Table 7.2.1, printed pp.381,698
(refs/quasithin.pdf).
-/

open scoped Classical
open Subgroup Representation Representation.BinaryOffender
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
public noncomputable section
namespace Representation.HermitianTensorThree.Involutions
variable (n : ℕ) [NeZero n]

/-- The marked root survives as an involution in the actual action image. -/
theorem orderOf_root_image : orderOf (binaryActionHom n (root n)) = 2 := by
  apply orderOf_eq_prime
  · rw [← map_pow,root_sq,map_one]
  · intro he
    have hh : UnipotentRadicals.unipotentHom n
        (⟨0,0,1⟩ : Matrix.PSL3Even.UnipotentGeometry.U (E n)) = 1 := he
    have hu := UnipotentRadicals.unipotentHom_injective n (hh.trans (map_one _).symm)
    exact one_ne_zero (congrArg Matrix.PSL3Even.UnipotentGeometry.U.c hu)

/-- Every inner involution has a conjugator in the original special-linear cover. -/
theorem inner_conjugate_root
    (i : Space n ≃ₗ[ZMod 2] Space n) (hiL : i ∈ binaryImage n)
    (hi2 : orderOf i = 2) :
    ∃ c : Cover n, MulAut.conj (binaryActionHom n c) i = binaryActionHom n (root n) := by
  have hi : i ^ 2 = 1 := (orderOf_eq_prime_iff.mp hi2).1
  have hi1 : i ≠ 1 := (orderOf_eq_prime_iff.mp hi2).2
  let P := zpowers i
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.zpowers_of_pow_eq_one hi
  obtain ⟨c,hc⟩ := UnipotentRadicals.two_subgroup_conjugate_le_unipotent n P
    (IsElementaryAbelian.isPGroup 2 P) (zpowers_le.mpr hiL)
  obtain ⟨u,hu⟩ := hc (mem_map_of_mem (MulAut.conj (binaryActionHom n c)).toMonoidHom
    (mem_zpowers i))
  change UnipotentRadicals.unipotentHom n u = MulAut.conj (binaryActionHom n c) i at hu
  have hu1 : u ≠ 1 := by
    intro he
    rw [he,map_one] at hu
    exact hi1 ((MulAut.conj (binaryActionHom n c)).injective (hu.symm.trans (map_one _).symm))
  have hu2 : u ^ 2 = 1 := by
    apply UnipotentRadicals.unipotentHom_injective n
    rw [map_pow,map_one,hu,← map_pow,hi,map_one]
  obtain ⟨d,hd⟩ := isConj_iff.mp
    (Matrix.PSL3.EvenInnerCentralizers.specialLinear_isConj_root (E n) u hu1 hu2)
  have hd' : MulAut.conj (binaryActionHom n d) (UnipotentRadicals.unipotentHom n u) =
      binaryActionHom n (root n) := by
    have he := congrArg (binaryActionHom n) hd
    have hr : Matrix.PSL3.EvenInnerCentralizers.rootSL (E n) = root n := rfl
    rw [map_mul,map_mul,map_inv,hr] at he
    exact he
  refine ⟨d*c, ?_⟩
  rw [map_mul, map_mul, MulAut.mul_apply, ← hu]
  exact hd'

private theorem fixedCodim_conjugate (i c : Space n ≃ₗ[ZMod 2] Space n) :
    fixedCodim (UnipotentRadicals.ambientAction n) (zpowers (MulAut.conj c i)) =
      fixedCodim (UnipotentRadicals.ambientAction n) (zpowers i) := by
  have h := fixedCodim_map_conj (UnipotentRadicals.ambientAction n) (zpowers i) c
  rw [MonoidHom.map_zpowers] at h
  exact h

/-- Inner involutions have the root fixed codimension, including at n = 1. -/
theorem inner_fixedCodim
    (i : Space n ≃ₗ[ZMod 2] Space n) (hiL : i ∈ binaryImage n)
    (hi2 : orderOf i = 2) :
    fixedCodim (UnipotentRadicals.ambientAction n) (zpowers i) = 4*n := by
  obtain ⟨c,hc⟩ := inner_conjugate_root n i hiL hi2
  rw [← fixedCodim_conjugate n i (binaryActionHom n c),hc,
    fixedCodim_zpowers_eq_displacement_rank]
  exact finrank_binaryRootMoved n

/-- Outer normalizer involutions have the field-involution fixed codimension. -/
theorem outer_fixedCodim
    (i : Space n ≃ₗ[ZMod 2] Space n) (hiN : i ∈ binaryNormalizer n)
    (hiL : i ∉ binaryImage n) (hi2 : orderOf i = 2) :
    fixedCodim (UnipotentRadicals.ambientAction n) (zpowers i) = 3*n := by
  obtain ⟨c,_,hc⟩ := OuterRank.outer_involution_conjugate n (normalizerCoverage n)
    i hiN hi2 hiL
  rw [← fixedCodim_conjugate n i c,hc,fixedCodim_zpowers_eq_displacement_rank]
  exact finrank_binaryFieldMoved n

/-- Exact involution codimensions for the literal action of any normalizer subgroup. -/
theorem overgroup_involution_fixedCodim
    (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (hM : M ≤ binaryNormalizer n)
    (i : M) (hi2 : orderOf i = 2) :
    fixedCodim (overgroupAction n M) (zpowers i) =
      if i.val ∈ binaryImage n then 4*n else 3*n := by
  classical
  have hio : orderOf i.val = 2 := (orderOf_injective M.subtype M.subtype_injective i).trans hi2
  have he := fixedCodim_map_equivariant (overgroupAction n M)
    (UnipotentRadicals.ambientAction n) M.subtype (LinearEquiv.refl (ZMod 2) (Space n))
    (fun _ _ => rfl) (zpowers i)
  rw [MonoidHom.map_zpowers] at he
  rw [he]
  split_ifs with hiL
  · exact inner_fixedCodim n i.val hiL hio
  · exact outer_fixedCodim n i.val (hM i.property) hiL hio

end Representation.HermitianTensorThree.Involutions
