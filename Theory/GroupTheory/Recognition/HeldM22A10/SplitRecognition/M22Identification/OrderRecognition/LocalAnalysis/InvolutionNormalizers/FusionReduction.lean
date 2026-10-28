module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.Contracts
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.Elementary
public import Theory.GroupTheory.InvolutionFusionFromCentralizer
/-!
# Reduction of ambient involution fusion to five coordinates

A kernel-checked cover by 24 explicit conjugators reduces every involution
of the centralizer model to one of `z 0`, `z 1`, `z 2`, `a`, `d`.
Fusion of these representatives in the ambient group suffices: conjugate
an arbitrary involution into a Sylow two-subgroup and use a central
involution there to reduce to the distinguished centralizer.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, p.4; the ambient reduction is the general
lemma in `Theory.GroupTheory.InvolutionFusionFromCentralizer`.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
open LocalModelDichotomy
local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
local instance : Fintype TwistedModel := Fintype.ofEquiv
  (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm
private def involutionConjugator (r : Fin 24) : TwistedModel :=
  ![SemidirectProduct.inl (Multiplicative.ofAdd ![0, 0, 0, 0]) * SemidirectProduct.inr (1),
    SemidirectProduct.inl (Multiplicative.ofAdd ![0, 0, 0, 0]) * SemidirectProduct.inr (Equiv.swap 1 2),
    SemidirectProduct.inl (Multiplicative.ofAdd ![0, 0, 0, 0]) * SemidirectProduct.inr (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3),
    SemidirectProduct.inl (Multiplicative.ofAdd ![1, 0, 0, 0]) * SemidirectProduct.inr (Equiv.swap 0 2 * Equiv.swap 1 2),
    SemidirectProduct.inl (Multiplicative.ofAdd ![1, 0, 0, 0]) * SemidirectProduct.inr (Equiv.swap 0 2 * Equiv.swap 1 2 * Equiv.swap 2 3),
    SemidirectProduct.inl (Multiplicative.ofAdd ![1, 0, 0, 0]) * SemidirectProduct.inr (Equiv.swap 0 2 * Equiv.swap 1 3),
    SemidirectProduct.inl (Multiplicative.ofAdd ![1, 0, 0, 0]) * SemidirectProduct.inr (Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 2 3),
    SemidirectProduct.inl (Multiplicative.ofAdd ![1, 0, 0, 0]) * SemidirectProduct.inr (Equiv.swap 0 1 * Equiv.swap 1 3),
    SemidirectProduct.inl (Multiplicative.ofAdd ![1, 0, 0, 0]) * SemidirectProduct.inr (1),
    SemidirectProduct.inl (Multiplicative.ofAdd ![1, 0, 1, 0]) * SemidirectProduct.inr (1),
    SemidirectProduct.inl (Multiplicative.ofAdd ![1, 0, 1, 0]) * SemidirectProduct.inr (Equiv.swap 1 2),
    SemidirectProduct.inl (Multiplicative.ofAdd ![1, 0, 1, 0]) * SemidirectProduct.inr (Equiv.swap 1 2 * Equiv.swap 2 3),
    SemidirectProduct.inl (Multiplicative.ofAdd ![0, 0, 0, 0]) * SemidirectProduct.inr (Equiv.swap 0 2 * Equiv.swap 1 2),
    SemidirectProduct.inl (Multiplicative.ofAdd ![0, 0, 0, 0]) * SemidirectProduct.inr (Equiv.swap 0 2 * Equiv.swap 1 2 * Equiv.swap 2 3),
    SemidirectProduct.inl (Multiplicative.ofAdd ![0, 0, 0, 0]) * SemidirectProduct.inr (Equiv.swap 0 2 * Equiv.swap 1 3),
    SemidirectProduct.inl (Multiplicative.ofAdd ![0, 0, 1, 0]) * SemidirectProduct.inr (1),
    SemidirectProduct.inl (Multiplicative.ofAdd ![0, 0, 1, 0]) * SemidirectProduct.inr (Equiv.swap 1 2),
    SemidirectProduct.inl (Multiplicative.ofAdd ![0, 0, 1, 0]) * SemidirectProduct.inr (Equiv.swap 1 2 * Equiv.swap 2 3),
    SemidirectProduct.inl (Multiplicative.ofAdd ![0, 0, 1, 0]) * SemidirectProduct.inr (Equiv.swap 0 2 * Equiv.swap 1 2),
    SemidirectProduct.inl (Multiplicative.ofAdd ![0, 0, 1, 0]) * SemidirectProduct.inr (Equiv.swap 0 2 * Equiv.swap 1 2 * Equiv.swap 2 3),
    SemidirectProduct.inl (Multiplicative.ofAdd ![0, 0, 1, 0]) * SemidirectProduct.inr (Equiv.swap 0 2 * Equiv.swap 1 3),
    SemidirectProduct.inl (Multiplicative.ofAdd ![1, 0, 1, 0]) * SemidirectProduct.inr (Equiv.swap 0 2 * Equiv.swap 1 2),
    SemidirectProduct.inl (Multiplicative.ofAdd ![1, 0, 1, 0]) * SemidirectProduct.inr (Equiv.swap 0 2 * Equiv.swap 1 2 * Equiv.swap 2 3),
    SemidirectProduct.inl (Multiplicative.ofAdd ![1, 0, 1, 0]) * SemidirectProduct.inr (Equiv.swap 0 2 * Equiv.swap 1 3)] r

/-- Every coordinate involution belongs to one of the five source classes. -/
public theorem model_involution_classes (x : TwistedModel) (hx : orderOf x = 2) :
    IsConj x (z 0) ∨ IsConj x (z 1) ∨ IsConj x (z 2) ∨ IsConj x a ∨ IsConj x d := by
  have h : ∀ x : TwistedModel, x ^ 2 = 1 → x ≠ 1 →
      ∃ r : Fin 24,
        involutionConjugator r * x * (involutionConjugator r)⁻¹ = z 0 ∨
        involutionConjugator r * x * (involutionConjugator r)⁻¹ = z 1 ∨
        involutionConjugator r * x * (involutionConjugator r)⁻¹ = z 2 ∨
        involutionConjugator r * x * (involutionConjugator r)⁻¹ = a ∨
        involutionConjugator r * x * (involutionConjugator r)⁻¹ = d := by decide +kernel
  have hx2 : x ^ 2 = 1 := by simpa only [hx] using pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by intro he; simp [he] at hx
  obtain ⟨r, hr⟩ := h x hx2 hx1
  rcases hr with h | h | h | h | h
  · exact Or.inl (isConj_iff.mpr ⟨_,h⟩)
  · exact Or.inr (Or.inl (isConj_iff.mpr ⟨_,h⟩))
  · exact Or.inr (Or.inr (Or.inl (isConj_iff.mpr ⟨_,h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (isConj_iff.mpr ⟨_,h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (isConj_iff.mpr ⟨_,h⟩))))

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- Fusion of the four remaining representatives implies ambient involution fusion. -/
public theorem involution_fusion_of_representatives
    (hz1 : IsConj (into D k (z 1)) D.z)
    (hz2 : IsConj (into D k (z 2)) D.z)
    (ha : IsConj (into D k a) D.z) (hd : IsConj (into D k d) D.z)
    (x : G) (hx : orderOf x = 2) : IsConj x D.z := by
  apply Theory.GroupTheory.isConj_of_involution_of_centralizer_fusion D.z_order ?_ hx
  intro y hy hc
  have hyC : y ∈ D.centralizer := mem_centralizer_singleton_iff.mpr hc.eq
  let v := k.symm ⟨y, hyC⟩
  have hv : into D k v = y := congrArg Subtype.val (k.apply_symm_apply ⟨y,hyC⟩)
  have hv2 : orderOf v = 2 := by
    rw [← orderOf_injective (into D k) (into_injective D k), hv, hy]
  rcases model_involution_classes v hv2 with h | h | h | h | h
  · simpa only [hv, into_z_zero D k] using (into D k).map_isConj h
  · simpa only [hv] using ((into D k).map_isConj h).trans hz1
  · simpa only [hv] using ((into D k).map_isConj h).trans hz2
  · simpa only [hv] using ((into D k).map_isConj h).trans ha
  · simpa only [hv] using ((into D k).map_isConj h).trans hd

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
