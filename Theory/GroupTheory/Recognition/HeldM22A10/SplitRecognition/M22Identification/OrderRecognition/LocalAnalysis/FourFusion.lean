module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysisData

/-!
# The two order-four classes, conditional on involution fusion

Conjugate the square of an element of order four to the marked involution.
The element then lies in its centralizer, and the Case II square roots of
`z 0` have exactly the two stated local classes. A small explicit set of
conjugators certifies this last finite computation. No involution fusion is
asserted here; its proof belongs to Janko's preceding ambient argument.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), 1–19, Section 5, p.9.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
namespace CaseII

local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
local instance : Fintype TwistedModel := Fintype.ofEquiv
  (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm
private def rootConjugator (r : Fin 2 × Fin 2 × Fin 6) : TwistedModel :=
  z 1 ^ r.1.val * z 3 ^ r.2.1.val * SemidirectProduct.inr
    (![1, Equiv.swap 1 2, Equiv.swap 1 2 * Equiv.swap 2 3,
      Equiv.swap 0 2 * Equiv.swap 1 2,
      Equiv.swap 0 2 * Equiv.swap 1 2 * Equiv.swap 2 3,
      Equiv.swap 0 2 * Equiv.swap 1 3] r.2.2)

/-- Every square root of the marked involution is locally conjugate to one
of the two source representatives. -/
public theorem model_four_roots : ∀ x : TwistedModel, x ^ 2 = z 0 →
    IsConj x (z 3 * a) ∨ IsConj x (z 1 * d) := by
  have h : ∀ x : TwistedModel, x ^ 2 = z 0 →
      ∃ r : Fin 2 × Fin 2 × Fin 6,
        rootConjugator r * x * (rootConjugator r)⁻¹ = z 3 * a ∨
        rootConjugator r * x * (rootConjugator r)⁻¹ = z 1 * d := by decide +kernel
  intro x hx
  obtain ⟨r, hr⟩ := h x hx
  exact hr.imp (fun h => isConj_iff.mpr ⟨_, h⟩) (fun h => isConj_iff.mpr ⟨_, h⟩)

universe u
variable {G : Type u} [Group G] [Finite G]

/-- Ambient involution fusion implies coverage by the two order-four classes. -/
public theorem four_fusion_of_involution_fusion (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer)
    (h2 : ∀ x : G, orderOf x = 2 → IsConj x D.z)
    (x : G) (hx : orderOf x = 4) :
    IsConj x (into D k (z 3 * a)) ∨ IsConj x (into D k (z 1 * d)) := by
  have hx2 : orderOf (x ^ 2) = 2 := by
    rw [orderOf_pow' x (by decide), hx]
    norm_num
  obtain ⟨g, hg⟩ := isConj_iff.mp (h2 _ hx2)
  let y := (MulAut.conj g) x
  have hy2 : y ^ 2 = D.z := by
    rw [show y ^ 2 = (MulAut.conj g) (x ^ 2) from (map_pow _ _ _).symm]
    exact hg
  have hyC : y ∈ D.centralizer := by
    apply mem_centralizer_singleton_iff.mpr
    rw [← hy2]
    simp [pow_two, mul_assoc]
  obtain ⟨v, hv⟩ := k.surjective ⟨y, hyC⟩
  have hvy : into D k v = y := congrArg Subtype.val hv
  have hv2 : v ^ 2 = z 0 := by
    apply into_injective D k
    rw [map_pow, hvy, into_z_zero D k]
    exact hy2
  have hxy : IsConj x (into D k v) := isConj_iff.mpr ⟨g, hvy.symm⟩
  rcases model_four_roots v hv2 with h | h
  · exact Or.inl (hxy.trans ((into D k).map_isConj h))
  · exact Or.inr (hxy.trans ((into D k).map_isConj h))

end CaseII
end Theory.GroupTheory.HeldM22A10.M22Identification
