module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.ToddTwist
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.CentralTwist
public import Theory.Representation.MathieuCodeRestriction.FixedSpaces

/-!
# The source plane and point twists are outer

The odd full-word automorphism fixes the embedded cocode and the actual
native 23-cycle fixing its singleton. Faithfulness forces an inner
conjugator into the cocode; the vanishing 23-cycle norm then forces it to
be trivial. This proves the Todd twist is outer without assuming H¹.
Transport gives the same result in the original marked point group.

The plane twist fixes Q pointwise. Self-centralization of Q forces any
inner conjugator into Z(Q)=Z(H), contradicting its nonidentity. These
are the alpha and beta constructions used in AS91 (8.2), pp.605–606.
The full automorphism group of their common intersection still requires
the source module and normalizer analysis.
-/

public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup LocalGeometry LocalGeometry.LocalSubgroups Sporadic.Mathieu MathieuCode
open scoped BigOperators

private theorem toddOddCocycle_cycle : toddCocycle toddOddWord cycle23 = 0 := by
  apply toddCocycle_of_fixed_word
  ext i
  fin_cases i <;> decide +kernel

private theorem toddOddTwist_cycle :
    toddTwist toddOddWord (SemidirectProduct.inr cycle23) = SemidirectProduct.inr cycle23 := by
  rw [toddTwist_apply]
  apply SemidirectProduct.ext
  · change (1 : ToddVector)*Multiplicative.ofAdd (toddCocycle toddOddWord cycle23) = 1
    rw [toddOddCocycle_cycle]
    rfl
  · rfl

private theorem cocode_fixed_cycle (v : Cocode) (hv : cocodeRepresentation cycle23 v = v) : v = 0 := by
  have hp : ∀ n : ℕ, cocodeRepresentation (cycle23^n) v = v := by
    intro n
    induction n with
    | zero => rw [pow_zero,map_one]; rfl
    | succ n ih => rw [pow_succ,map_mul,Module.End.mul_apply,hv,ih]
  have hs := cocode_sum_cycle v
  simp only [hp,Finset.sum_const,Finset.card_univ,Fintype.card_fin] at hs
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2)] at hs
  have h23 : (23 : ZMod 2) = 1 := by decide
  change (23 : ZMod 2) • v = 0 at hs
  rwa [h23,one_smul] at hs

/-- A full-word automorphism that fixes the cocode pointwise can be inner
only through an element of the cocode itself. -/
private theorem toddInner_fixer_right (w : Full) (x : ToddGroup)
    (hx : toddTwist w = MulAut.conj x) : x.right = 1 := by
  apply cocode_faithful
  apply LinearMap.ext
  intro v
  have he : x * SemidirectProduct.inl (Multiplicative.ofAdd v) * x⁻¹ =
      SemidirectProduct.inl (Multiplicative.ofAdd v) := by
    rw [← MulAut.conj_apply,← hx,toddTwist_vector]
  have hh := congrArg SemidirectProduct.left (mul_inv_eq_iff_eq_mul.mp he)
  change x.left*toddAction x.right (Multiplicative.ofAdd v) =
    Multiplicative.ofAdd v*toddAction 1 x.left at hh
  rw [map_one,MulAut.one_apply,mul_comm (Multiplicative.ofAdd v)] at hh
  rw [map_one]
  change cocodeRepresentation x.right v = v
  exact congrArg Multiplicative.toAdd (mul_left_cancel hh)

/-- The odd full-word automorphism is outer, proved with the actual 23-cycle
and its vanishing cocode norm. -/
theorem toddOddTwist_not_inner : ¬ ∃ x : ToddGroup, toddTwist toddOddWord = MulAut.conj x := by
  rintro ⟨x,hx⟩
  have hr := toddInner_fixer_right toddOddWord x hx
  have hc : x*SemidirectProduct.inr cycle23*x⁻¹ = SemidirectProduct.inr cycle23 := by
    rw [← MulAut.conj_apply,← hx,toddOddTwist_cycle]
  have hh := congrArg SemidirectProduct.left (mul_inv_eq_iff_eq_mul.mp hc)
  change x.left*toddAction x.right 1 = 1*toddAction cycle23 x.left at hh
  rw [map_one,mul_one,one_mul] at hh
  have hv : x.left.toAdd = 0 := cocode_fixed_cycle x.left.toAdd
    (congrArg Multiplicative.toAdd hh.symm)
  have hx1 : x = 1 := by
    apply SemidirectProduct.ext
    · exact congrArg Multiplicative.ofAdd hv
    · exact hr
  apply toddOddTwist_ne_one
  rw [hx,hx1,map_one]

variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
variable (a : SourceIncidence.LocalData h)

/-- The original marked point group has the same outer automorphism. -/
theorem pointOddTwist_not_inner :
    ¬ ∃ m : a.P.M, pointTwist a toddOddWord = MulAut.conj m := by
  rintro ⟨m,hm⟩
  apply toddOddTwist_not_inner
  refine ⟨a.P.toddEquiv.symm m,?_⟩
  apply (MulAut.congr a.P.toddEquiv).injective
  rw [MulAut.congr_conj,a.P.toddEquiv.apply_symm_apply]
  exact (pointTwist_eq_congr a toddOddWord).symm.trans hm

/-- The plane central twist is also outer: an inner automorphism fixing Q
pointwise would be induced by Z(Q)=Z(H) and hence be the identity. -/
theorem planeTwist_not_inner (h0 : IsTypeJ4 z)
    (e : CubicAutomorphismQuotient (centralizer z ⧸ core z)) :
    ¬ ∃ x : centralizer z, planeTwist h0 e = MulAut.conj x := by
  rintro ⟨x,hx⟩
  have hc : x ∈ Subgroup.centralizer (core z : Set (centralizer z)) := by
    intro q hq
    have he : x*q*x⁻¹=q := by
      change MulAut.conj x q = q
      rw [← hx]
      exact planeTwist_fixes_core h0 e ⟨q,hq⟩
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hle : Subgroup.centralizer (core z : Set (centralizer z)) ≤ core z := by
    rw [h0.core_eq_twoCore]
    exact h0.twoCore_selfCentralizing
  have hxQ : x ∈ core z := hle hc
  have hxZ : (⟨x,hxQ⟩ : core z) ∈ center (core z) := by
    apply mem_center_iff.mpr
    intro q
    exact Subtype.ext (hc q.val q.property)
  have hxH : x ∈ center (centralizer z) := by
    rw [← SourceRecognition.core_center_eq_centralizer_center h0]
    exact mem_map_of_mem (core z).subtype hxZ
  apply planeTwist_ne_one h0 e
  rw [hx]
  apply MulEquiv.ext
  intro y
  change x*y*x⁻¹=y
  rw [← mem_center_iff.mp hxH y,mul_inv_cancel_right]

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
