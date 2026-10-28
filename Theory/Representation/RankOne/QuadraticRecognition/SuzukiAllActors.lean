module
public import Theory.Representation.RankOne.QuadraticRecognition.SuzukiActors
public import Theory.SpecificGroups.Suzuki.SmallInvolutionPair
public import BenderSuzuki.MatrixGroups.SuzukiZero
public import Theory.GroupTheory.SylowElementConjugacy
public import Theory.Representation.BinaryPrimeDisplacement

/-!
# The Suzuki quadratic square bound at every source parameter

The degenerate Suzuki group Sz(2) has a cyclic Sylow of order four, so its
involutions form one conjugacy class and every quadratic actor has order at
most two. Two concrete involutions have product of order five. Faithfulness
forces that product to move at least four binary dimensions, while displacement
is subadditive. Each involution therefore moves at least two dimensions.
Together with the previously proved nondegenerate bound, this proves
|A|² ≤ |V/C_V(A)| for every Suzuki parameter, excluding the strict DGS branch.

The group is the actual Suzuki matrix group, including Sz(2) of order twenty;
no dihedral family is appended to the Chapter 5 list. Source: DGS85,
*Groups and Graphs*, (5.12), printed pp.113–114 and the small cases on p.104.
CriticalSuzukiExclusion applies the uniform result on the original quotient.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender BenderSuzuki.MatrixGroups
namespace Representation.RankOne.QuadraticRecognition
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
local instance finiteSmallSuzukiActorQuotient (C : Submodule (ZMod 2) V) : Finite (V ⧸ C) :=
  Finite.of_surjective _ C.mkQ_surjective

private theorem suzukiZero_sylow_cyclic (S : Sylow 2 (SuzukiMatrixGroup 0)) : IsCyclic S := by
  let P : Sylow 2 (SuzukiMatrixGroup 0) := Sylow.ofCard (zpowers suzukiZeroRootGenerator) (by
    rw [Nat.card_zpowers,suzukiZeroRootGenerator_order,suzukiZero_card]
    rw [show (20 : ℕ) = 2^2 * 5 from rfl,
      Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
    norm_num [Nat.Prime.factorization Nat.prime_two,
      Nat.Prime.factorization (by decide : Nat.Prime 5)])
  let : IsCyclic P := inferInstanceAs (IsCyclic (zpowers suzukiZeroRootGenerator))
  exact (Sylow.equiv P S).isCyclic.mp inferInstance

private theorem suzukiZero_involutions_isConj
    (a b : SuzukiMatrixGroup 0) (ha : orderOf a = 2) (hb : orderOf b = 2) : IsConj a b := by
  let S : Sylow 2 (SuzukiMatrixGroup 0) := Classical.choice inferInstance
  let : IsCyclic S := suzukiZero_sylow_cyclic S
  obtain ⟨x,hx⟩ := S.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using ha)
  obtain ⟨y,hy⟩ := S.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using hb)
  have horder (c : SuzukiMatrixGroup 0) (hc : orderOf c = 2) (d : S) (hd : IsConj c (d : SuzukiMatrixGroup 0)) :
      orderOf d = 2 := by
    rw [← Subgroup.orderOf_coe]
    obtain ⟨g,hg⟩ := isConj_iff.mp hd
    rw [←hg]
    exact ((MulAut.conj g).orderOf_eq c).trans hc
  have hxy : x = y := IsCyclic.eq_of_orderOf_eq_two (horder a ha x hx) (horder b hb y hy)
  exact hx.trans (hxy ▸ hy.symm)

private theorem fixedCodim_product_le (ρ : Representation (ZMod 2) (SuzukiMatrixGroup 0) V)
    (a b : SuzukiMatrixGroup 0) :
    fixedCodim ρ (zpowers (a*b)) ≤ fixedCodim ρ (zpowers a) + fixedCodim ρ (zpowers b) := by
  let τ : SuzukiMatrixGroup 0 →* (V ≃ₗ[ZMod 2] V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp ρ.asGroupHom
  have h := BinaryNormalizerRank.rank_mul_le (τ a) (τ b)
  rw [←map_mul] at h
  simp only [fixedCodim_zpowers_eq_displacement_rank]
  exact h

/-- The small Suzuki group also has no faithful binary transvection action. -/
theorem suzukiZero_involution_fixedCodim_ge_two
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup 0) V) (hf : Function.Injective ρ)
    (a : SuzukiMatrixGroup 0) (ha : orderOf a = 2) :
    2 ≤ fixedCodim ρ (zpowers a) := by
  have heq (b : SuzukiMatrixGroup 0) (hb : orderOf b = 2) :
      fixedCodim ρ (zpowers b) = fixedCodim ρ (zpowers a) := by
    obtain ⟨g,hg⟩ := isConj_iff.mp (suzukiZero_involutions_isConj a b ha hb)
    rw [←hg,fixedCodim_zpowers_conj]
  have hp := prime_order_le_fixedCodim ρ hf (by decide : Nat.Prime 5) (by decide)
    (suzukiZeroInvolution * suzukiWeyl 0) suzukiZeroInvolution_mul_weyl_order
  have h5 : orderOf (2 : ZMod 5) = 4 := BinaryPrimeDegree.orderOf_two_mod_five
  rw [h5] at hp
  have hu := fixedCodim_product_le ρ suzukiZeroInvolution (suzukiWeyl 0)
  rw [heq _ suzukiZeroInvolution_order,heq _ (suzukiWeyl_orderOf 0)] at hu
  omega

/-- DGS (5.12)'s square exclusion includes Sz(2), the actual order-twenty
matrix group. No D₁₀ row is added to the source catalogue. -/
theorem suzukiZero_square_bound
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup 0) V) (hf : Function.Injective ρ)
    (S : Sylow 2 (SuzukiMatrixGroup 0)) (A : Subgroup (SuzukiMatrixGroup 0))
    (hAS : A ≤ S) (hq : IsQuadratic ρ A) :
    Nat.card A ^ 2 ≤ Nat.card (V ⧸ fixedSpace ρ A) := by
  let : IsElementaryAbelian 2 A := elementary_of_faithful_quadratic ρ hf A hq
  let : IsCyclic S := suzukiZero_sylow_cyclic S
  let : IsCyclic A := Subgroup.isCyclic_of_le hAS
  have hAc : Nat.card A ≤ 2 := by
    obtain ⟨a,ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := A)
    have hs : a ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian a.val a.property)
    have hd := orderOf_dvd_of_pow_eq_one hs
    rw [ha] at hd
    exact Nat.le_of_dvd (by decide) hd
  by_cases hA : A = ⊥
  · rw [hA,card_bot,one_pow]
    exact Nat.card_pos
  obtain ⟨a,ha,ha1⟩ := A.bot_or_exists_ne_one.resolve_left hA
  have ha2 : orderOf a = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian a ha) ha1
  have hd := (suzukiZero_involution_fixedCodim_ge_two ρ hf a ha2).trans
    (NaturalTensor.fixedCodim_mono ρ (zpowers_le.mpr ha))
  have hc : 4 ≤ Nat.card (V ⧸ fixedSpace ρ A) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hd
  nlinarith

/-- The uniform Suzuki square bound, including every source parameter. -/
theorem suzuki_all_square_bound (m : ℕ)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V) (hf : Function.Injective ρ)
    (S : Sylow 2 (SuzukiMatrixGroup m)) (A : Subgroup (SuzukiMatrixGroup m))
    (hAS : A ≤ S) (hq : IsQuadratic ρ A) :
    Nat.card A ^ 2 ≤ Nat.card (V ⧸ fixedSpace ρ A) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact suzukiZero_square_bound ρ hf S A hAS hq
  · exact suzuki_square_bound hm ρ hf S A hAS hq

end Representation.RankOne.QuadraticRecognition
