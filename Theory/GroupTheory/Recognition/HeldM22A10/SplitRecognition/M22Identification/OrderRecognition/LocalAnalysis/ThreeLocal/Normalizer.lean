module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.Contracts
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The order of a fused elementary-nine Sylow normalizer

An elementary abelian Sylow three-subgroup of order nine has 48
abstract automorphisms. If it is self-centralizing, the index in its
normalizer therefore divides 48 and is prime to three. If all ambient
order-three elements are fused, Burnside's normalizer control of fusion
makes its eight nonidentity elements a single normalizer orbit. Its
normalizer index is thus eight or sixteen, and its order is 72 or 144.

This is the normalizer-order consequence needed from Janko's Lemma 8.
The elementary Sylow and fusion hypotheses remain explicit; this module
does not prove their existence from the Case II centralizer.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 3, pp.7–8, Lemma 8.
-/

open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.HeldM22A10.M22Identification

private theorem card_mulAut_nine (P : Type*) [Group P] [Finite P]
    [IsElementaryAbelian 3 P] (hP : Nat.card P = 9) : Nat.card (MulAut P) = 48 := by
  classical
  have hpow : 3 ^ Module.finrank (ZMod 3) (Additive P) = 3 ^ 2 := by
    have hsize := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive P)
    change Nat.card P = _ at hsize
    simpa only [Nat.card_zmod, hP, show (3 : ℕ) ^ 2 = 9 by decide] using hsize.symm
  have hdim : Module.finrank (ZMod 3) (Additive P) = 2 :=
    Nat.pow_right_injective (by decide : 1 < 3) hpow
  let autLinear : MulAut P ≃* (Additive P ≃ₗ[ZMod 3] Additive P) :=
    { toFun := fun aut =>
        { aut.toAdditive with map_smul' := ZMod.map_smul aut.toAdditive }
      invFun := fun aut => MulEquiv.toAdditive.symm aut.toAddEquiv
      left_inv := by intro aut; ext; rfl
      right_inv := by intro aut; ext; rfl
      map_mul' := by intro aut other; ext; rfl }
  let basis := Module.finBasisOfFinrankEq (ZMod 3) (Additive P) hdim
  let e := autLinear.trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) (Additive P)).symm.trans
      (Matrix.GeneralLinearGroup.toLin' basis).symm)
  rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field]
  norm_num [Fin.prod_univ_succ, ZMod.card]

private theorem order_three_of_ne_one {P : Type*} [Group P]
    [IsElementaryAbelian 3 P] (x : P) (hx : x ≠ 1) : orderOf x = 3 := by
  apply orderOf_eq_prime
  · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 P) x
  · exact hx

/-- Burnside fusion and the faithful normalizer action retain both source orders. -/
public theorem normalizer_card_of_elementary_nine_fusion
    {G : Type*} [Group G] [Finite G] (P : Sylow 3 G)
    [IsElementaryAbelian 3 P] (hP : Nat.card P = 9)
    (hC : centralizer (P : Set G) = P)
    (hf : ∀ x y : G, orderOf x = 3 → orderOf y = 3 → IsConj x y) :
    Nat.card (normalizer (P : Set G)) = 72 ∨
      Nat.card (normalizer (P : Set G)) = 144 := by
  classical
  change centralizer ((P : Subgroup G) : Set G) = (P : Subgroup G) at hC
  change Nat.card (normalizer ((P : Subgroup G) : Set G)) = 72 ∨
    Nat.card (normalizer ((P : Subgroup G) : Set G)) = 144
  let N := normalizer ((P : Subgroup G) : Set G)
  let f := (P : Subgroup G).normalizerMonoidHom
  have hk : f.ker = (P : Subgroup G).subgroupOf N := by
    rw [Subgroup.normalizerMonoidHom_ker, hC]
  have hkc : Nat.card f.ker = 9 := by
    rw [hk]
    exact (Nat.card_congr (subgroupOfEquivOfLe (P : Subgroup G).le_normalizer).toEquiv).trans hP
  have hi : ¬ 3 ∣ f.ker.index := by
    rw [hk]
    exact (P.subtype (P : Subgroup G).le_normalizer).not_dvd_index
  have hd : f.ker.index ∣ 48 := by
    rw [index_ker]
    exact card_mulAut_nine P hP ▸ f.range.card_subgroup_dvd_card
  have hprod : 9 * f.ker.index = Nat.card N := by
    simpa only [hkc] using f.ker.card_mul_index
  obtain ⟨x, hx⟩ : ∃ x : (P : Subgroup G), x ≠ 1 := by
    by_contra! h
    have : Subsingleton P := ⟨fun x y => (h x).trans (h y).symm⟩
    have hc : Nat.card P = 1 := Nat.card_unique
    omega
  have horbit : MulAction.orbit N x = {y : (P : Subgroup G) | y ≠ 1} := by
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      intro h
      have he := congrArg Subtype.val h
      change (n : G) * (x : G) * (n : G)⁻¹ = 1 at he
      apply hx
      apply Subtype.ext
      change (x : G) = 1
      have hh := congrArg (fun t : G => (n : G)⁻¹ * t * (n : G)) he
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right,
        mul_one, inv_mul_cancel] using hh
    · intro hy
      have hxy := hf x y (by simpa using order_three_of_ne_one x hx)
        (by simpa using order_three_of_ne_one y hy)
      obtain ⟨g, hg⟩ := isConj_iff.mp hxy
      have hgmem : (g⁻¹)⁻¹ * (x : G) * g⁻¹ ∈ P := by
        change (g⁻¹)⁻¹ * (x : G) * g⁻¹ ∈ (P : Subgroup G)
        simpa only [inv_inv, hg] using y.property
      obtain ⟨n, hn, he⟩ := P.conj_eq_normalizer_conj_of_mem (x : G) g⁻¹
        x.property hgmem
      refine ⟨⟨n⁻¹, N.inv_mem hn⟩, ?_⟩
      apply Subtype.ext
      change n⁻¹ * (x : G) * (n⁻¹)⁻¹ = y
      simpa only [inv_inv, hg] using he.symm
  have horbitcard : Nat.card (MulAction.orbit N x) = 8 := by
    rw [horbit]
    let := Fintype.ofFinite P
    change Nat.card {y : (P : Subgroup G) // y ≠ 1} = 8
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp [← Nat.card_eq_fintype_card, hP]
  have h8 : 8 ∣ Nat.card N := by
    rw [← horbitcard, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer N x),
      ← Subgroup.index_eq_card]
    exact (MulAction.stabilizer N x).index_dvd_card
  have h8i : 8 ∣ f.ker.index := by
    have hh : 8 ∣ 9 * f.ker.index := hprod ▸ h8
    exact (show Nat.Coprime 8 9 by decide).dvd_of_dvd_mul_left hh
  have hcases : f.ker.index = 8 ∨ f.ker.index = 16 := by
    have hle := Nat.le_of_dvd (by decide : 0 < 48) hd
    interval_cases f.ker.index <;> omega
  rcases hcases with h | h
  · exact Or.inl (by simpa only [h] using hprod.symm)
  · exact Or.inr (by simpa only [h] using hprod.symm)
end Theory.GroupTheory.HeldM22A10.M22Identification
