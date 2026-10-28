module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ExceptionalRestrictions.Ahat6
public import Theory.LinearAlgebra.OddDeterminantOneDisplacement
public import Theory.GroupTheory.PrimeOrderLift

/-!
# The exceptional triple-six intersection on the binary doubled orbit

The source C.2.7(c) intersection has index fifteen in the exceptional
triple-cover block. Its order is therefore divisible by nine, with the
central cubic retained. On the other hand, its actual action on the original
paired plane's orbit factors through S₃. The kernel centralizes the residual
sixteen embedded in U(K). An order-three element cannot do this: the genuine
SL₃(F₄) restriction has determinant one, so a nonidentity odd-order actor
fixes at most four vectors. Thus the kernel is prime to three, a contradiction.

This uses the source intersection index. An index-two subgroup of a Sylow
alone can fix a binary four-space in the hexacode, as witnessed by
Hexacode.ThompsonOffenders.planeFixed_finrank; that stronger local exclusion
is unavailable. The Chapter12 companion supplies the original orbit action,
residual sixteen and literal intersection, without a new source premise.

Source: Aschbacher--Smith, C.2.7(3)(c), printed p.145, C.1.22, p.129,
and the proof after 7.7.10, pp.708--709, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Theory.GroupTheory
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryExceptionalSix
open scoped MatrixGroups IsMulCommutative

/-- Odd determinant-one actors on the three-space over F₄ fix at most four vectors. -/
theorem odd_linear_fixed_card {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) (g : Matrix.SpecialLinearGroup (Fin 3) F)
    (hg : Odd (orderOf g)) (hne : g ≠ 1) :
    Nat.card {v : Fin 3 → F // g.toLin' v = v} ≤ 4 := by
  let e := g.toLin'
  have he : e ≠ 1 := by
    intro h
    apply hne
    apply Matrix.SpecialLinearGroup.toLin'_injective
    simpa only [map_one] using h
  have ho : Odd (orderOf e) := by
    rw [orderOf_injective _ Matrix.SpecialLinearGroup.toLin'_injective]
    exact hg
  have hd : e.det = 1 := by
    apply Units.ext
    rw [LinearEquiv.coe_det]
    change LinearMap.det (Matrix.toLin' g.val) = 1
    rw [LinearMap.det_toLin']
    exact g.property
  have hb := e.two_le_displacement_of_odd_det_one he ho hd
  let δ := e.toLinearMap - LinearMap.id
  have hr := δ.finrank_range_add_finrank_ker
  have hv : Module.finrank F (Fin 3 → F) = 3 := by simp
  rw [hv] at hr
  have hk : Module.finrank F δ.ker ≤ 1 := by
    change 2 ≤ Module.finrank F δ.range at hb
    omega
  let a : {v : Fin 3 → F // g.toLin' v = v} ≃ δ.ker :=
    { toFun := fun v => ⟨v.val, sub_eq_zero.mpr v.property⟩
      invFun := fun v => ⟨v.val, sub_eq_zero.mp v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr a,Module.natCard_eq_pow_finrank (K := F),hF]
  exact (Nat.pow_le_pow_right (by decide : 0 < (4 : ℕ)) hk).trans_eq (by decide)

/-- An order-three element cannot centralize a sixteen in the actual exceptional U. -/
theorem exceptional_cubic_not_centralize {K : Type*} [Group K] [Finite K]
    (hb : ChapterC.IsExceptionalAhat6Block K) (D : Subgroup K)
    (hDU : D ≤ ChapterC.blockU K) (hD : 16 ≤ Nat.card D)
    (x : K) (hx : orderOf x = 3) : x ∉ centralizer (D : Set K) := by
  intro hfix
  let := hb.1.elementary
  obtain ⟨F,_,_,hF,_,m,ht,f,e,hf,he⟩ := hb.natural_restriction
  let := m
  let := ht
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  let q := QuotientGroup.mk' (pCore 2 K)
  have hqx : orderOf (q x) = 3 := by
    rw [q.orderOf_map_eq_of_coprime_of_isPGroup_ker
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) x (by rw [hx]; decide),hx]
  have hfx : orderOf (f (q x)) = 3 := (orderOf_injective f hf (q x)).trans hqx
  have hne : f (q x) ≠ 1 := by
    intro h
    rw [h,orderOf_one] at hfx
    contradiction
  let j : D → {v : Fin 3 → F // (f (q x)).toLin' v = v} := fun d =>
    ⟨e (Additive.ofMul (inclusion hDU d)),by
      have hh := he x (inclusion hDU d)
      have hc : ChapterC.blockConjugate K x (inclusion hDU d) = inclusion hDU d := by
        apply Subtype.ext
        change x * (d : K) * x⁻¹ = (d : K)
        rw [←hfix d d.property,mul_inv_cancel_right]
      rw [hc] at hh
      exact hh.symm⟩
  have hj : Function.Injective j := by
    intro a b h
    apply inclusion_injective hDU
    apply Additive.ofMul.injective
    exact e.injective (congrArg Subtype.val h)
  have hbound := (Nat.card_le_card_of_injective j hj).trans
    (odd_linear_fixed_card hF (f (q x)) (by rw [hfx]; decide) hne)
  omega

/-- A symmetric-three action faithful on a sixteen up to its pointwise
centralizer cannot occur on the index-fifteen exceptional intersection. -/
theorem no_exceptional_index_fifteen {K : Type*} [Group K] [Finite K]
    (hb : ChapterC.IsExceptionalAhat6Block K) (B D : Subgroup K)
    (hDU : D ≤ ChapterC.blockU K) (hD : 16 ≤ Nat.card D)
    (π : B →* Equiv.Perm (Fin 3))
    (hk : ∀ x : π.ker, (x.val : K) ∈ centralizer (D : Set K)) : B.index ≠ 15 := by
  intro hindex
  have hthree : ¬ 3 ∣ Nat.card π.ker := by
    intro hd
    obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := π.ker) 3 hd
    have ho : orderOf (x.val : K) = 3 := by
      rw [Subgroup.orderOf_coe,Subgroup.orderOf_coe,hx]
    exact exceptional_cubic_not_centralize hb D hDU hD x.val ho (hk x)
  have hquot : Nat.card (K ⧸ pCore 2 K) = 1080 := by
    rw [← (center (K ⧸ pCore 2 K)).card_mul_index,
      index_eq_card,hb.2.2.1,Nat.card_congr hb.2.2.2.1.some.toEquiv,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := K)).exists_card_eq
  have hcard := (pCore 2 K).card_mul_index
  rw [index_eq_card,hquot,hn] at hcard
  have hB := B.card_mul_index
  rw [hindex,←hcard] at hB
  have hBcard : Nat.card B = 72 * 2 ^ n := by omega
  have h9 : 9 ∣ Nat.card B := by rw [hBcard]; exact dvd_mul_of_dvd_left (by decide) _
  rw [←π.ker.card_mul_index,index_ker] at h9
  have hc : Nat.Coprime 9 (Nat.card π.ker) :=
    (Nat.prime_three.coprime_pow_of_not_dvd (m := 2) hthree).symm
  have h9r := hc.dvd_of_dvd_mul_left h9
  have hd := π.range.card_subgroup_dvd_card
  rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 3)),
    Fintype.card_perm,Fintype.card_fin] at hd
  have hh := h9r.trans hd
  norm_num [Nat.factorial] at hh

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryExceptionalSix
