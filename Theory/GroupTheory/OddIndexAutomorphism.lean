module
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

/-!
# Inner automorphisms detected at odd index

An automorphism fixing an odd-index overgroup of a self-centralizing normal
elementary two-group is inner by an element of that kernel. Average the
crossed displacement over the literal left cosets; their odd number makes
the product a principal crossed homomorphism. The resulting conjugator is
fixed by the specified overgroup.

The averaging proof extends the private argument in
`GraphUniquenessSystem/OddIndexRigidity.lean`, retaining its conjugator
instead of requiring the fixed subgroup to vanish. The ambient centralizer
consequence is used for T∩L in Aschbacher–Smith, 14.4.5, printed p.1008.
-/

public noncomputable section
open Subgroup
namespace MulAut
private theorem crossed_principal_of_odd_index
    {G A : Type*} [Group G] [Finite G] [CommGroup A]
    (H : Subgroup G) (ρ : G →* MulAut A) (δ : G → A)
    (hmul : ∀ g k, δ (g * k) = δ g * ρ g (δ k))
    (hH : ∀ h ∈ H, δ h = 1) (hpow : ∀ a : A, a ^ 2 = 1)
    (hodd : Odd H.index) :
    ∃ c : A, (∀ h : H, ρ h c = c) ∧ ∀ g, c = δ g * ρ g c := by
  classical
  let := Fintype.ofFinite (G ⧸ H)
  let d : G ⧸ H → A := Quotient.lift δ (by
    intro a b hab
    have hh := hH (a⁻¹ * b) (QuotientGroup.leftRel_apply.mp hab)
    have he := hmul a (a⁻¹ * b)
    rw [mul_inv_cancel_left, hh, map_one, mul_one] at he
    exact he.symm)
  have hd (g : G) (q : G ⧸ H) : d (g • q) = δ g * ρ g (d q) := by
    induction q using QuotientGroup.induction_on with
    | H a => exact hmul g a
  let c : A := ∏ q : G ⧸ H, d q
  have hc (g : G) : c = δ g * ρ g c := by
    have hr : c = ∏ q : G ⧸ H, d (g • q) :=
      (Fintype.prod_equiv (MulAction.toPerm g) (fun q => d (g • q)) d (fun _ => rfl)).symm
    conv_lhs => rw [hr]
    simp_rw [hd]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← map_prod]
    have hp : δ g ^ Fintype.card (G ⧸ H) = δ g := by
      rw [← Nat.card_eq_fintype_card, ← index_eq_card]
      obtain ⟨k, hk⟩ := hodd
      rw [hk, pow_add, pow_mul, hpow, one_pow, pow_one, one_mul]
    rw [hp]
  refine ⟨c, ?_, hc⟩
  intro h
  have hh := hc h
  rw [hH h h.property, one_mul] at hh
  exact hh.symm

open scoped IsMulCommutative

/-- An automorphism fixing an odd-index overgroup of a self-centralizing
normal elementary two-group is conjugation by an element fixed by that overgroup. -/
theorem eq_conj_of_fixes_odd_index
    {B : Type*} [Group B] [Finite B]
    (N S : Subgroup B) [N.Normal] [IsElementaryAbelian 2 N]
    (hNS : N ≤ S) (hself : centralizer (N : Set B) ≤ N) (hodd : Odd S.index)
    (α : MulAut B) (hfix : ∀ s ∈ S, α s = s) :
    ∃ n : N, (n : B) ∈ centralizer (S : Set B) ∧ α = MulAut.conj (n : B) := by
  have hδ (g : B) : α g * g⁻¹ ∈ N := by
    apply hself
    apply mem_centralizer_iff.mpr
    intro n hn
    have hi : g⁻¹ * n * g ∈ N := by
      simpa only [inv_inv] using (inferInstance : N.Normal).conj_mem n hn g⁻¹
    have he := hfix (g⁻¹ * n * g) (hNS hi)
    rw [map_mul, map_mul, map_inv, hfix n (hNS hn)] at he
    have hh := congrArg (fun a => α g * a * g⁻¹) he
    group at hh
    simpa only [mul_assoc, zpow_neg_one] using hh
  let δ : B → N := fun g => ⟨α g * g⁻¹, hδ g⟩
  obtain ⟨n, hn, he⟩ := crossed_principal_of_odd_index S
    (MulAut.conjNormal : B →* MulAut N) δ
    (by intro g k; apply Subtype.ext; simp [δ, map_mul, mul_assoc])
    (by intro s hs; apply Subtype.ext; simp [δ, hfix s hs])
    (fun n => Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (n : B) n.property)) hodd
  refine ⟨n, ?_, ?_⟩
  · intro s hs
    have hh := congrArg Subtype.val (hn ⟨s,hs⟩)
    change s * (n : B) * s⁻¹ = n at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  · apply MulEquiv.ext
    intro g
    have hh := congrArg Subtype.val (he g)
    change (n : B) = (α g * g⁻¹) * (g * (n : B) * g⁻¹) at hh
    have heq := congrArg (fun b => b * g * (n : B)⁻¹) hh
    change α g = (n : B) * g * (n : B)⁻¹
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using heq.symm
end MulAut

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The centralizer of an odd-index overgroup of the abelian kernel is inner
on the block, through an element of that kernel. -/
theorem centralizer_le_sup_of_odd_index
    (L V S : Subgroup G) (hVL : V ≤ L) (hVS : V ≤ S)
    [IsElementaryAbelian 2 V] [(V.subgroupOf L).Normal]
    (hfaith : L ⊓ centralizer (V : Set G) ≤ V)
    (hodd : Odd (S.subgroupOf L).index) :
    normalizer (L : Set G) ⊓ centralizer (S : Set G) ≤
      V ⊔ centralizer (L : Set G) := by
  let : IsElementaryAbelian 2 (V.subgroupOf L) := IsElementaryAbelian.subgroupOf hVL
  intro c hc
  let α := L.normalizerMonoidHom ⟨c,hc.1⟩
  have hself : centralizer (V.subgroupOf L : Set L) ≤ V.subgroupOf L := by
    intro x hx
    apply hfaith
    refine ⟨x.property, ?_⟩
    intro v hv
    exact congrArg Subtype.val (hx (⟨v,hVL hv⟩ : L) hv)
  obtain ⟨v, hv, he⟩ := MulAut.eq_conj_of_fixes_odd_index
    (V.subgroupOf L) (S.subgroupOf L) (comap_mono hVS) hself hodd α (by
      intro s hs
      apply Subtype.ext
      change c * (s : G) * c⁻¹ = s
      rw [← hc.2 s hs, mul_inv_cancel_right])
  have hvC : (v.val.val)⁻¹ * c ∈ centralizer (L : Set G) := by
    intro l hl
    have hh := congrArg Subtype.val (DFunLike.congr_fun he (⟨l,hl⟩ : L))
    change c * l * c⁻¹ = v.val.val * l * v.val.val⁻¹ at hh
    calc
      l * (v.val.val⁻¹ * c) = v.val.val⁻¹ * (v.val.val * l * v.val.val⁻¹) * c := by group
      _ = v.val.val⁻¹ * (c * l * c⁻¹) * c := by rw [hh]
      _ = (v.val.val⁻¹ * c) * l := by group
  have hm := (V ⊔ centralizer (L : Set G)).mul_mem
    (mem_sup_left v.property) (mem_sup_right hvC)
  change v.val.val * (v.val.val⁻¹ * c) ∈ V ⊔ centralizer (L : Set G) at hm
  simpa only [mul_inv_cancel_left] using hm
end Subgroup
