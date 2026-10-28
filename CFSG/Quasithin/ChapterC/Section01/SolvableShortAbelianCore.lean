module

public import CFSG.Quasithin.ChapterC.Section01.BlockBasics
public import Theory.GroupTheory.PResidual.AbelianCoprimeKernel
public import Theory.GroupTheory.PResidual.PrimeSection
public import Theory.GroupTheory.Commutator.CentralizingComplement
public import Theory.GroupTheory.CoprimeCentralizerDirectProduct
public import Theory.GroupTheory.NormalizingInvolutionCard
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Solvable short groups with abelian two-core have order twelve

We use the literal short-group conditions of C.1.7. Solvability excludes
its quasisimple quotient. Since the core image in L/U(L) is central and
the quotient above it has order three, L/U(L) is abelian. Two-perfection
then makes its order odd, so O₂(L) = U(L).

An element of order three supplements this elementary abelian core.
Coprime splitting makes its fixed subgroup trivial. For any nonidentity
core element x, the cubic norm identity says a²(x) = x a(x), so x and
a(x) generate an invariant four-group. The full normal-subgroup interval
in C.1.7 forces this four-group to be the whole core. Thus |L| = 4 · 3.
No natural-module identification or alternating-block assumption is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7–13,
printed pp.123–125, especially the solvable case of C.1.8.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
variable {L : Type*} [Group L] [Finite L]

omit [Finite L] in
private theorem quotient_three [Group.IsSolvable L] (h : IsShort L) :
    Nat.card (L ⧸ pCore 2 L) = 3 := by
  rcases h.quotient with hq | hq
  · let := hq
    let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) :=
      IsQuasisimple.simple
    let : Nontrivial (L ⧸ pCore 2 L) :=
      (QuotientGroup.mk'_surjective (center (L ⧸ pCore 2 L))).nontrivial
    exact (Group.IsPerfect.not_isSolvable (L ⧸ pCore 2 L) inferInstance).elim
  · exact hq

private theorem core_eq_U (h : IsShort L) (hq : Nat.card (L ⧸ pCore 2 L) = 3) :
    pCore 2 L = blockU L := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : IsCyclic (L ⧸ pCore 2 L) := isCyclic_of_prime_card hq
  let f := QuotientGroup.lift (blockU L) (QuotientGroup.mk' (pCore 2 L))
    (by simpa only [QuotientGroup.ker_mk'] using (blockU_le_core (L := L)))
  have hk : f.ker = (pCore 2 L).map (QuotientGroup.mk' (blockU L)) := by
    dsimp [f]
    rw [QuotientGroup.ker_lift, QuotientGroup.ker_mk']
  let : IsMulCommutative (L ⧸ blockU L) :=
    f.isMulCommutative_of_isCyclic_of_ker_le_center (hk ▸ blockU_core_image_le_center)
  have hc : Nat.Coprime 2 (Nat.card (L ⧸ blockU L)) := by
    have hh := coprime_card_pResidual_of_commGroup (A := L ⧸ blockU L) 2
    rwa [(pResidual_eq_top_iff 2 _).mpr (h.quotient_twoPerfect (blockU L)), card_top] at hh
  have hb : (pCore 2 L).map (QuotientGroup.mk' (blockU L)) = ⊥ := by
    apply (Subgroup.card_eq_one).mp
    rcases (pCore_isPGroup (p := 2) (G := L)).map (QuotientGroup.mk' (blockU L)) |>.card_eq_or_dvd with h1 | h2
    · exact h1
    · exact (Nat.prime_two.coprime_iff_not_dvd.mp hc
        (h2.trans (card_subgroup_dvd_card _))).elim
  exact le_antisymm (by simpa only [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] using hb)
    blockU_le_core

private theorem invariant_four {V : Type*} [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [Nontrivial V] (a : MulAut V)
    (ha : a ^ 3 = 1) (hf : ∀ x, a x = x → x = 1) :
    ∃ W : Subgroup V, Nat.card W = 4 ∧ W.map a.toMonoidHom = W := by
  classical
  have hs (x : V) : x ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) x
  have hi (x : V) : x⁻¹ = x := inv_eq_iff_mul_eq_one.mpr (by simpa [pow_two] using hs x)
  have ha3 (x : V) : a (a (a x)) = x := congrArg (fun f : MulAut V => f x) ha
  have ha2 (x : V) : a (a x) = x * a x := by
    have hn : x * a x * a (a x) = 1 := hf _ (by rw [map_mul, map_mul, ha3]; ac_rfl)
    exact (eq_inv_of_mul_eq_one_right hn).trans (hi _)
  obtain ⟨x, hx⟩ := exists_ne (1 : V)
  have ho : orderOf x = 2 := orderOf_eq_prime (hs x) hx
  have hout : a x ∉ zpowers x := by
    intro hmem
    rw [mem_zpowers_iff_mem_range_orderOf, ho] at hmem
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hmem
    have hnlt := Finset.mem_range.mp hn
    interval_cases n
    · exact hx (a.injective (by simpa using he.symm))
    · exact hx (hf x (by simpa using he.symm))
  let W := zpowers x ⊔ zpowers (a x)
  have hcard : Nat.card W = 4 := by
    rw [card_sup_zpowers_of_normalizing_involution (zpowers x) (a x) (hs _) hout
      (by rw [normalizer_eq_top]; trivial), Nat.card_zpowers, ho]
  have hxW : x ∈ W := (show zpowers x ≤ W from le_sup_left) (mem_zpowers x)
  have haxW : a x ∈ W := (show zpowers (a x) ≤ W from le_sup_right) (mem_zpowers (a x))
  have haaW : a (a x) ∈ W := by rw [ha2]; exact W.mul_mem hxW haxW
  refine ⟨W, hcard, le_antisymm ?_ ?_⟩
  · rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    exact sup_le (zpowers_le.mpr haxW) (zpowers_le.mpr haaW)
  · refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
    · exact mem_map.mpr ⟨a (a x), haaW, ha3 x⟩
    · exact mem_map.mpr ⟨x, hxW, rfl⟩

private theorem core_four [IsMulCommutative (pCore 2 L)] (h : IsShort L)
    (hq : Nat.card (L ⧸ pCore 2 L) = 3) : Nat.card (pCore 2 L) = 4 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hU : pCore 2 L = blockU L := core_eq_U h hq
  let : IsElementaryAbelian 2 (pCore 2 L) := hU ▸ h.elementary
  let : Nontrivial (pCore 2 L) := (Subgroup.nontrivial_iff_ne_bot _).mpr h.core_ne_bot
  obtain ⟨t, ht, hgen⟩ := exists_prime_order_sup_pCore_eq_top (G := L)
    (by decide : Nat.Coprime 2 3) hq
  have hc : Nat.Coprime (Nat.card (zpowers t)) (Nat.card (pCore 2 L)) := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := L)).exists_card_eq
    rw [Nat.card_zpowers, ht, hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hcomm : ⁅pCore 2 L, zpowers t⁆ = pCore 2 L := by
    rw [commutator_eq_of_centralizing_sup (by simpa only [sup_comm] using hgen)
      (le_centralizer_iff_isMulCommutative.mpr inferInstance) le_normalizer_of_normal]
    exact hU.symm
  have hd := commutator_disjoint_centralizer_of_coprime (pCore 2 L) (zpowers t)
    le_normalizer_of_normal hc
  rw [hcomm, disjoint_iff, inf_eq_right.mpr inf_le_left] at hd
  let a : MulAut (pCore 2 L) := MulAut.conjNormal t
  have ha : a ^ 3 = 1 := by
    change (MulAut.conjNormal t) ^ 3 = 1
    rw [← map_pow, ← ht, pow_orderOf_eq_one, map_one]
  have hf : ∀ x, a x = x → x = 1 := by
    intro x hx
    apply Subtype.ext
    have htx : Commute t (x : L) := by
      have he := congrArg Subtype.val hx
      change t * (x : L) * t⁻¹ = x at he
      exact (mul_inv_eq_iff_eq_mul.mp he)
    have hm : (x : L) ∈ pCore 2 L ⊓ centralizer (zpowers t : Set L) := by
      refine ⟨x.property, mem_centralizer_iff.mpr ?_⟩
      rintro y ⟨n, rfl⟩
      exact (htx.zpow_left n).eq
    simpa only [hd, mem_bot, Subgroup.coe_one] using hm
  obtain ⟨W, hWcard, hWmap⟩ := invariant_four a ha hf
  let N := W.map (pCore 2 L).subtype
  have hN : N ≤ pCore 2 L := map_subtype_le _
  have hNcard : Nat.card N = 4 := (card_subtype _ _).trans hWcard
  have htN : t ∈ normalizer (N : Set L) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (W.map (pCore 2 L).subtype).map (MulAut.conj t).toMonoidHom = N
    calc
      _ = (W.map a.toMonoidHom).map (pCore 2 L).subtype := by
        rw [Subgroup.map_map, Subgroup.map_map]
        rfl
      _ = N := by rw [hWmap]
  have hPN : pCore 2 L ≤ normalizer (N : Set L) :=
    ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le hN)).trans (centralizer_le_normalizer _)
  have hnormal : N.Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [← hgen]
    exact sup_le (zpowers_le.mpr htN) hPN))
  have hcenter : blockU L ⊓ center L = ⊥ := by
    rw [← hU]
    exact le_bot_iff.mp ((inf_le_inf_left _ (center_le_centralizer _)).trans hd.le)
  rcases h.irreducible.2 N hnormal (by rw [hcenter]; exact bot_le)
    (hN.trans hU.le) with hbot | hfull
  · rw [hbot, hcenter, card_bot] at hNcard
    norm_num at hNcard
  · rw [← hU] at hfull
    exact hfull ▸ hNcard

/-- The numerical consequence of shortness used by the binary linear Borel exclusion. -/
theorem IsShort.card_eq_twelve_of_solvable_of_abelian_core [Group.IsSolvable L] [IsMulCommutative (pCore 2 L)]
    (h : IsShort L) : Nat.card L = 12 := by
  have hq := quotient_three h
  have hP := core_four h hq
  have he := Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 L)
  rw [hq, hP] at he
  exact he

end CFSG.Quasithin.ChapterC
