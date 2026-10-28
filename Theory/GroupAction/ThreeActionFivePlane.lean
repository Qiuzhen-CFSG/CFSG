module
public import Theory.Frattini.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Theory.GroupAction.Invariant
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Theory.GroupTheory.PGroup.CoprimeFrattiniAction
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Tactic

/-!
# Cubic actions on a five-plane and commuting involutions

A nontrivial three-group action on a group of order 25 is fixed-free and
irreducible. Orbit counting modulo three rules out a fixed subgroup or an
invariant subgroup of order five. On an abelian such group, a commuting
nonidentity involution therefore has trivial fixed subgroup, and inverts
every element. The Frattini kernel also detects nontrivial coprime actions.

These facts apply to the literal supercritical Frattini quotient in
Aschbacher--Smith, proof of 12.6.26, printed p.832.
-/

public section
open Subgroup
namespace Theory.GroupAction

variable {A W : Type*} [Group A] [Group W] [Finite W]
  [MulDistribMulAction A W]

/-- A nontrivial three-group action on a group of order 25 is fixed-free. -/
theorem fixed_eq_bot_of_three_action_card_twentyfive
    (hA : IsPGroup 3 A) (hW : Nat.card W = 25)
    (hm : FixedPoints.subgroup A W ≠ ⊤) : FixedPoints.subgroup A W = ⊥ := by
  have hmod := hA.card_modEq_card_fixedPoints W
  change Nat.ModEq 3 (Nat.card W) (Nat.card (FixedPoints.subgroup A W)) at hmod
  rw [hW] at hmod
  have hd : Nat.card (FixedPoints.subgroup A W) ∣ 5 ^ 2 :=
    by simpa [hW] using (FixedPoints.subgroup A W).card_subgroup_dvd_card
  obtain ⟨n,hn,hc⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 5)).mp hd
  interval_cases n
  · exact card_eq_one.mp hc
  · rw [hc] at hmod
    norm_num [Nat.ModEq] at hmod
  · exact (hm (eq_top_of_card_eq _ (hc.trans hW.symm))).elim

/-- Every invariant subgroup of the same nontrivial action is trivial or full. -/
theorem irreducible_of_three_action_card_twentyfive
    (hA : IsPGroup 3 A) (hW : Nat.card W = 25)
    (hm : FixedPoints.subgroup A W ≠ ⊤)
    (B : Subgroup W) [IsInvariant A W B] : B = ⊥ ∨ B = ⊤ := by
  have hf := fixed_eq_bot_of_three_action_card_twentyfive hA hW hm
  have hfB : FixedPoints.subgroup A B = ⊥ := by
    apply bot_unique
    intro x hx
    apply Subtype.ext
    exact hf.le (fun a => congrArg Subtype.val (hx a))
  have hmod := hA.card_modEq_card_fixedPoints B
  change Nat.ModEq 3 (Nat.card B) (Nat.card (FixedPoints.subgroup A B)) at hmod
  rw [hfB,card_bot] at hmod
  have hd : Nat.card B ∣ 5 ^ 2 := by simpa [hW] using B.card_subgroup_dvd_card
  obtain ⟨n,hn,hc⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 5)).mp hd
  interval_cases n
  · exact Or.inl (card_eq_one.mp hc)
  · rw [hc] at hmod
    norm_num [Nat.ModEq] at hmod
  · exact Or.inr (eq_top_of_card_eq _ (hc.trans hW.symm))

end Theory.GroupAction

namespace MulAut
open scoped IsMulCommutative
variable {A W : Type*} [Group A] [Group W] [IsMulCommutative W] [Finite W]

/-- A commuting nonidentity involution inverts the entire abelian five-plane. -/
theorem inverts_of_commuting_three_action_card_twentyfive
    (hA : IsPGroup 3 A) (hW : Nat.card W = 25)
    (a : A →* MulAut W) (ha : a ≠ 1)
    (t : MulAut W) (ht : t ^ 2 = 1) (hne : t ≠ 1)
    (hcomm : ∀ g, Commute t (a g)) : ∀ w, t w = w⁻¹ := by
  let : MulDistribMulAction A W := MulDistribMulAction.compHom W a
  have hm : FixedPoints.subgroup A W ≠ ⊤ := by
    intro hh
    apply ha
    ext g w
    exact (hh.ge (mem_top w)) g
  have hinv : IsInvariant A W t.fixedSubgroup := by
    constructor
    intro g w
    constructor
    · intro hw
      rw [mem_fixedSubgroup] at hw ⊢
      change t ((a g) w) = (a g) w
      rw [show t ((a g) w) = (a g) (t w) from DFunLike.congr_fun (hcomm g).eq w]
      rw [hw]
    · intro hw
      rw [mem_fixedSubgroup] at hw ⊢
      apply (a g).injective
      rw [←show t ((a g) w) = (a g) (t w) from DFunLike.congr_fun (hcomm g).eq w]
      exact hw
  have hf : t.fixedSubgroup = ⊥ := by
    rcases Theory.GroupAction.irreducible_of_three_action_card_twentyfive hA hW hm
      t.fixedSubgroup with hb | hh
    · exact hb
    · exact (hne (MulEquiv.ext (fun w => (mem_fixedSubgroup t w).mp (hh.ge (mem_top w))))).elim
  intro w
  have hww : w * t w ∈ t.fixedSubgroup := by
    rw [mem_fixedSubgroup]
    rw [map_mul,show t (t w) = w from DFunLike.congr_fun ht w,mul_comm]
  exact mul_eq_one_iff_eq_inv.mp (by simpa only [mul_comm] using (show w * t w = 1 from hf.le hww))
end MulAut

namespace MonoidHom
variable {A W : Type*} [Group A] [Group W] [Finite W]

/-- A nontrivial coprime action is detected on the actual Frattini quotient. -/
theorem frattini_action_ne_one_of_coprime {p : ℕ} [Fact p.Prime]
    (hW : IsPGroup p W) (a : A →* MulAut W)
    (hc : Nat.Coprime (Nat.card A) p) (ha : a ≠ 1) :
    (quotientAut (frattini W)).comp a ≠ 1 := by
  intro he
  have hle : a.range ≤ (quotientAut (frattini W)).ker := by
    rintro _ ⟨g,rfl⟩
    exact DFunLike.congr_fun he g
  have hp := (isPGroup_quotientAut_frattini_kernel hW).to_le hle
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hcard : Nat.card a.range = 1 := Nat.eq_one_of_dvd_coprimes (hc.pow_right n)
    (card_dvd_of_surjective a.rangeRestrict a.rangeRestrict_surjective) (hn ▸ dvd_rfl)
  apply ha
  apply MonoidHom.ext
  intro g
  exact (card_eq_one.mp hcard).le (show a g ∈ a.range from ⟨g,rfl⟩)
end MonoidHom

namespace Theory.GroupAction
open Subgroup

/-- On an actual five-group Frattini plane, a nontrivial three-subgroup
is irreducible and a commuting nontrivial order-two subgroup inverts the plane.
Both actions are induced by the specified homomorphism. -/
theorem five_frattini_plane_action
    {K Y : Type*} [Group K] [Finite K] [Group Y] [Finite Y]
    (hY : IsPGroup 5 Y) (hcard : Nat.card (Y ⧸ frattini Y) = 25)
    (a : K →* MulAut Y) (P B : Subgroup K)
    (hP : IsPGroup 3 P) (hmP : P.map a ≠ ⊥)
    (hB : Nat.card B = 2) (hmB : B.map a ≠ ⊥)
    (hcomm : P ≤ centralizer (B : Set K)) :
    let b := (quotientAut (frattini Y)).comp a
    P.map b ≠ ⊥ ∧
      (∀ U : Subgroup (Y ⧸ frattini Y),
        (∀ p ∈ P, ∀ x ∈ U, b p x ∈ U) → U = ⊥ ∨ U = ⊤) ∧
      (∀ v : B, v ≠ 1 → ∀ x : Y ⧸ frattini Y, b v.val x = x⁻¹) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fact (IsPGroup 5 Y) := ⟨hY⟩
  let : IsElementaryAbelian 5 (Y ⧸ frattini Y) := isElementaryAbelian_quotient_frattini
  let b := (quotientAut (frattini Y)).comp a
  let c := b.comp P.subtype
  have haP : a.comp P.subtype ≠ 1 := by
    intro he
    apply hmP
    apply (Subgroup.map_eq_bot_iff _).mpr
    intro p hp
    exact DFunLike.congr_fun he ⟨p,hp⟩
  have hcop : Nat.Coprime (Nat.card P) 5 := by
    obtain ⟨n,hn⟩ := hP.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 5).pow_left n
  have hc : c ≠ 1 := MonoidHom.frattini_action_ne_one_of_coprime hY _ hcop haP
  have haB : a.comp B.subtype ≠ 1 := by
    intro he
    apply hmB
    apply (Subgroup.map_eq_bot_iff _).mpr
    intro v hv
    exact DFunLike.congr_fun he ⟨v,hv⟩
  let d := b.comp B.subtype
  have hd : d ≠ 1 := MonoidHom.frattini_action_ne_one_of_coprime hY _
    (by rw [hB]; decide) haB
  have hdinj : Function.Injective d := by
    let : Fact (Nat.card B).Prime := ⟨by rw [hB]; decide⟩
    apply (MonoidHom.ker_eq_bot_iff d).mp
    rcases d.ker.eq_bot_or_eq_top_of_prime_card with hbot | htop
    · exact hbot
    · exact (hd (MonoidHom.ext (fun v => htop.ge (mem_top v)))).elim
  refine ⟨?_,?_,?_⟩
  · intro he
    apply hc
    apply MonoidHom.ext
    intro p
    exact mem_bot.mp (he ▸ mem_map_of_mem b p.property)
  · intro U hU
    let : MulDistribMulAction P (Y ⧸ frattini Y) := MulDistribMulAction.compHom _ c
    let : IsInvariant P (Y ⧸ frattini Y) U := ⟨fun p x => ⟨hU p.val p.property x,
      fun hx => by
        have hh := hU (p⁻¹).val (p⁻¹).property (c p x) hx
        change c p⁻¹ (c p x) ∈ U at hh
        simpa only [←MulAut.mul_apply,←map_mul,inv_mul_cancel,map_one,MulAut.one_apply] using hh⟩⟩
    apply irreducible_of_three_action_card_twentyfive hP hcard _ U
    intro he
    apply hc
    ext p x
    exact (he.ge (mem_top x)) p
  · intro v hv
    apply MulAut.inverts_of_commuting_three_action_card_twentyfive hP hcard c hc (d v)
    · rw [←map_pow,show v ^ 2 = 1 from hB ▸ pow_card_eq_one',map_one]
    · exact fun he => hv (hdinj (he.trans (map_one d).symm))
    · intro p
      exact (show Commute v.val p.val from hcomm p.property v.val v.property).map b
end Theory.GroupAction
