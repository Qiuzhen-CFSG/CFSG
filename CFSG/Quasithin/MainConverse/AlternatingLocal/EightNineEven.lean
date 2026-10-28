module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.MainConverse.Transport
public import CFSG.Quasithin.MainConverse.AlternatingLocal.EightNineEven.Eight
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Perm.Option
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Even characteristic in A₈ and A₉

The imported A₈ calculation transports condition E along the constructed
exceptional equivalence A₈ ≃ PSL₄(2), using the binary parabolic calculation.
We prove the A₉ case by descent to an eight-point stabilizer, then transport
both results to isomorphic copies.

The regular translation action of the binary three-space embeds in A₈. Extend
it by one fixed point and choose a Sylow two-subgroup T containing it. Since T
acts on nine points, it fixes a point; transitivity on the original eight points
forces this to be the added point.

If a nonidentity two-subgroup Q is normalized by T, then Q ≤ T. Its fixed-point
set is T-invariant, and faithfulness excludes all nine points, so it consists
of precisely the added point. Thus N(Q) lies in that point stabilizer, which
is actually isomorphic to A₈. Maximality among two-locals descends to the
stabilizer, so condition E in A₈ supplies exactly the required local condition
in A₉. No characteristic-two-type assertion for all A₉ two-locals is used.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, Theorem
0.1.2(3), printed pp.3–4, repeated pp.481–482. The small translation calculation
adapts `GLS3.Chapter5.PRank.exists_regularEightTranslationSubgroup` from
`Theory/Alternating/proposition_5_2_9_10.lean` under narrow imports.
-/

namespace CFSG.Quasithin.MainConverse

open Subgroup

variable {G : Type*} [Group G]

private theorem maximal_local_subgroupOf {M H : Subgroup G}
    (hM : IsMaximalTwoLocal M) (hMH : M ≤ H) :
    IsMaximalTwoLocal (M.subgroupOf H) := by
  obtain ⟨Q, hQ, hp, hMQ⟩ := hM.1
  have hQH : Q ≤ H := Q.le_normalizer.trans (hMQ ▸ hMH)
  have hlocal : IsTwoLocal (M.subgroupOf H) := by
    refine ⟨Q.subgroupOf H, ?_, hp.comap_subtype, ?_⟩
    · intro hbot
      have := congrArg (fun R : Subgroup H => R.map H.subtype) hbot
      rw [map_subgroupOf_eq_of_le hQH, Subgroup.map_bot] at this
      exact hQ this
    · rw [hMQ, subgroupOf_normalizer_eq hQH]
  refine ⟨hlocal, ?_⟩
  rintro K ⟨R, hR, hpR, rfl⟩ hMK
  have hlift : IsTwoLocal (normalizer (R.map H.subtype : Set G)) :=
    ⟨R.map H.subtype, fun hb => hR
      ((map_eq_bot_iff_of_injective R H.subtype_injective).mp hb), hpR.map _, rfl⟩
  have hMN : M ≤ normalizer (R.map H.subtype : Set G) := by
    have h := (map_mono (f := H.subtype) hMK).trans (R.le_normalizer_map H.subtype)
    rwa [map_subgroupOf_eq_of_le hMH] at h
  have hNM := hM.2 hlift hMN
  intro x hx
  exact hNM (R.le_normalizer_map H.subtype (mem_map_of_mem H.subtype hx))

private theorem even_at_descent [Finite G] (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hH : IsEvenCharacteristic H)
    (hN : ∀ Q : Subgroup G, Q ≠ ⊥ → IsPGroup 2 Q →
      (T : Subgroup G) ≤ normalizer (Q : Set G) → normalizer (Q : Set G) ≤ H) :
    IsEvenCharacteristicAt T := by
  intro M hM hTM
  have hMH : M ≤ H := by
    obtain ⟨Q, hQ, hpQ, rfl⟩ := hM.1
    exact hN Q hQ hpQ hTM
  have hh := hH (T.subtype hTH) (M.subgroupOf H)
    (maximal_local_subgroupOf hM hMH) (fun _ hx => hTM hx)
  exact hh.of_equiv (subgroupOfEquivOfLe hMH)

private theorem pgroup_le_sylow_of_normalized {p : ℕ} (T : Sylow p G)
    (Q : Subgroup G) (hpQ : IsPGroup p Q)
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G)) : Q ≤ T := by
  have hp : IsPGroup p (Q.subgroupOf (normalizer (Q : Set G))) := hpQ.comap_subtype
  have h := hp.le_sylow_of_normal (T.subtype hTQ)
  intro q hq
  exact h (show (⟨q, Q.le_normalizer hq⟩ : normalizer (Q : Set G)) ∈
    Q.subgroupOf (normalizer (Q : Set G)) from hq)

private theorem normalizer_moves_fixed {α : Type*} [MulAction G α]
    (Q : Subgroup G) {x : α} (hx : ∀ q : Q, q • x = x)
    {g : G} (hg : g ∈ normalizer (Q : Set G)) :
    ∀ q : Q, q • (g • x) = g • x := by
  intro q
  have hq : g⁻¹ * q * g ∈ Q := by
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp ((normalizer (Q : Set G)).inv_mem hg) q).mp q.property
  have hh := congrArg (fun y : α => g • y) (hx ⟨g⁻¹ * q * g, hq⟩)
  change (q : G) • (g • x) = g • x
  simpa only [Subgroup.mk_smul, mul_smul, smul_inv_smul] using hh

private theorem unique_fixed_of_transitive_complement {α : Type*} [MulAction G α]
    [FaithfulSMul G α] (S Q : Subgroup G) (x : α)
    (hQ : Q ≠ ⊥) (hQS : Q ≤ S) (hSN : S ≤ normalizer (Q : Set G))
    (hfix : ∀ s : S, s • x = x)
    (htrans : ∀ y z : α, y ≠ x → z ≠ x → ∃ s : S, s • y = z) :
    ∀ y : α, (∀ q : Q, q • y = y) ↔ y = x := by
  intro y
  constructor
  · intro hy
    by_contra hyx
    apply hQ
    apply eq_bot_iff.mpr
    intro q hq
    apply mem_bot.mpr
    apply eq_of_smul_eq_smul (α := α)
    intro z
    simp only [one_smul]
    by_cases hzx : z = x
    · subst z
      exact hfix ⟨q, hQS hq⟩
    · obtain ⟨s, hs⟩ := htrans y z hyx hzx
      rw [← hs]
      exact normalizer_moves_fixed Q hy (hSN s.property) ⟨q, hq⟩
  · rintro rfl q
    exact hfix ⟨q, hQS q.property⟩

private theorem normalizer_le_point_stabilizer {α : Type*} [MulAction G α]
    (Q : Subgroup G) (x : α)
    (hfixed : ∀ y : α, (∀ q : Q, q • y = y) ↔ y = x) :
    normalizer (Q : Set G) ≤ MulAction.stabilizer G x := by
  intro g hg
  exact (hfixed (g • x)).mp (normalizer_moves_fixed Q ((hfixed x).mpr rfl) hg)

private abbrev A8 := alternatingGroup (Fin 8)
private abbrev A9o := alternatingGroup (Option (Fin 8))

private def extend : A8 →* A9o where
  toFun g := ⟨g.val.optionCongr, by
    simpa only [Equiv.Perm.mem_alternatingGroup, Equiv.optionCongr_sign] using g.property⟩
  map_one' := by apply Subtype.ext; exact Equiv.optionCongr_one
  map_mul' g h := by
    apply Subtype.ext
    ext x
    cases x <;> rfl

private theorem extend_injective : Function.Injective extend := by
  intro g h he
  apply Subtype.ext
  exact Equiv.optionCongr_injective (congrArg Subtype.val he)

private def extendStabilizer : A8 →* MulAction.stabilizer A9o (none : Option (Fin 8)) :=
  extend.codRestrict _ (fun _ => rfl)

private theorem extendStabilizer_bijective : Function.Bijective extendStabilizer := by
  refine ⟨fun _ _ h => extend_injective (congrArg Subtype.val h), ?_⟩
  intro g
  have hgfix : g.val.val none = none := g.property
  have hg : (Equiv.removeNone g.val.val).optionCongr = g.val.val := by
    rw [map_equiv_removeNone, hgfix, Equiv.swap_self]
    rfl
  have hsign : Equiv.Perm.sign (Equiv.removeNone g.val.val) = 1 := by
    rw [← Equiv.optionCongr_sign, hg]
    exact Equiv.Perm.mem_alternatingGroup.mp g.val.property
  refine ⟨⟨Equiv.removeNone g.val.val, Equiv.Perm.mem_alternatingGroup.mpr hsign⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hg

private noncomputable def stabilizerEquiv :
    MulAction.stabilizer A9o (none : Option (Fin 8)) ≃* A8 :=
  (MulEquiv.ofBijective extendStabilizer extendStabilizer_bijective).symm

private theorem exists_transitive_two_subgroup :
    ∃ B : Subgroup A8, IsPGroup 2 B ∧ ∀ x y : Fin 8, ∃ b : B, b • x = y := by
  let V := Fin 3 → ZMod 2
  let transHom : Multiplicative V →* Equiv.Perm V := {
    toFun := fun a => AddAction.toPerm a.toAdd
    map_one' := by ext x; simp [AddAction.toPerm_apply]
    map_mul' := by intro a b; ext x; simp [AddAction.toPerm_apply, add_assoc] }
  have hsquare : ∀ a : Multiplicative V, a ^ 2 = 1 := by
    intro a
    rw [pow_two]
    change a.toAdd + a.toAdd = (0 : V)
    funext i
    change a.toAdd i + a.toAdd i = 0
    have htwo : (2 : ZMod 2) = 0 := by decide
    linear_combination a.toAdd i * htwo
  have hsign : ∀ a : Multiplicative V, Equiv.Perm.sign (transHom a) = 1 := by
    intro a
    by_cases ha : a = 1
    · simp [ha]
    · have ha0 : a.toAdd ≠ 0 := ha
      have hs : (transHom a) ^ 2 = 1 := by rw [← map_pow, hsquare, map_one]
      rw [Equiv.Perm.sign_of_pow_two_eq_one hs]
      have hfixed : Fintype.card (Function.fixedPoints (transHom a)) = 0 := by
        rw [Fintype.card_eq_zero_iff]
        refine ⟨fun x => ha0 ?_⟩
        have hx : a.toAdd + x.val = x.val := x.property
        exact add_right_cancel (show a.toAdd + x.val = 0 + x.val by simpa using hx)
      rw [hfixed]
      norm_num [V, pow_succ]
  let altTransHom := transHom.codRestrict (alternatingGroup V)
    (fun a => Equiv.Perm.mem_alternatingGroup.mpr (hsign a))
  let e : V ≃ Fin 8 := Fintype.equivFinOfCardEq (by simp [V])
  let f : Multiplicative V →* A8 := e.altCongrHom.toMonoidHom.comp altTransHom
  have hp : IsPGroup 2 (Multiplicative V) := IsPGroup.of_card (n := 3) (by
    change Nat.card V = 2 ^ 3
    simp [V, Nat.card_eq_fintype_card])
  refine ⟨f.range, ?_, ?_⟩
  · rw [MonoidHom.range_eq_map]
    exact (hp.to_subgroup ⊤).map f
  · intro x y
    let a : Multiplicative V := Multiplicative.ofAdd (e.symm y - e.symm x)
    refine ⟨⟨f a, ⟨a, rfl⟩⟩, ?_⟩
    change e ((e.symm y - e.symm x) + e.symm x) = y
    simp

private theorem exists_sylow_fixing_none :
    ∃ T : Sylow 2 A9o,
      (∀ t : T, t • (none : Option (Fin 8)) = none) ∧
      ∀ x y : Fin 8, ∃ t : T, t • some x = some y := by
  obtain ⟨B, hpB, htrans⟩ := exists_transitive_two_subgroup
  obtain ⟨T, hBT⟩ := (hpB.map extend).exists_le_sylow
  have hTtrans : ∀ x y : Fin 8, ∃ t : T, t • some x = some y := by
    intro x y
    obtain ⟨b, hb⟩ := htrans x y
    refine ⟨⟨extend b, hBT (mem_map_of_mem extend b.property)⟩, ?_⟩
    change some (b.val.val x) = some y
    exact congrArg some hb
  obtain ⟨x, hx⟩ := T.isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card
    (Option (Fin 8)) (by norm_num [Nat.card_eq_fintype_card])
  have hxnone : x = none := by
    cases x with
    | none => rfl
    | some x =>
      obtain ⟨y, hy⟩ := exists_ne x
      obtain ⟨t, ht⟩ := hTtrans x y
      have hh : some y = some x := ht.symm.trans (hx t)
      exact (hy (Option.some.inj hh)).elim
  subst x
  exact ⟨T, hx, hTtrans⟩

/-- Condition E for A₈ implies condition E for A₉ via its eight-point stabilizer.
The unconditional theorem below supplies the separate A₈ calculation. -/
public theorem alternatingNine_evenCharacteristic_of_eight
    (h8 : IsEvenCharacteristic (alternatingGroup (Fin 8))) :
    IsEvenCharacteristic (alternatingGroup (Fin 9)) := by
  have hoption : IsEvenCharacteristic A9o := by
    obtain ⟨T, hfix, htrans⟩ := exists_sylow_fixing_none
    apply IsEvenCharacteristicAt.all (T := T)
    have hTH : (T : Subgroup A9o) ≤ MulAction.stabilizer A9o (none : Option (Fin 8)) := by
      intro t ht
      exact hfix ⟨t, ht⟩
    apply even_at_descent T _ hTH (h8.of_equiv stabilizerEquiv.symm)
    intro Q hQ hpQ hTQ
    apply normalizer_le_point_stabilizer Q none
    apply unique_fixed_of_transitive_complement (T : Subgroup A9o) Q none
      hQ (pgroup_le_sylow_of_normalized T Q hpQ hTQ) hTQ hfix
    intro x y hx hy
    cases x with
    | none => exact (hx rfl).elim
    | some x =>
      cases y with
      | none => exact (hy rfl).elim
      | some y => exact htrans x y
  let e : Option (Fin 8) ≃ Fin 9 := Fintype.equivFinOfCardEq (by simp)
  exact hoption.of_equiv e.altCongrHom

/-- Transport the A₉ reduction along an actual multiplicative equivalence. -/
public theorem alternatingNine_evenCharacteristic_of_eight_of_iso
    {H : Type*} [Group H] [Finite H]
    (h8 : IsEvenCharacteristic (alternatingGroup (Fin 8)))
    (e : H ≃* alternatingGroup (Fin 9)) : IsEvenCharacteristic H :=
  CFSG.Quasithin.MainConverse.evenCharacteristic_of_model_equiv e
    (alternatingNine_evenCharacteristic_of_eight h8)

/-- Condition E for every group actually isomorphic to A₈. -/
public theorem alternatingEight_evenCharacteristic_of_iso
    {H : Type*} [Group H] [Finite H]
    (e : H ≃* alternatingGroup (Fin 8)) : IsEvenCharacteristic H :=
  evenCharacteristic_of_model_equiv e alternatingEight_evenCharacteristic

/-- The actual alternating group on nine points satisfies source condition E. -/
public theorem alternatingNine_evenCharacteristic :
    IsEvenCharacteristic (alternatingGroup (Fin 9)) :=
  alternatingNine_evenCharacteristic_of_eight alternatingEight_evenCharacteristic

/-- Condition E for every group actually isomorphic to A₉. -/
public theorem alternatingNine_evenCharacteristic_of_iso
    {H : Type*} [Group H] [Finite H]
    (e : H ≃* alternatingGroup (Fin 9)) : IsEvenCharacteristic H :=
  evenCharacteristic_of_model_equiv e alternatingNine_evenCharacteristic

end CFSG.Quasithin.MainConverse
