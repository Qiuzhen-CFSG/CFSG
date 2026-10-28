module

public import Theory.SpecificGroups.Alternating.FiveLocalGeometry
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple
public import Theory.GroupTheory.OddInvolutionEndpointModels
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith

/-!
# Cubic normalizers in A₅

For every subgroup of order three in an actual A₅ carrier, its normalizer
is isomorphic to S₃ and is maximal. Simplicity bounds proper subgroup orders
by twelve. The Sylow-three congruence forces the normalizer to have order
six and excludes any proper overgroup of order twelve. An explicit even
permutation action of the dihedral group of order six gives the genuine
normalizer isomorphism; Sylow conjugacy transports it to every cubic subgroup.

Source: Aschbacher, *Sporadic Groups* (1994), 47.10, pp.266–267,
where the local vertex stabilizer K_X is identified with S₃.
-/

public section

open Subgroup
namespace alternatingGroup.FiveLocalGeometry

private theorem proper_card_le_twelve {H : Type*} [Group H] [Finite H]
    (e : H ≃* A5) (L : Subgroup H) (hL : L ≠ ⊤) : Nat.card L ≤ 12 := by
  let : IsSimpleGroup H := e.isSimpleGroup
  have hc : Nat.card H = 60 := (Nat.card_congr e.toEquiv).trans card
  have hi : 5 ≤ L.index := by
    by_contra hn
    apply hL
    apply Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt
    have hb := Nat.factorial_le (show L.index ≤ 4 by omega)
    rw [hc]
    norm_num [Nat.factorial] at hb ⊢
    omega
  have hp := L.card_mul_index
  rw [hc] at hp
  nlinarith

private theorem cubic_normalizer_ne_top {H : Type*} [Group H] [Finite H]
    (e : H ≃* A5) (P : Subgroup H) (hP : Nat.card P = 3) :
    normalizer (P : Set H) ≠ ⊤ := by
  let : IsSimpleGroup H := e.isSimpleGroup
  intro ht
  rcases (normalizer_eq_top_iff.mp ht).eq_bot_or_eq_top with hb | hb
  · rw [hb, card_bot] at hP
    omega
  · rw [hb, Nat.card_congr Subgroup.topEquiv.toEquiv,
      Nat.card_congr e.toEquiv, card] at hP
    omega

/-- Every subgroup of order three has a normalizer of order six. -/
theorem cubic_normalizer_card {H : Type*} [Group H] [Finite H]
    (e : H ≃* A5) (P : Subgroup H) (hP : Nat.card P = 3) :
    Nat.card (normalizer (P : Set H)) = 6 := by
  have hb := proper_card_le_twelve e _ (cubic_normalizer_ne_top e P hP)
  have hd := card_dvd_of_le P.le_normalizer
  rw [hP] at hd
  have hi := (normalizer (P : Set H)).card_mul_index
  rw [Nat.card_congr e.toEquiv, card] at hi
  let S : Sylow 3 H := Sylow.ofCard P
    (by rw [hP, Nat.card_congr e.toEquiv, card]; decide +kernel)
  have hs := card_sylow_modEq_one 3 H
  rw [S.card_eq_index_normalizer] at hs
  change (normalizer (P : Set H)).index % 3 = 1 % 3 at hs
  generalize Nat.card (normalizer (P : Set H)) = n at *
  interval_cases n <;> omega

/-- The cubic normalizer is a maximal proper subgroup of the actual A₅. -/
theorem cubic_normalizer_maximal {H : Type*} [Group H] [Finite H]
    (e : H ≃* A5) (P : Subgroup H) (hP : Nat.card P = 3) :
    normalizer (P : Set H) ⋖ ⊤ := by
  refine ⟨lt_top_iff_ne_top.mpr (cubic_normalizer_ne_top e P hP), ?_⟩
  intro L hNL hLt
  have hb := proper_card_le_twelve e L (ne_of_lt hLt)
  have hn := cubic_normalizer_card e P hP
  have hd := card_dvd_of_le hNL.le
  rw [hn] at hd
  have hL : Nat.card L = 12 := by
    have hne : Nat.card L ≠ 6 := by
      intro hc
      exact hNL.ne (eq_of_le_of_card_ge hNL.le (by omega))
    have hp : 0 < Nat.card L := Nat.card_pos
    omega
  have hPL := P.le_normalizer.trans hNL.le
  have hPc : Nat.card (P.subgroupOf L) = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hPL).toEquiv, hP]
  let S : Sylow 3 L := Sylow.ofCard (P.subgroupOf L)
    (by rw [hPc, hL]; decide +kernel)
  have hNc : Nat.card (normalizer (P.subgroupOf L : Set L)) = 6 := by
    rw [← subgroupOf_normalizer_eq hPL,
      Nat.card_congr (subgroupOfEquivOfLe hNL.le).toEquiv, hn]
  have hi := (normalizer (P.subgroupOf L : Set L)).card_mul_index
  rw [hNc, hL] at hi
  have hs := card_sylow_modEq_one 3 L
  rw [S.card_eq_index_normalizer] at hs
  change (normalizer (P.subgroupOf L : Set L)).index % 3 = 1 % 3 at hs
  omega

private def cubicCycle : A5 := ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel⟩

private def cubicFlip : A5 := ⟨Equiv.swap 0 1 * Equiv.swap 3 4, by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel⟩

private theorem cubicCycle_order : orderOf cubicCycle = 3 :=
  orderOf_eq_prime (by decide +kernel) (by decide +kernel)

private def cubicDihedralHom : DihedralGroup 3 →* A5 where
  toFun d := match d with
    | .r i => cubicCycle ^ i.val
    | .sr i => cubicFlip * cubicCycle ^ i.val
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

private theorem cubicDihedralHom_injective : Function.Injective cubicDihedralHom := by
  have hi : Function.Injective (fun d : DihedralGroup 3 =>
      ((cubicDihedralHom d).val 0, (cubicDihedralHom d).val 1)) := by decide +kernel
  intro d e h
  exact hi (congrArg (fun g : A5 => (g.val 0, g.val 1)) h)

private theorem cubicFlip_normalizes :
    cubicFlip ∈ normalizer (zpowers cubicCycle : Set A5) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [MonoidHom.map_zpowers]
  have hi : cubicFlip * cubicCycle * cubicFlip⁻¹ = cubicCycle⁻¹ := by decide +kernel
  change zpowers (cubicFlip * cubicCycle * cubicFlip⁻¹) = _
  rw [hi, zpowers_inv]

private theorem cubicDihedralHom_range :
    cubicDihedralHom.range = normalizer (zpowers cubicCycle : Set A5) := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨d, rfl⟩
    have hc := (zpowers cubicCycle).le_normalizer (mem_zpowers cubicCycle)
    cases d with
    | r i => exact pow_mem hc i.val
    | sr i => exact mul_mem cubicFlip_normalizes (pow_mem hc i.val)
  · rw [cubic_normalizer_card (MulEquiv.refl A5) (zpowers cubicCycle)
      (by rw [Nat.card_zpowers, cubicCycle_order])]
    rw [← Nat.card_congr (MonoidHom.ofInjective cubicDihedralHom_injective).toEquiv,
      Nat.card_eq_fintype_card, DihedralGroup.card]

private theorem cubicCycle_normalizer_equiv :
    Nonempty (normalizer (zpowers cubicCycle : Set A5) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨e⟩ := Theory.GroupTheory.nonempty_dihedralThreeEquivPerm
  exact ⟨(MulEquiv.subgroupCongr cubicDihedralHom_range.symm).trans
    ((MonoidHom.ofInjective cubicDihedralHom_injective).symm.trans e)⟩

/-- The full cubic normalizer, with its genuine multiplication, is S₃. -/
theorem cubic_normalizer_equiv {H : Type*} [Group H] [Finite H]
    (e : H ≃* A5) (P : Subgroup H) (hP : Nat.card P = 3) :
    Nonempty (normalizer (P : Set H) ≃* Equiv.Perm (Fin 3)) := by
  have hPe : Nat.card (P.map e.toMonoidHom) = 3 := by
    rw [card_map_of_injective e.injective, hP]
  obtain ⟨g, hg⟩ := cubic_conjugate (MulEquiv.refl A5) (P.map e.toMonoidHom)
    (zpowers cubicCycle) hPe (by rw [Nat.card_zpowers, cubicCycle_order])
  let a : H ≃* A5 := e.trans (MulAut.conj g)
  have ha : P.map a.toMonoidHom = zpowers cubicCycle := by
    rw [map_map] at hg
    exact hg
  have hn : (normalizer (P : Set H)).map a.toMonoidHom =
      normalizer (zpowers cubicCycle : Set A5) := by
    rw [map_equiv_normalizer_eq, ha]
  obtain ⟨f⟩ := cubicCycle_normalizer_equiv
  exact ⟨(equivMapOfInjective _ a.toMonoidHom a.injective).trans
    ((MulEquiv.subgroupCongr hn).trans f)⟩

end alternatingGroup.FiveLocalGeometry
