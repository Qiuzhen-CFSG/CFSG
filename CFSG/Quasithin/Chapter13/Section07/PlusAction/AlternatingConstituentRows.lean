module
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OddFFRows
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.RankOneConstituent

/-!
# An alternating constituent excludes the remaining rank-one kernel row

The actual alternating-five constituent rules out the natural SL₂ row of
B.5.6. A component of order 60 cannot be SL₃ over a binary field, since its
unipotent subgroup has order divisible by eight. The remaining deleted
permutation row is incompatible with the commuting fixed-free cubic.

This comparison keeps the constituent's actor injection and the literal
component inside the offender subgroup. Its source consumer is the remaining
alternating-five branch in 13.7.4(1), printed pp.937–938.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.OddFFRows
open ChapterB.QuasisimpleSource ChapterB.SourceInduction

private theorem not_slThree_card60 (F : BinaryField)
    (hc : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) = 60) : False := by
  have hd := (Matrix.PSL3.LinearThree.unipotentSL F.Carrier).card_subgroup_dvd_card
  rw [Matrix.PSL3.LinearThree.card_unipotentSL, F.card_eq, hc, ← pow_mul] at hd
  have hp := F.degree_pos
  have h8 : 8 ∣ 60 :=
    (Nat.pow_dvd_pow 2 (show 3 ≤ F.degree * 3 by omega)).trans hd
  norm_num at h8

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- An actual deleted-permutation constituent excludes all B.5 rank-one rows
for an order-sixty component commuting with a fixed-free cubic. -/
theorem not_alternatingFive_constituent_of_commuting_cubic
    {E : Subgroup G} {C : Subgroup E} [C.Normal] [IsQuasisimple C]
    (hfaith : Function.Injective ρ) (hcore : pCore 2 E = ⊥)
    (cover : SQTKQuotient KnownSimple.IsKnownSimple E)
    (hCN : C ≤ offenderSubgroup (ρ.comp E.subtype)) (hr : primeRank 3 E ≤ 1)
    (hwhole : moved (ρ.comp E.subtype) C = ⊤) (hcard : Nat.card C = 60)
    (f : alternatingGroup (Fin 5) →* C) (hf : Function.Injective f)
    (i : BinaryPermutation.natural (Fin 5) →+ V) (hi : Function.Injective i)
    (hact : ∀ a v, i (alternatingNatural 5 a v) = ρ (f a : G) (i v))
    (z : G) (hz : z ^ 3 = 1)
    (hcomm : ∀ c : C, z * (c : G) = (c : G) * z)
    (hfix : ∀ v, ρ z v = v → v = 0) : False := by
  let σ := ρ.comp E.subtype
  let N := offenderSubgroup σ
  let L := C.subgroupOf N
  obtain ⟨c,hc⟩ := component_rankOne_rows σ
    (hfaith.comp E.subtype_injective) hcore cover hCN hr
  let s := c.sectionData
  have hspace : s.space.toSubmodule = ⊤ := by
    rw [s.space_eq]
    change subspaceCommutator (σ.comp N.subtype) ⊤ L = ⊤
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hCN]
    exact hwhole
  have hcardL : Nat.card L = 60 :=
    (Nat.card_congr (subgroupOfEquivOfLe hCN).toEquiv).trans hcard
  let j : C ≃* L := (subgroupOfEquivOfLe hCN).symm
  let f' := j.toMonoidHom.comp f
  have hf' : Function.Injective f' := j.injective.comp hf
  have ha' : ∀ a v, i (alternatingNatural 5 a v) = (σ.comp N.subtype) (f' a) (i v) :=
    hact
  cases hc with
  | irreducible _ _ _ hc _ =>
    cases hc with
    | linearTwo F _ e _ _ =>
      exact RankOneConstituent.not_linearTwo_of_alternating_injection s F e f' hf' i hi ha'
    | linearThree F _ _ e _ =>
      exact not_slThree_card60 F ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hcardL)
    | symmetricFive e _ _ =>
      let a : ActionEquiv (s.action.comp L.subtype) (alternatingNatural 5) := {
        groupEquiv := e.subgroupEquiv
        linearEquiv := e.action.linearEquiv
        intertwines := by
          intro g v
          have hh := e.action.intertwines ⟨g,e.contained g.property⟩ v
          rw [e.compatible] at hh
          exact hh }
      exact not_alternatingFive_central_quotient_of_commuting_cubic ρ
        (E.subtype.comp N.subtype) s hspace a z hz
        (fun l => hcomm ((subgroupOfEquivOfLe hCN) l)) hfix
  | doubleThree F _ _ e _ _ =>
    exact not_slThree_card60 F ((Nat.card_congr e.groupEquiv.toEquiv).symm.trans hcardL)

/-- The original component inclusion supplies the same contradiction. The
three-rank bound follows from its two-group quotient and order sixty. -/
theorem not_ambient_alternatingFive_constituent_of_commuting_cubic
    {E C : Subgroup G} [C.Normal] [IsQuasisimple C] (hCE : C ≤ E)
    (hfaith : Function.Injective ρ) (hcore : pCore 2 E = ⊥)
    (cover : SQTKQuotient KnownSimple.IsKnownSimple E)
    (hCN : C.subgroupOf E ≤ offenderSubgroup (ρ.comp E.subtype))
    (hquot : IsPGroup 2 (E ⧸ C.subgroupOf E))
    (hwhole : moved ρ C = ⊤) (hcard : Nat.card C = 60)
    (f : alternatingGroup (Fin 5) →* C) (hf : Function.Injective f)
    (i : BinaryPermutation.natural (Fin 5) →+ V) (hi : Function.Injective i)
    (hact : ∀ a v, i (alternatingNatural 5 a v) = ρ (f a : G) (i v))
    (z : G) (hz : z ^ 3 = 1)
    (hcomm : ∀ c : C, z * (c : G) = (c : G) * z)
    (hfix : ∀ v, ρ z v = v → v = 0) : False := by
  let e := subgroupOfEquivOfLe hCE
  let : IsQuasisimple (C.subgroupOf E) := IsQuasisimple.of_mulEquiv e.symm
  have hcard' : Nat.card (C.subgroupOf E) = 60 := (Nat.card_congr e.toEquiv).trans hcard
  have hrC : primeRank 3 (C.subgroupOf E) ≤ 1 := by
    obtain ⟨P,hP,hPc⟩ := exists_elementaryAbelian_card_primeRank
      (G := C.subgroupOf E) (p := 3)
    have hd : 3 ^ primeRank 3 (C.subgroupOf E) ∣ 60 :=
      hcard' ▸ hPc ▸ P.card_subgroup_dvd_card
    by_contra hn
    have h9 : 9 ∣ 60 :=
      (Nat.pow_dvd_pow 3 (show 2 ≤ primeRank 3 (C.subgroupOf E) by omega)).trans hd
    norm_num at h9
  have hr : primeRank 3 E ≤ 1 :=
    (primeRank_le_of_normal_two_quotient (C.subgroupOf E) hquot 3 (by decide)).trans hrC
  have hm : moved (ρ.comp E.subtype) (C.subgroupOf E) = ⊤ := by
    change subspaceCommutator (ρ.comp E.subtype) ⊤ (C.subgroupOf E) = ⊤
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hCE]
    exact hwhole
  exact not_alternatingFive_constituent_of_commuting_cubic ρ hfaith hcore cover hCN hr
    hm hcard' (e.symm.toMonoidHom.comp f) (e.symm.injective.comp hf) i hi hact
    z hz (fun c => hcomm (e c)) hfix

end CFSG.Quasithin.Chapter13.Section07.PlusAction.OddFFRows
