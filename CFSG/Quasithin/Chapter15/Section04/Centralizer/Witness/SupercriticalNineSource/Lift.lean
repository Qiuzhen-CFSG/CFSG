module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.Lifting
public import CFSG.Quasithin.Chapter3.Section02.SourceXiSigns
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.Frattini.OmegaProducts

/-!
# Normal residual lifts with their source quotient actions

A normal two-perfect subgroup P of M/O₂(M) has a normal residual lift Y.
The intrinsic quotient Y/O₂(Y) identifies with P through the original
quotient map. The same marking intertwines ambient conjugation and both
stages of the source Frattini action. In particular a cubic actor on P
gives a cubic element of the full N_G(Y)-automizer of Y/O₂(Y).

Source: the supercritical lifts in Aschbacher--Smith 15.4.10, printed p.1159,
and Definition 3.2.12, printed p.584.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.SupercriticalNineSource
open FamilySource
variable {G : Type*} [Group G] [Finite G]

/-- Normal residual lifts have the literal intrinsic two-core quotient P. -/
theorem normal_lift_quotient (M : Subgroup G) (P : Subgroup (CoreQuotient M))
    [P.Normal] (hp : IsPPerfect 2 P) :
    ∃ e : Chapter1.XiQuotient (lift M P) ≃* P,
      ∀ y : lift M P,
        (e (QuotientGroup.mk' (pCore 2 (lift M P)) y) : CoreQuotient M) =
          quotientMap M ⟨(y : G), lift_le M P y.property⟩ := by
  let Y := lift M P
  have hYM : Y ≤ M := lift_le M P
  have hn : M ≤ normalizer (Y : Set G) :=
    lift_normalized M M le_rfl P (by rw [normalizer_eq_top]; exact le_top)
  let : (Y.subgroupOf M).Normal := (normal_subgroupOf_iff_le_normalizer hYM).mpr hn
  let f := (subgroupOfEquivOfLe hYM).symm
  let e := (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans
    ((coreQuotientEquivImage 2 (Y.subgroupOf M)).trans
      (MulEquiv.subgroupCongr (image_lift M P hp)))
  refine ⟨e, ?_⟩
  intro y
  change ((coreQuotientEquivImage 2 (Y.subgroupOf M))
    (QuotientGroup.mk' (pCore 2 (Y.subgroupOf M)) (f y)) : CoreQuotient M) = _
  exact coreQuotientEquivImage_apply_mk 2 (Y.subgroupOf M) (f y)

omit [Finite G] in
/-- A marking by the original map intertwines the intrinsic normalizer action. -/
theorem normal_lift_action_compatible (M : Subgroup G) (P : Subgroup (CoreQuotient M))
    [P.Normal]
    (e : Chapter1.XiQuotient (lift M P) ≃* P)
    (he : ∀ y : lift M P,
      (e (QuotientGroup.mk' (pCore 2 (lift M P)) y) : CoreQuotient M) =
        quotientMap M ⟨(y : G), lift_le M P y.property⟩)
    (m : M) (hm : (m : G) ∈ normalizer (lift M P : Set G))
    (v : Chapter1.XiQuotient (lift M P)) :
    e (Chapter3.xiQuotientNormalizerAction (lift M P) ⟨m, hm⟩ v) =
      MulAut.conjNormal (quotientMap M m) (e v) := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (lift M P)) v
  apply Subtype.ext
  change (e (quotientAut (pCore 2 (lift M P))
    ((lift M P).normalizerMonoidHom ⟨m, hm⟩)
      (QuotientGroup.mk' (pCore 2 (lift M P)) y)) : CoreQuotient M) = _
  rw [quotientAut_apply_mk, he, MulAut.conjNormal_apply, he]
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

/-- The actual order-three M-actor gives a cubic element of the full ambient
automizer of the intrinsic quotient, using the original quotient marking. -/
theorem three_dvd_lift_automizer (M : Subgroup G) (P : Subgroup (CoreQuotient M))
    [P.Normal] (hp : IsPPerfect 2 P) (m : M)
    (hm : orderOf (MulAut.conjNormal (quotientMap M m) : MulAut P) = 3) :
    3 ∣ Nat.card (Chapter3.xiQuotientAutomizer (lift M P)) := by
  obtain ⟨e, he⟩ := normal_lift_quotient M P hp
  have hn : M ≤ normalizer (lift M P : Set G) :=
    lift_normalized M M le_rfl P (by rw [normalizer_eq_top]; exact le_top)
  let n : normalizer (lift M P : Set G) := ⟨m, hn m.property⟩
  have ha : MulAut.congr e (Chapter3.xiQuotientNormalizerAction (lift M P) n) =
      MulAut.conjNormal (quotientMap M m) := by
    apply MulEquiv.ext
    intro p
    obtain ⟨v, rfl⟩ := e.surjective p
    change e (Chapter3.xiQuotientNormalizerAction (lift M P) n (e.symm (e v))) = _
    rw [e.symm_apply_apply]
    exact normal_lift_action_compatible M P e he m (hn m.property) v
  apply Chapter3.three_dvd_xiQuotientAutomizer_of_actor (lift M P) n
  rw [← (MulAut.congr e).orderOf_eq, ha, hm]

/-- A prime-five residual lift with uppercase membership and a cubic actor
belongs to the actual source positive family. -/
theorem five_lift_mem_XiPlus (T M : Subgroup G) (P : Subgroup (CoreQuotient M))
    [P.Normal] (hp : IsPPerfect 2 P) (h5 : 5 ∣ Nat.card P)
    (hXi : lift M P ∈ Chapter1.Xi G T) (m : M)
    (hm : orderOf (MulAut.conjNormal (quotientMap M m) : MulAut P) = 3) :
    lift M P ∈ Chapter3.XiPlus G T := by
  obtain ⟨e, _⟩ := normal_lift_quotient M P hp
  have h5q : 5 ∣ Nat.card (Chapter1.XiQuotient (lift M P)) :=
    (Nat.card_congr e.toEquiv).symm ▸ h5
  exact Chapter3.mem_XiPlus_of_five_dvd_of_three_dvd_automizer hXi
    (h5q.trans (card_quotient_dvd_card (pCore 2 (lift M P))))
    (three_dvd_lift_automizer M P hp m hm)

end CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.SupercriticalNineSource
