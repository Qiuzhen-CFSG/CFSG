module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryCover
public import Theory.GroupTheory.TwoPerfectElementaryIndexTwo

/-!
# The whole elementary core in the nonnormal unitary branch

Let R = O₂(J) and N = K ∩ R for the actual proper unitary overcomponent.
The source intersection N is elementary of order q³ and has index at most
two in R. The faithful natural section on R/Φ(R) bounds |Φ(R)| by two.
If Φ(R) were nontrivial, that section would exhaust R/Φ(R), making the
original action irreducible. But a perfect group preserves every elementary
index-two subgroup of a non-elementary group. Thus N would give a proper
nonzero invariant subspace, a contradiction. Hence the whole R is elementary.

In either ordinary unitary orientation, the previously proved R ≤ O₂(K)
gives R = N. Its order q³ identifies the whole original core action as
natural or dual for J/R = SL₃(q), with the actual quotient isomorphism.
The degree-two extension is included in elementary-core recognition; its
whole moved-core identification and the second-parabolic contradiction
remain required. No equality between the extended overlap core and O₂(K)
is used.

The Chapter12 companion applies these results to the same prepared pair,
retaining all original quotient maps, orders and Sylow data.
Source: Aschbacher–Smith 5.2.8, printed pp.652–653 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryMoved

variable {G : Type*} [Group G] [Finite G]

/-- The actual core is elementary: otherwise its elementary subgroup of
index two is invariant, contradicting the full natural Frattini section. -/
theorem elementary_core [Group.IsPerfect G]
    {h : HasCharacteristicTwo G} {m : ℕ} (hm : 1 ≤ m)
    (d : UnitaryCover.NaturalCoreSection h m)
    (hc : Nat.card (pCore 2 G) ≤ 2*(2^m)^3)
    (A : Subgroup (pCore 2 G)) (hA : IsElementaryAbelian 2 A)
    (hAc : Nat.card A = (2^m)^3) (hAi : A.index ≤ 2) :
    IsElementaryAbelian 2 (pCore 2 G) := by
  by_contra hne
  have hphine : frattini (pCore 2 G) ≠ ⊥ := fun hz =>
    hne ((frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hz)
  let := d.irreducible_of_frattini_ne_bot hc hphine
  have hAt : A ≠ ⊤ := by
    intro he
    let : IsElementaryAbelian 2 (⊤ : Subgroup (pCore 2 G)) := he ▸ hA
    have hE : IsElementaryAbelian 2 (pCore 2 G) := IsElementaryAbelian.of_injective
      (topEquiv (G := pCore 2 G)).symm.toMonoidHom
      (topEquiv (G := pCore 2 G)).symm.injective
    apply hne
    exact hE
  have hi : A.index = 2 := by
    have hpos := Nat.pos_of_ne_zero (index_ne_zero_of_finite (H := A))
    have hnot := mt index_eq_one.mp hAt
    omega
  have hperfect : IsPPerfect 2 G := by
    intro N hN hq
    let : N.Normal := hN
    by_contra hnt
    let : Nontrivial (G ⧸ N) := QuotientGroup.nontrivial_iff.mpr hnt
    let : Group.IsPerfect (G ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    exact Group.IsPerfect.not_isNilpotent (G ⧸ N) hq.isNilpotent
  have hfix (g : G) : (MulAut.conjNormal g : MulAut (pCore 2 G)) • A = A :=
    twoPerfect_fixes_elementary_index_two hperfect MulAut.conjNormal A hA hi hne g
  let E := (pCore 2 G) ⧸ frattini (pCore 2 G)
  let q := QuotientGroup.mk' (frattini (pCore 2 G))
  let i : Subgroup E ≃o Submodule (ZMod 2) (UnitaryCover.CoreSpace G) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)
  let W : Subrepresentation (UnitaryCover.frattiniAction h) := {
    toSubmodule := i (A.map q)
    apply_mem_toSubmodule := by
      intro g v hv
      obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 G) g
      change v.toMul ∈ A.map q at hv
      obtain ⟨a,ha,hav⟩ := hv
      have hav' : v = Additive.ofMul (q a) := congrArg Additive.ofMul hav.symm
      rw [hav',UnitaryCover.frattiniAction_apply]
      change quotientAut (frattini (pCore 2 G)) (MulAut.conjNormal g) (q a) ∈ A.map q
      refine ⟨MulAut.conjNormal g a,?_,(quotientAut_apply_mk _ _ _).symm⟩
      rw [←hfix g]
      exact mem_map_of_mem (MulAut.conjNormal g).toMonoidHom ha }
  rcases (inferInstance : (UnitaryCover.frattiniAction h).IsIrreducible).eq_bot_or_eq_top W with hz | ht
  · have hmap : A.map q = ⊥ := i.injective (by
      have hh := congrArg Subrepresentation.toSubmodule hz
      change i (A.map q) = ⊥ at hh
      exact hh.trans i.map_bot.symm)
    have hAPhi : A ≤ frattini (pCore 2 G) := by
      intro a ha
      have hz := mem_map_of_mem q ha
      rw [hmap,mem_bot] at hz
      exact (QuotientGroup.eq_one_iff _).mp hz
    have hb := card_le_of_le hAPhi
    rw [hAc] at hb
    have hphic := d.frattini_card_le_two hc
    have hq : 2 ≤ 2^m := by simpa using Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hm
    have h8 : 8 ≤ (2^m)^3 := Nat.pow_le_pow_left hq 3
    omega
  · have hmap : A.map q = ⊤ := i.injective (by
      have hh := congrArg Subrepresentation.toSubmodule ht
      change i (A.map q) = ⊤ at hh
      exact hh.trans i.map_top.symm)
    have he := congrArg (Subgroup.comap q) hmap
    rw [comap_map_eq,comap_top,QuotientGroup.ker_mk'] at he
    exact hAt (frattini_nongenerating he)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryMoved

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
section Unitary
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B (residual H))
  (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
  (he : (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm).reverse)) ∨
    (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)))
include d h hH hp m hm he

/-- The entire original overcomponent core is elementary, in both unitary
orientations and including the degree-two extension. -/
theorem Preparation.unitary_overcomponent_elementary_core
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H < J)
    (hQR : ¬ (residual H).pCoreIn 2 ≤ J.pCoreIn 2) :
    IsElementaryAbelian 2 (J.pCoreIn 2) ∧ frattini (pCore 2 J) = ⊥ := by
  let K := residual H
  let R := J.pCoreIn 2
  let N := K ⊓ R
  obtain ⟨hN,hNc⟩ := d.unitary_overcomponent_proper_intersection h hH hp m hm he hJ hKJ.le hQR
  obtain ⟨_,_,_,_,_,hNi⟩ := d.unitary_overcomponent_core_intersection h hH hp m hm he hJ hKJ.le
  obtain ⟨_,_,hc,hsection⟩ := d.unitary_overcomponent_full_linear_action h hH hp m hm he hJ hKJ hQR
  let e : pCore 2 J ≃* R := (pCore 2 J).equivMapOfInjective J.subtype J.subtype_injective
  let A := (N.subgroupOf R).map e.symm.toMonoidHom
  let := hN
  let : IsElementaryAbelian 2 (N.subgroupOf R) := IsElementaryAbelian.subgroupOf (show N ≤ R from inf_le_right)
  have hA : IsElementaryAbelian 2 A := IsElementaryAbelian.map e.symm.toMonoidHom
  have hAc : Nat.card A = (2^m)^3 := by
    rw [card_map_of_injective e.symm.injective,
      Nat.card_congr (subgroupOfEquivOfLe (show N ≤ R from inf_le_right)).toEquiv]
    exact hNc
  have hAi : A.index ≤ 2 := by
    rw [index_map_of_bijective e.symm.bijective]
    exact hNi
  have hRc : Nat.card (pCore 2 J) ≤ 2*(2^m)^3 := by
    rw [Nat.card_congr e.toEquiv]
    exact (d.unitary_overcomponent_proper_quotient_core h hH hp m hm he hJ hKJ.le hQR).2
  let : Group.IsPerfect J := Chapter1.mem_L_isPerfect hJ
  let : IsElementaryAbelian 2 (pCore 2 J) :=
    UnitaryMoved.elementary_core hm hsection hRc A hA hAc hAi
  exact ⟨IsElementaryAbelian.of_injective e.symm.toMonoidHom e.symm.injective,
    frattini_eq_bot_of_isElementaryAbelian (p := 2)⟩

omit he in
/-- In either ordinary unitary orientation the actual core is the entire
natural module, since it is the original intersection of order q³. -/
theorem Preparation.unitary_ordinary_overcomponent_natural_core
    (heordinary : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm).reverse))
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H < J)
    (hQR : ¬ (residual H).pCoreIn 2 ≤ J.pCoreIn 2) :
    Nat.card (J.pCoreIn 2) = (2^m)^3 ∧
      ∃ hc : HasCharacteristicTwo J, UnitaryCover.NaturalCoreAction hc m := by
  have hRK := (d.unitary_ordinary_overcomponent_core_le h hH hp m hm heordinary hJ hKJ.le).trans
    (pCoreIn_le 2 _)
  have heq : residual H ⊓ J.pCoreIn 2 = J.pCoreIn 2 := inf_eq_right.mpr hRK
  have hcard := (d.unitary_overcomponent_proper_intersection h hH hp m hm (.inl heordinary)
    hJ hKJ.le hQR).2
  rw [heq] at hcard
  obtain ⟨_,_,hc,hsection⟩ := d.unitary_overcomponent_full_linear_action h hH hp m hm
    (.inl heordinary) hJ hKJ hQR
  refine ⟨hcard,hc,hsection.whole_of_card_le ?_⟩
  change Nat.card ((pCore 2 J) ⧸ frattini (pCore 2 J)) ≤ _
  calc
    _ ≤ Nat.card (pCore 2 J) := Nat.card_le_card_of_surjective
      (QuotientGroup.mk' (frattini (pCore 2 J))) (QuotientGroup.mk'_surjective _)
    _ = Nat.card (J.pCoreIn 2) := Nat.card_congr
      ((pCore 2 J).equivMapOfInjective J.subtype J.subtype_injective).toEquiv
    _ = (2^m)^3 := hcard

end Unitary
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
