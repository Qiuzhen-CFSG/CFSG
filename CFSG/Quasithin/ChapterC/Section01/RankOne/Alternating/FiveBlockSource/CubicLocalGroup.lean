module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.CubicSelection
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup
public import CFSG.Quasithin.ChapterA.Section01.Fitting.Characteristic
/-!
# The selected cubic local before the Baumann reduction

Pull back the marked twelve-element local and four-group along the original
S₅ action. The latter is an actual Sylow of index three, stays inside the
original R, and contains the marked Baumann group. Characteristic two restricts
from the original group. The literal residual is exactly the chosen subgroup
of L, proved by its two-perfectness and two-group supplement.
Source: Aschbacher–Smith C.1.21(4), C.1.23(1), printed pp.129–130.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
open Theory.SpecificGroups.SymmetricFive Theory.SpecificGroups.SymmetricFive.CubicSelection
variable {H : Type*} [Group H] [Finite H]

@[expose] def cubicLocalGroup (q : H →* Sym) : Subgroup H := OuterFourGeometry.localGroup.comap q
@[expose] def cubicLocalTwoGroup (q : H →* Sym) : Subgroup H := OuterFourGeometry.four.comap q
private def localProjection (q : H →* Sym) : cubicLocalGroup q →* OuterFourGeometry.localGroup :=
  (q.comp (cubicLocalGroup q).subtype).codRestrict _ fun x => x.property

omit [Finite H] in
private theorem localProjection_surjective (q : H →* Sym) (hq : Function.Surjective q) :
    Function.Surjective (localProjection q) := by
  intro y
  obtain ⟨x,hx⟩ := hq y
  exact ⟨⟨x,show q x∈OuterFourGeometry.localGroup from hx.symm ▸ y.property⟩,Subtype.ext hx⟩

omit [Finite H] in
/-- The original two-group in the selected local has index three. -/
theorem cubicLocalTwoGroup_index (q : H →* Sym) (hq : Function.Surjective q) :
    ((cubicLocalTwoGroup q).subgroupOf (cubicLocalGroup q)).index = 3 := by
  let B := OuterFourGeometry.four.subgroupOf OuterFourGeometry.localGroup
  have hc : Nat.card B = 4 := (Nat.card_congr
    (subgroupOfEquivOfLe OuterFourGeometry.four_le_local).toEquiv).trans OuterFourGeometry.four_card
  have hi : B.index = 3 := by
    have hh := B.index_mul_card
    rw [hc,OuterFourGeometry.local_card] at hh
    omega
  have he : (cubicLocalTwoGroup q).subgroupOf (cubicLocalGroup q) = B.comap (localProjection q) := rfl
  rw [he,B.index_comap_of_surjective (localProjection_surjective q hq),hi]

omit [Finite H] in
/-- Pull back the marked four-group through the actual two-group kernel. -/
theorem cubicLocalTwoGroup_isPGroup (q : H →* Sym) (hk : IsPGroup 2 q.ker) :
    IsPGroup 2 (cubicLocalTwoGroup q) :=
  (IsElementaryAbelian.isPGroup 2 OuterFourGeometry.four).comap_of_ker_isPGroup q hk

omit [Finite H] in
/-- The literal selected two-group is a Sylow subgroup of the literal local. -/
theorem cubicLocalTwoGroup_sylow (q : H →* Sym) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) :
    ∃ P : Sylow 2 (cubicLocalGroup q),
      (P : Subgroup (cubicLocalGroup q)) = (cubicLocalTwoGroup q).subgroupOf (cubicLocalGroup q) := by
  have hp : IsPGroup 2 ((cubicLocalTwoGroup q).subgroupOf (cubicLocalGroup q)) :=
    (cubicLocalTwoGroup_isPGroup q hk).comap_subtype
  exact ⟨hp.toSylow (by rw [cubicLocalTwoGroup_index q hq]; decide),rfl⟩

/-- The selected local contains the original two-core, so characteristic two restricts. -/
theorem cubicLocalGroup_characteristic (q : H →* Sym)
    (hfit : generalizedFitting H = pCore 2 H) (hQ : pCore 2 H ≤ q.ker) :
    generalizedFitting (cubicLocalGroup q) = pCore 2 (cubicLocalGroup q) := by
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  apply centralizer_pCore_le_of_pCore_le (cubicLocalGroup q)
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfit)
  intro g hg
  change q g∈OuterFourGeometry.localGroup
  rw [MonoidHom.mem_ker.mp (hQ hg)]
  exact one_mem _

omit [Finite H] in
/-- The selected two-group stays between the original Baumann subgroup and R. -/
theorem cubicLocalTwoGroup_bounds (q : H →* Sym) (R B : Subgroup H)
    (hR : R.map q = OuterFourGeometry.eight) (hk : q.ker ≤ R)
    (hB : B.map q = OuterFourGeometry.four) : B ≤ cubicLocalTwoGroup q ∧ cubicLocalTwoGroup q ≤ R := by
  refine ⟨map_le_iff_le_comap.mp hB.le,?_⟩
  have hr : OuterFourGeometry.eight.comap q = R := by
    rw [←hR,comap_map_eq,sup_eq_left.mpr hk]
  exact (comap_mono OuterFourGeometry.four_le_eight).trans_eq hr
/-- The selected local is the product of its original cubic residual and
its original two-group, not just a quotient generation statement. -/
theorem cubicLocalGroup_eq_residual_join (q : H →* Sym) (hq : Function.Surjective q)
    (L : Subgroup H) (hL : L.map q = alternatingGroup (Fin 5)) :
    cubicLocalGroup q = selectedResidual q L ⊔ cubicLocalTwoGroup q := by
  have hY : selectedResidual q L ≤ cubicLocalGroup q :=
    map_le_iff_le_comap.mp ((selectedResidual_image q L hL).le.trans cubic_le_local)
  have hP : cubicLocalTwoGroup q ≤ cubicLocalGroup q := comap_mono OuterFourGeometry.four_le_local
  have he : (selectedResidual q L ⊔ cubicLocalTwoGroup q).map q = OuterFourGeometry.localGroup := by
    rw [Subgroup.map_sup,selectedResidual_image q L hL,
      show (cubicLocalTwoGroup q).map q = OuterFourGeometry.four from map_comap_eq_self_of_surjective hq _,
      cubic_sup_four]
  have hk : q.ker ≤ cubicLocalTwoGroup q := by
    intro g hg
    change q g∈OuterFourGeometry.four
    rw [MonoidHom.mem_ker.mp hg]
    exact one_mem _
  have hh := congrArg (comap q) he
  change OuterFourGeometry.localGroup.comap q = _
  simpa only [comap_map_eq,sup_eq_left.mpr (hk.trans le_sup_right)] using hh.symm

/-- The literal O² of the selected local is exactly the subgroup chosen in L. -/
theorem cubicLocalGroup_residual (q : H →* Sym) (hq : Function.Surjective q)
    (L : Subgroup H) [L.Normal] (hL : L.map q = alternatingGroup (Fin 5))
    (hk : IsPGroup 2 q.ker) :
    (pResidual 2 (cubicLocalGroup q)).map (cubicLocalGroup q).subtype = selectedResidual q L := by
  let N := cubicLocalGroup q
  let Y := selectedResidual q L
  let P := cubicLocalTwoGroup q
  have hN : N=Y⊔P := cubicLocalGroup_eq_residual_join q hq L hL
  have hYN : Y ≤ N := hN.symm ▸ le_sup_left
  have hPN : P ≤ N := hN.symm ▸ le_sup_right
  let : (Y.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hYN).mpr (by
    rw [hN]
    exact sup_le Y.le_normalizer (selectedResidual_normalized q L hL))
  have hYP : IsPPerfect 2 (Y.subgroupOf N) :=
    (selectedResidual_twoPerfect q L).of_surjective (subgroupOfEquivOfLe hYN).symm.toMonoidHom
      (subgroupOfEquivOfLe hYN).symm.surjective
  have hpP : IsPGroup 2 (P.subgroupOf N) := (cubicLocalTwoGroup_isPGroup q hk).comap_subtype
  have he : Y.subgroupOf N ⊔ P.subgroupOf N = ⊤ := by
    rw [←subgroupOf_sup hYN hPN,←hN,subgroupOf_self]
  rw [pResidual_eq_of_isPPerfect_sup (Y.subgroupOf N) (P.subgroupOf N) hYP hpP he,
    map_subgroupOf_eq_of_le hYN]

end CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
