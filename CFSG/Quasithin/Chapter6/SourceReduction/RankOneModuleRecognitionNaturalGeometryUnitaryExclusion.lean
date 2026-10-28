module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryAmalgam
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPlaneRadical.Structure
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot.CubicFixed
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourExtension.PlaneAction
public import Theory.GroupTheory.PResidual.NormalPGroupSupplement
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourExtension.BinaryOrders

/-!
# Excluding the concrete binary unitary amalgams on the original natural layer

A cubic in the actual unitary plane factor fixes a nonzero Hermitian matrix.
Its two-core has order sixteen. Any isomorphism from the original local L
would therefore identify its entire natural layer with that two-core, contrary
to the fixed-free cubic action on the natural SL2(4) module.

The original local L is the two-residual of LT. The ordinary unitary plane
and its field extension both have two-residual isomorphic to the same concrete
plane factor. Thus neither can be the original vertex LT. The point endpoints
are excluded by the factor five in the order of LT. Consequently the literal
source amalgam, with its whole Borel overlap, is not even parabolically
equivalent to either binary unitary model, in either orientation.

The final theorem applies this exclusion to the already constructed escaping
subgroup on the original cover. General mixed-pair recognition and the contained
S5 parabolic escape remain with qt-d-1222-rankone-recognition-natural, as do
initial 6.1.4–5, omega escape and remaining geometry through unconditional 6.1.27.
Source: Aschbacher–Smith 6.1.19, printed p.675, and F.1.12(I)(6),
printed pp.263–264 (`refs/quasithin.pdf`).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalUnitary
open ChapterF.GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourPlaneRadical UnitaryFourShortRoot UnitaryFourPlaneLocal
open Representation.OrthogonalFourMinus

private theorem unitary_fixed_cubic :
    ∃ c v : L2 1 (Nat.le_refl 1), orderOf c = 3 ∧
      v ∈ pCore 2 (L2 1 (Nat.le_refl 1)) ∧ v ≠ 1 ∧ c*v*c⁻¹=v := by
  let F := MatrixField 1
  let σ := fieldConj 1
  let hσ := fieldConj_involutive 1 (Nat.le_refl 1)
  let a := cubic F
  let c := levi F σ hσ a
  let X := fixedParameter F σ hσ 1
  let u := twoCoreEquiv F σ hσ (Multiplicative.ofAdd X)
  have hc : orderOf c=3 := by
    have hi : Function.Injective (levi F σ hσ) :=
      (show Function.LeftInverse (factorRestriction F (UnitaryFourFlag.form F σ hσ))
        (levi F σ hσ) from factorRestriction_levi F σ hσ).injective
    exact (orderOf_injective (levi F σ hσ) hi a).trans (cubic_order F)
  have hfix : c*u.val*c⁻¹=u.val := by
    have hh := twoCoreEquiv_conj F σ hσ c (Multiplicative.ofAdd X)
    rw [quotientEquivSL2_mk,factorRestriction_levi] at hh
    change MulAut.conjNormal c u = twoCoreEquiv F σ hσ
      (Multiplicative.ofAdd (hermitianCongruence F σ hσ (cubic F) (fixedParameter F σ hσ 1))) at hh
    rw [fixedParameter_fixed] at hh
    exact congrArg Subtype.val hh
  have hu : u.val ≠ 1 := by
    intro he
    have he' : u=1 := Subtype.ext he
    have hx : X=0 := congrArg Multiplicative.toAdd
      ((twoCoreEquiv F σ hσ).injective (he'.trans (map_one _).symm))
    have hh := congrArg (fun Y : hermitianMatrices F σ => Y.val 0 1) hx
    exact one_ne_zero hh
  let e := L2ProjectIso 1 (Nat.le_refl 1)
  refine ⟨e c,e u.val,(e.orderOf_eq c).trans hc,?_,?_,?_⟩
  · rw [←pCore_map_iso 2 e]
    exact mem_map_of_mem e.toMonoidHom u.property
  · exact fun he => hu (e.injective (he.trans e.map_one.symm))
  · rw [←map_inv,←map_mul,←map_mul,hfix]
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalUnitary

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G}
open ChapterF.GreenBook.LieModels.UnitaryFour

/-- The original natural local group is not the Hermitian plane factor. -/
theorem natural_four_not_unitary_plane
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2) :
    ¬ Nonempty (L ≃* L2 1 (Nat.le_refl 1)) := by
  rintro ⟨e⟩
  have hVQ : layer L R ≤ L.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (T.isPGroup'.to_le h.layer_le_T) h.layer_le_L
      (normalizer_commutator_ge_right R L)
  have hcard : Nat.card (L.pCoreIn 2) = 16 := by
    change Nat.card ((pCore 2 L).map L.subtype) = 16
    rw [card_map_of_injective L.subtype_injective]
    have he := Nat.card_congr ((e.subgroupMap (pCore 2 L)).trans
      (MulEquiv.subgroupCongr (pCore_map_iso 2 e))).toEquiv
    exact he.trans (by simpa using L2TwoCore_card 1 (Nat.le_refl 1))
  have hV : layer L R = L.pCoreIn 2 := eq_of_le_of_card_ge hVQ (by
    rw [hcard,hnat.card]
    norm_num)
  obtain ⟨c,v,hc,hv,hv1,hcv⟩ := NaturalUnitary.unitary_fixed_cubic
  have hvQ : e.symm v ∈ pCore 2 L := by
    rw [←pCore_map_iso 2 e.symm]
    exact mem_map_of_mem e.symm.toMonoidHom hv
  have hfix : ((e.symm c : L) : G) * ((e.symm v : L) : G) *
      ((e.symm c : L) : G)⁻¹ = ((e.symm v : L) : G) := by
    have hh := congrArg e.symm hcv
    rw [map_mul,map_mul,map_inv] at hh
    exact congrArg Subtype.val hh
  have hone := hnat.cubic_fixed_eq_one (e.symm c).property
    ((orderOf_coe _).trans ((e.symm.orderOf_eq c).trans hc))
    (hV ▸ mem_map_of_mem L.subtype hvQ) hfix
  exact hv1 (e.symm.injective ((Subtype.ext hone).trans e.symm.map_one.symm))
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalUnitary
open ChapterF.GreenBook.LieModels.UnitaryFour
open Extension
local notation "h1" => (Nat.le_refl 1)

private def plane_residual_equiv : pResidual 2 (planeParabolic 1 h1) ≃* L2 1 h1 := by
  let e := MulEquiv.subgroupCongr BinaryCompletion.plane_eq_local
  have he : pResidual 2 (planeParabolic 1 h1) = ⊤ := by
    apply (Subgroup.map_injective (f := e.toMonoidHom) e.injective)
    rw [map_pResidual,L2_pResidual_eq_top,map_top_of_surjective e.toMonoidHom e.surjective]
  exact (MulEquiv.subgroupCongr he).trans (topEquiv.trans e)

private def extended_plane_residual_equiv : pResidual 2 (plane 1 h1) ≃* L2 1 h1 := by
  let e := MulEquiv.subgroupCongr BinaryCompletion.plane_eq_local
  have hp : IsPPerfect 2 (planeParabolic 1 h1) :=
    (L2_isPPerfect 1 h1).of_surjective e.symm.toMonoidHom e.symm.surjective
  have hi : IsPPerfect 2 binaryPlaneInclusion.range :=
    hp.of_surjective binaryPlaneInclusion.rangeRestrict binaryPlaneInclusion.rangeRestrict_surjective
  have hlow : binaryPlaneInclusion.range ≤ pResidual 2 (plane 1 h1) :=
    le_pResidual_of_isPPerfect _ hi
  have hhigh : pResidual 2 (plane 1 h1) ≤ binaryPlaneInclusion.range := by
    rw [binaryPlaneInclusion_range_eq_ker]
    apply pResidual_le_ker_of_isPGroup 2 binaryPlaneParity
    exact IsPGroup.of_card (n := 1) (by change Nat.card (ZMod 2) = 2^1; simp)
  exact (MulEquiv.subgroupCongr (le_antisymm hhigh hlow)).trans
    ((MonoidHom.ofInjective binaryPlaneInclusion_injective).symm.trans e)
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalUnitary

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
open ChapterF.GreenBook.LieModels.UnitaryFour

private def natural_local_residual_equiv
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n) :
    pResidual 2 (L ⊔ (T : Subgroup G) : Subgroup G) ≃* L := by
  let H := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf H
  let S := (T : Subgroup G).subgroupOf H
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer h.sylow_normalizes_L)
  let e : A ≃* L := subgroupOfEquivOfLe (show L ≤ H from le_sup_left)
  have hp : IsPPerfect 2 A := h.local_mem.2.2.1.of_surjective
    e.symm.toMonoidHom e.symm.surjective
  have hsup : A ⊔ S = ⊤ := by
    rw [←subgroupOf_sup (show L ≤ H from le_sup_left) (show (T : Subgroup G) ≤ H from le_sup_right),subgroupOf_self]
  have he := pResidual_of_normal_pGroup_supplement 2 A S T.isPGroup'.comap_subtype hsup
  rw [(pResidual_eq_top_iff 2 A).mpr hp,←MonoidHom.range_eq_map,range_subtype] at he
  exact (MulEquiv.subgroupCongr he.symm).trans e

/-- Recovering the original local group as the two-residual excludes both
ordinary and field-extended unitary plane vertices. -/
theorem natural_four_not_unitary_vertex
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2) :
    (¬ Nonempty ((L ⊔ (T : Subgroup G) : Subgroup G) ≃* planeParabolic 1 (Nat.le_refl 1))) ∧
    (¬ Nonempty ((L ⊔ (T : Subgroup G) : Subgroup G) ≃* Extension.plane 1 (Nat.le_refl 1))) := by
  have no := natural_four_not_unitary_plane h hnat
  have step {H : Type} [Group H] (eH : pResidual 2 H ≃* L2 1 (Nat.le_refl 1)) :
      ¬ Nonempty ((L ⊔ (T : Subgroup G) : Subgroup G) ≃* H) := by
    rintro ⟨e⟩
    apply no
    exact ⟨(natural_local_residual_equiv h).symm.trans
      (((e.subgroupMap (pResidual 2 (L ⊔ (T : Subgroup G) : Subgroup G))).trans
        (MulEquiv.subgroupCongr (map_pResidual 2 e))).trans eH)⟩
  exact ⟨step NaturalUnitary.plane_residual_equiv,step NaturalUnitary.extended_plane_residual_equiv⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G}
open ChapterF.GreenBook.LieModels.UnitaryFour

omit [Finite G] in
private theorem natural_four_five_dvd_vertex
    (hnat : IsNaturalModule L (layer L R) 2) :
    5 ∣ Nat.card (L ⊔ (T : Subgroup G) : Subgroup G) := by
  obtain ⟨F,_,_,_,hF,e,_⟩ := hnat
  have hq : Nat.card (L ⧸ pCore 2 L)=60 := by
    rw [Nat.card_congr e.toEquiv,GorensteinWalter.sl2_card_formula,hF]
    norm_num
  have hd := (pCore 2 L).index_dvd_card
  rw [index_eq_card,hq] at hd
  exact (dvd_trans (by decide : 5 ∣ 60) hd).trans
    (card_dvd_of_le (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left))

omit [Finite G] in
/-- The factor five excludes both unitary point vertices. -/
theorem natural_four_not_unitary_point_vertex
    (hnat : IsNaturalModule L (layer L R) 2) :
    (¬ Nonempty ((L ⊔ (T : Subgroup G) : Subgroup G) ≃* pointParabolic 1 (Nat.le_refl 1))) ∧
    (¬ Nonempty ((L ⊔ (T : Subgroup G) : Subgroup G) ≃* Extension.point 1 (Nat.le_refl 1))) := by
  have hd := natural_four_five_dvd_vertex (T := T) hnat
  constructor
  · rintro ⟨e⟩
    rw [Nat.card_congr e.toEquiv,BinaryCompletion.point_card] at hd
    norm_num at hd
  · rintro ⟨e⟩
    rw [Nat.card_congr e.toEquiv,Extension.binary_point_card] at hd
    norm_num at hd

/-- Both orientations of the literal source pair are excluded from the
ordinary and field-extended binary unitary amalgams. -/
@[expose] def NaturalUnitaryAmalgamExclusion (T : Sylow 2 G) (L B : Subgroup G) : Prop :=
    let P := ChapterF.Source.parabolic ![L,B] (T : Subgroup G)
    let D := ChapterF.Source.commonBorel ![L,B] (T : Subgroup G)
    let α := RankTwoAmalgam.ofSubgroups (P 0) D (P 1)
      (ChapterF.Source.commonBorel_le_parabolic 0) (ChapterF.Source.commonBorel_le_parabolic 1)
    let β := RankTwoAmalgam.ofSubgroups (P 1) D (P 0)
      (ChapterF.Source.commonBorel_le_parabolic 1) (ChapterF.Source.commonBorel_le_parabolic 0)
    (¬ Nonempty (RankTwoAmalgam.ParabolicEquiv α (amalgam 1 (Nat.le_refl 1)))) ∧
    (¬ Nonempty (RankTwoAmalgam.ParabolicEquiv β (amalgam 1 (Nat.le_refl 1)))) ∧
    (¬ Nonempty (RankTwoAmalgam.ParabolicEquiv α (Extension.amalgam 1 (Nat.le_refl 1)))) ∧
    (¬ Nonempty (RankTwoAmalgam.ParabolicEquiv β (Extension.amalgam 1 (Nat.le_refl 1))))

/-- The actual source pair and whole overlap admit neither unitary model,
even without requiring the two isomorphism squares to commute. -/
theorem natural_cubic_amalgam_not_unitary
    {B : Subgroup G}
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (hF : ChapterF.Source.HypothesisF11 ![L,B] (T : Subgroup G))
    (e : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) :
    NaturalUnitaryAmalgamExclusion T L B := by
  obtain ⟨hp,he⟩ := natural_four_not_unitary_point_vertex (T := T) hnat
  obtain ⟨hq,hf⟩ := natural_four_not_unitary_vertex h hnat
  have hP := (natural_cubic_amalgam_products hF e).1
  rw [←hP] at hp he hq hf
  exact ⟨fun ⟨j⟩ => hp ⟨j.left⟩,fun ⟨j⟩ => hq ⟨j.right⟩,
    fun ⟨j⟩ => he ⟨j.left⟩,fun ⟨j⟩ => hf ⟨j.right⟩⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G]
/-- The same original escaping subgroup, its source pair and faithful local
triple, now excluding both concrete binary unitary rows in either orientation. -/
@[expose] def NaturalEscapingAmalgamUnitaryData (T : Sylow 2 G) (L R P N M : Subgroup G) : Prop :=
  ∃ B : Subgroup G, B ≤ P ⊔ N.pCoreIn 2 ∧
    B ≤ Escape.I (T : Subgroup G) L R ∧ (¬ B ≤ M) ∧
    Nonempty ((B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) ∧
    ChapterF.Source.HypothesisF11 ![L,B] (T : Subgroup G) ∧
    Group.IsSolvable (ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1) ∧
    ChapterF.Source.LocallyRankOneTriple
      (fun i => (ChapterF.Source.parabolic ![L,B] (T : Subgroup G) i).subgroupOf
        (ChapterF.Source.generated ![L,B] (T : Subgroup G)))
      ((ChapterF.Source.commonBorel ![L,B] (T : Subgroup G)).subgroupOf
        (ChapterF.Source.generated ![L,B] (T : Subgroup G))) ∧ NaturalUnitaryAmalgamExclusion T L B

variable [Finite G] {T : Sylow 2 G} {L M R P N : Subgroup G}
/-- Apply the concrete unitary exclusion to the original escaping subgroup.
Recognition of a general mixed pair remains separate. -/
theorem natural_escaping_amalgam_unitary_exclusion
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (d : NaturalEscapingAmalgamData T L R P N M) :
    NaturalEscapingAmalgamUnitaryData T L R P N M := by
  obtain ⟨B,hBK,hBI,hBM,he,hF,hsolv,htriple⟩ := d
  exact ⟨B,hBK,hBI,hBM,he,hF,hsolv,htriple,
    natural_cubic_amalgam_not_unitary h hnat hF he.some⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
