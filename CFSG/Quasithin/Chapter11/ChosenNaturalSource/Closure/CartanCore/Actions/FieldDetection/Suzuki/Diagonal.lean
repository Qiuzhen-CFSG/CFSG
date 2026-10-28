module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Suzuki.Fixed
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Components
public import Theory.GroupTheory.CComponent.DiagonalNormalizer

/-!
# Every Suzuki Borel coefficient lifts to the original Sylow normalizer

In the swapped case, the component normalizer has index two inside G₁.
The general diagonal lifting theorem applies to the original component
projection, after transporting it to G₁. Its restriction has exactly the
intrinsic component two-core as kernel. Sylow maximality identifies the
component Sylow image with the marked root group, so every Borel coefficient
has a diagonal lift normalizing the original T. The fixed case is supplied
by `Fixed`. Both cases retain the literal `OrbitCoordinates.coefficient`.

The final consumer discharges the normalizer-lift premise in source
11.5.6(3). Construction of the orbit coordinates and their nontrivial field
actor remains with qt-d-1222-natural-closure-cartan; this theorem does not
assume or claim that construction. Earlier geometry is discharged by
qt-d-1222-natural-closure and its preceding-geometry producers.
Source: Aschbacher--Smith, 11.5.6(3), printed pp.780--781.
-/

public noncomputable section

open Subgroup Theory.GroupTheory BenderSuzuki BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.SuzukiBorelFieldQuotient
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.Suzuki
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

private theorem suzuki_center (m : ℕ) (hm : 0 < m) :
    center (SuzukiMatrixGroup m) = ⊥ := by
  have hmodel : IsSimpleBenderGroup (SuzukiMatrixGroup m) :=
    .isSuzuki ⟨m,hm,⟨MulEquiv.refl _⟩⟩
  let := hmodel.isSimple
  rcases (inferInstance : (center (SuzukiMatrixGroup m)).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (hmodel.not_commutative (fun x y => by
      have hx : x ∈ center (SuzukiMatrixGroup m) := h.symm ▸ mem_top x
      exact (mem_center_iff.mp hx y).symm)).elim

/-- Every coefficient has a lift in the original Sylow normalizer, also
when the original Sylow interchanges the two C-components. -/
theorem OrbitCoordinates.normalizerLifts_of_swapped
    {L V : Subgroup G} {D : ChosenModule T L V} (E : Geometry D)
    (hp : E.point ≠ ⊥) (hT : (T : Subgroup G) ≤ E.G₁)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (hmove : ¬ (T : Subgroup G) ≤ normalizer (I : Set G))
    {m : ℕ} (c : OrbitCoordinates T I m) (hm : 0 < m) : c.NormalizerLifts hm := by
  classical
  let H := E.G₁
  let A := I.subgroupOf H
  let J := (orbit T I).subgroupOf H
  have hIH : I ≤ H := hI.1.trans E.Y_le_G₁
  have hJH : orbit T I ≤ H := conjugateSpanBy_le hIH (hT.trans H.le_normalizer)
  let eA : A ≃* I := subgroupOfEquivOfLe hIH
  let eJ : J ≃* orbit T I := subgroupOfEquivOfLe hJH
  let S : Sylow 2 H := T.subtype hT
  let model : (A ⧸ pCore 2 A) ≃* SuzukiMatrixGroup m :=
    (QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).trans c.component
  have hA : A.IsCComponent := E.component_in_point_normalizer hI
  let : Group.IsPerfect A := hA.perfect
  have hmodel : IsSimpleBenderGroup (SuzukiMatrixGroup m) :=
    .isSuzuki ⟨m,hm,⟨MulEquiv.refl _⟩⟩
  let := hmodel.isSimple
  let : IsSimpleGroup (A ⧸ pCore 2 A) := model.isSimpleGroup
  have hz : center (A ⧸ pCore 2 A) = ⊥ := by
    apply eq_bot_iff.mpr
    intro a ha
    have hh : model a ∈ center (SuzukiMatrixGroup m) := (centerCongr model ⟨a,ha⟩).property
    rw [suzuki_center m hm,mem_bot] at hh
    exact model.injective (hh.trans model.map_one.symm)
  let : IsQuasisimple (A ⧸ pCore 2 A) := {
    simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }
  have ho : Nat.Coprime 2 (Nat.card (MulAut.Outer (A ⧸ pCore 2 A))) := by
    rw [Nat.card_congr (MulAut.outerCongr model).toEquiv]
    exact (suzuki_odd_outer_index m hm).coprime_two_left
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp hmove
  let tH : H := ⟨t,hT ht⟩
  have htnH : tH ∉ normalizer (A : Set H) := by
    rw [← subgroupOf_normalizer_eq hIH]
    exact htn
  have hi : (normalizer (A : Set H)).index = 2 := by
    rcases E.component_normal_or_index_two hp hI with hnormal | hindex
    · exact (htnH ((normalizer_eq_top_iff.mpr hnormal).symm ▸ mem_top tH)).elim
    · exact hindex
  have hAJ : A ≤ J := fun a ha => le_conjugateSpanBy I (T : Subgroup G) ha
  have hAtJ : A.conjBy tH ≤ J := by
    rintro _ ⟨a,ha,rfl⟩
    exact (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy I (T : Subgroup G) ht)
      (a : G)).mp (le_conjugateSpanBy I (T : Subgroup G) ha)
  let f : J →* SuzukiMatrixGroup m := c.quotient.comp eJ.toMonoidHom
  have hrestrict : f.comp (inclusion hAJ) =
      model.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A)) := by
    apply MonoidHom.ext
    intro a
    exact c.restriction (eA a)
  have hf : Function.Surjective (f.comp (inclusion hAJ)) := by
    rw [hrestrict]
    exact model.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : (f.comp (inclusion hAJ)).ker = pCore 2 A := by
    rw [hrestrict]
    ext a
    change model (QuotientGroup.mk' (pCore 2 A) a) = 1 ↔ a ∈ pCore 2 A
    rw [model.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff _
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_subnormal A hA.subnormal
  have himage : P.map (f.comp (inclusion hAJ)) = SuzukiRootSubgroup m := by
    have hle : P.map (f.comp (inclusion hAJ)) ≤ SuzukiRootSubgroup m := by
      rw [← c.sylow_image]
      rintro _ ⟨a,ha,rfl⟩
      refine ⟨eJ (inclusion hAJ a), ?_, rfl⟩
      change ((a : H) : G) ∈ (T : Subgroup G)
      have haS : (a : H) ∈ (S : Subgroup H) := by rw [hP] at ha; exact ha
      exact haS
    have htwo : IsPGroup 2 (SuzukiRootSubgroup m) := by
      rw [← c.sylow_image]
      exact T.isPGroup'.comap_subtype.map c.quotient
    exact ((P.mapSurjective hf).is_maximal' htwo hle).symm
  intro u
  obtain ⟨y,hy⟩ := projection_surjective m hm u
  have hyN : (y : SuzukiMatrixGroup m) ∈
      normalizer (P.map (f.comp (inclusion hAJ)) : Set (SuzukiMatrixGroup m)) := by
    rw [himage, suzukiRootSubgroup_normalizer m hm]
    exact y.property
  obtain ⟨d,hdN,hdy⟩ := exists_diagonal_sylow_normalizer_lift S A hA hi hz ho tH ht
    htnH J hAJ hAtJ f (suzuki_center m hm) hf hk P hP y hyN
  have hdT : ((d : H) : G) ∈ normalizer (T : Set G) := by
    have hh := (S : Subgroup H).le_normalizer_map H.subtype (mem_map_of_mem H.subtype hdN)
    change ((d : H) : G) ∈ normalizer (((T : Subgroup G).subgroupOf H).map H.subtype : Set G) at hh
    rwa [map_subgroupOf_eq_of_le hT] at hh
  have hdB : ((d : H) : G) ∈ borel T I := by
    refine ⟨d.property, ?_⟩
    exact inf_normalizer_le_normalizer_inf
      ⟨hdT,(orbit T I).le_normalizer d.property⟩
  refine ⟨⟨d,hdB⟩,hdT,?_⟩
  change projection m hm (c.borelMap hm ⟨d,hdB⟩) = u
  have he : c.borelMap hm ⟨d,hdB⟩ = y := Subtype.ext hdy
  rw [he,hy]

/-- Both possible component orbits supply the same literal coefficient lifts. -/
theorem OrbitCoordinates.normalizerLifts
    {L V : Subgroup G} {D : ChosenModule T L V} (E : Geometry D)
    (hp : E.point ≠ ⊥) (hT : (T : Subgroup G) ≤ E.G₁)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    {m : ℕ} (c : OrbitCoordinates T I m) (hm : 0 < m) : c.NormalizerLifts hm := by
  by_cases hTI : (T : Subgroup G) ≤ normalizer (I : Set G)
  · exact c.normalizerLifts_of_fixed hm hTI
  · exact c.normalizerLifts_of_swapped E hp hT hI hTI hm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.Suzuki

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open CartanActions.FieldDetection.Suzuki
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : ChosenModule T L V} (E : Geometry D)

/-- The original Suzuki Borel-movement consumer has no remaining
normalizer-lift premise. Coordinates and the field actor are constructed
by the remaining field-action branch of this task. -/
theorem suzuki_borel_movement_of_field_action
    (hp : E.point ≠ ⊥) (hT : (T : Subgroup G) ≤ E.G₁)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    {m : ℕ} (hm : 0 < m) (c : OrbitCoordinates T I m)
    (a : FieldAction E c hm) : E.BorelMovement :=
  a.borel_movement (conjugateSpanBy_le hI.1 (hT.trans E.G₁_normalizes_Y))
    (c.normalizerLifts E hp hT hI hm)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
