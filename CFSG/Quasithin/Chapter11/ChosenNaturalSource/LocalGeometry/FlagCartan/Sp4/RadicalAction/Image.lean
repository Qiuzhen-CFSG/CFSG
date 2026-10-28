module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.RadicalAction.Action
public import Theory.SpecificGroups.SymplecticFour.NaturalScalarCubic
public import Theory.SpecificGroups.SymplecticFour.FixedPlaneDisplacement

/-!
# Image, kernel, fixed space and displacement of the original plane radical

The actual local two-core surjects onto every symmetric shear. Together
with the full-action comparison this identifies the literal centralizer
kernel and the full fixed-plane preimage. Self-orthogonality bounds every
original displacement by that plane, giving the subgroup inputs used in
11.2.4 without discarding the central kernel.

Source: Aschbacher--Smith, 11.2.4, printed pp.769--770.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Matrix
open scoped MatrixGroups IsMulCommutative commutatorElement
open Theory.SpecificGroups.SymplecticFour
open SymplecticConjugatePair.Ambient SymplecticConjugatePair.Ambient.Normalizer
open SymplecticNaturalNormalizer
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4.RadicalAction
open PlaneAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

theorem alignedRadicalMap_range :
    (alignedRadicalMap S m).range = Plane.radical.map planeLocal.subtype := by
  apply le_antisymm
  · rintro _ ⟨r,rfl⟩
    exact alignedRadicalMap_mem S m r
  · rintro _ ⟨q,hq,rfl⟩
    obtain ⟨l,hl⟩ := localProjection_surjective S m 1 q
    have hlc : l ∈ pCore 2 ((flag m S).Li 1) := by
      rw [←planeProjection_ker]
      change Plane.quotientMap (localProjection S m 1 l) = 1
      rw [hl]
      exact hq
    let r : (flag m S).Ri 1 := ⟨l,planeCore_le_radical S m (mem_map_of_mem _ hlc)⟩
    refine ⟨r,?_⟩
    apply naturalHom_injective
    apply LinearEquiv.ext
    intro v
    change alignedRadicalMap S m r • v = q.val • v
    rw [alignedRadicalMap_apply,alignedOperator_apply]
    change (alignment m)⁻¹ •
      (ambientAction S m (inclusion le_sup_left (⟨l,(localResidual_le _ l.property).1⟩ : L))
        ((alignment m) • v)) = _
    rw [ambientAction_component]
    have he := localProjection_coe S m 1 l
    rw [hl] at he
    change _ = q.val • v
    rw [he,mul_smul,mul_smul]
    rfl

theorem radicalMap_range : (radicalMap S m).range =
    (Plane.radical.map planeLocal.subtype).map (MulAut.conj (alignment m)).toMonoidHom := by
  rw [radicalMap,MonoidHom.range_comp,alignedRadicalMap_range]

/-- The full action kernel is also the kernel on the original central quotient. -/
theorem radicalMap_ker : (radicalMap S m).ker = (centralizer (V : Set G)).subgroupOf ((flag m S).Ri 1) := by
  ext r
  change radicalMap S m r = 1 ↔ (r : G) ∈ centralizer (V : Set G)
  constructor
  · intro hr v hv
    let v' : V := ⟨v,hv⟩
    have h := radicalMap_fullAction S m r (D.spaceEquiv.symm v').toAdd
    rw [hr,map_one,Module.End.one_apply] at h
    change D.spaceEquiv (D.spaceEquiv.symm v') =
      V.normalizerMonoidHom (inclusion (ambientJoin_normalizes_seed S)
        (radicalInclusion S m r)) (D.spaceEquiv (D.spaceEquiv.symm v')) at h
    rw [D.spaceEquiv.apply_symm_apply] at h
    exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val h).symm).symm
  · intro hr
    apply naturalHom_injective
    apply LinearEquiv.ext
    intro w
    rw [map_one]
    change radicalMap S m r • w = w
    rw [radicalMap_apply]
    obtain ⟨v,hv⟩ := (Coordinates.sp4 m).projection_surjective (Multiplicative.ofAdd w)
    have hw : ((Coordinates.sp4 m).projection v).toAdd = w := congrArg Multiplicative.toAdd hv
    rw [←hw]
    change (Coordinates.sp4 m).conjugationAction _ _ _ _ = _
    rw [Coordinates.conjugationAction_projection]
    congr 2
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hr v.val v.property).symm

theorem fixed_eq_plane : V ⊓ centralizer ((flag m S).Ri 1 : Set G) = (flag m S).Vi 1 := by
  apply le_antisymm
  · intro v hv
    let v' : V := ⟨v,hv.1⟩
    let w := ((Coordinates.sp4 m).projection v').toAdd
    have hfix (r : (flag m S).Ri 1) : ambientAction S m (radicalInclusion S m r) w = w := by
      change (Coordinates.sp4 m).conjugationAction _ _ _ _ = _
      rw [Coordinates.conjugationAction_projection]
      congr 2
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hv.2 r r.property)
    apply ((Coordinates.sp4 m).mem_preimage _ v').mpr
    change w ∈ ModelFlag.movedStage (alignment m) 2
    rw [ModelFlag.mem_movedStage]
    apply NaturalScalarCubic.plane_radical_fixed
    intro q hq
    change q ∈ Plane.radical.map planeLocal.subtype at hq
    rw [←alignedRadicalMap_range S m] at hq
    obtain ⟨r,rfl⟩ := hq
    rw [alignedRadicalMap_apply,alignedOperator_apply,smul_inv_smul,hfix]
  · exact le_inf (D.centralQuotientPreimage_le _)
      (le_centralizer_iff.mp (radical_centralizes_plane S m))

/-- Every original radical displacement lies in the entire original plane. -/
theorem commutator_le_plane : ⁅V,(flag m S).Ri 1⁆ ≤ (flag m S).Vi 1 := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro r hr v hv
  let r' : (flag m S).Ri 1 := ⟨r,hr⟩
  let v' : V := ⟨v,hv⟩
  let w : V := V.normalizerMonoidHom (inclusion (ambientJoin_normalizes_seed S)
    (radicalInclusion S m r')) v' * v'⁻¹
  change (w : G) ∈ (flag m S).Vi 1
  apply ((Coordinates.sp4 m).mem_preimage _ w).mpr
  change ((Coordinates.sp4 m).projection w).toAdd ∈ ModelFlag.movedStage (alignment m) 2
  rw [ModelFlag.mem_movedStage]
  change toLinear (alignment m)⁻¹ (((Coordinates.sp4 m).projection w).toAdd) ∈ plane S.field.Carrier
  have he : ((Coordinates.sp4 m).projection w).toAdd =
      ambientAction S m (radicalInclusion S m r') ((Coordinates.sp4 m).projection v').toAdd -
        (show Vector S.field.Carrier from ((Coordinates.sp4 m).projection v').toAdd) := by
    rw [map_mul,map_inv]
    simp only [toAdd_mul,toAdd_inv,←sub_eq_add_neg]
    exact congrArg (fun x : Vector S.field.Carrier => x - (show Vector S.field.Carrier from ((Coordinates.sp4 m).projection v').toAdd))
      ((Coordinates.sp4 m).conjugationAction_projection _ _ _ v').symm
  rw [he,map_sub]
  change (alignment m)⁻¹ • ambientAction S m (radicalInclusion S m r') _ -
      (alignment m)⁻¹ • (show Vector S.field.Carrier from ((Coordinates.sp4 m).projection v').toAdd) ∈ _
  have ha := alignedRadicalMap_apply S m r' ((alignment m)⁻¹ • (show Vector S.field.Carrier from ((Coordinates.sp4 m).projection v').toAdd))
  rw [alignedOperator_apply,smul_inv_smul] at ha
  rw [←ha]
  exact displacement_mem_of_self_orthogonal (plane S.field.Carrier) (by
      ext u
      constructor
      · intro h
        exact (orthogonal_plane_iff u).mp (fun v hv =>
          TwoLocalCover.form_alternating.eq_iff.mp (h v hv))
      · intro h v hv
        exact plane_isotropic v u hv h)
    (alignedRadicalMap S m r') (fun u hu => by
      rw [alignedRadicalMap_apply,radical_aligned_fixes S m r' u hu]) _

/-- Both original local facts used after A ≤ R₂ in source 11.2.4. -/
theorem subgroup_action {A : Subgroup G} (hA : A ≤ (flag m S).Ri 1) :
    A ≤ centralizer ((flag m S).Vi 1 : Set G) ∧ ⁅V,A⁆ ≤ (flag m S).Vi 1 :=
  ⟨hA.trans (radical_centralizes_plane S m),
    (commutator_mono le_rfl hA).trans (commutator_le_plane S m)⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4.RadicalAction
