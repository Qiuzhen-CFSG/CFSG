module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.RadicalAction.Shears

/-!
# The original plane radical acts on the entire chosen cover

The natural plane kernel is O₂(L₂T). Its operators fix the aligned plane,
so their two-power order removes both the field twist and scalar multiplier.
The resulting symplectic homomorphism retains the published flag alignment.
Equality of natural operators lifts to the entire original chosen module
by the two-group kernel comparison, and fixed lifting yields C_T(V₂)=R₂.
No central kernel is discarded or assumed to split.

Source: Aschbacher--Smith, 11.2.4, printed pp.769--770, using I.2.3(1).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Matrix
open scoped MatrixGroups IsMulCommutative
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

def radicalLocal : (flag m S).Ri 1 →* localJoin S m := inclusion (map_subtype_le _)
def radicalInclusion : (flag m S).Ri 1 →* ambientJoin D :=
  (inclusion (localJoin_le_ambient S m)).comp (radicalLocal S m)

theorem radical_fixes_quotient_plane (r : (flag m S).Ri 1)
    (v : (flag m S).space 1) : ambientAction S m (radicalInclusion S m r) v.val = v.val := by
  have hr : radicalLocal S m r ∈ pCore 2 (localJoin S m) := by
    obtain ⟨a,ha,he⟩ := r.property
    have he' : a = radicalLocal S m r := Subtype.ext he
    exact he' ▸ ha
  rw [←quotientPlaneAction_ker] at hr
  exact congrArg Subtype.val (LinearMap.congr_fun hr v)

def alignedOperator : ambientJoin D →*
    (Vector S.field.Carrier ≃ₗ[ZMod 2] Vector S.field.Carrier) :=
  (MulAut.conj (naturalHom (alignment m)⁻¹)).toMonoidHom.comp (linearAction (ambientAction S m))

theorem alignedOperator_apply (g : ambientJoin D) (v : Vector S.field.Carrier) :
    alignedOperator S m g v = (alignment m)⁻¹ •
      (ambientAction S m g ((alignment m) • v)) := by
  change naturalHom (alignment m)⁻¹
    (ambientAction S m g ((naturalHom (alignment m)⁻¹)⁻¹ v)) = _
  rw [←map_inv,inv_inv]
  rfl

theorem alignedOperator_mem_normalizer (g : ambientJoin D) :
    alignedOperator S m g ∈ naturalNormalizer := by
  have ha := (naturalDerivedImage (F := S.field.Carrier)).le_normalizer
    (naturalHom_mem (field_card_gt_two S) (alignment m)⁻¹)
  exact naturalNormalizer.mul_mem (naturalNormalizer.mul_mem ha
    (ambientOperator_mem_normalizer S m g)) (naturalNormalizer.inv_mem ha)

theorem radical_aligned_fixes (r : (flag m S).Ri 1) (v : Vector S.field.Carrier)
    (hv : v ∈ plane S.field.Carrier) :
    alignedOperator S m (radicalInclusion S m r) v = v := by
  have hw : (alignment m) • v ∈ (flag m S).space 1 :=
    ⟨v,hv,rfl⟩
  rw [alignedOperator_apply,radical_fixes_quotient_plane S m r ⟨_,hw⟩,inv_smul_smul]

theorem exists_radical_matrix (r : (flag m S).Ri 1) :
    ∃ g : Sp S.field.Carrier, ∀ v,
      alignedOperator S m (radicalInclusion S m r) v = g • v := by
  have hp : IsPGroup 2 ((flag m S).Ri 1) := pCore_isPGroup.map _
  obtain ⟨k,hk⟩ := hp r
  apply Model.inner_of_twoPower_fixes_plane
    ⟨_,alignedOperator_mem_normalizer S m (radicalInclusion S m r)⟩
    (radical_aligned_fixes S m r) k
  rw [←map_pow,←map_pow,hk,map_one,map_one]

def alignedRadicalMap : (flag m S).Ri 1 →* Sp S.field.Carrier where
  toFun r := (exists_radical_matrix S m r).choose
  map_one' := by
    apply naturalHom_injective
    apply LinearEquiv.ext
    intro v
    change (exists_radical_matrix S m 1).choose • v = (1 : Sp S.field.Carrier) • v
    rw [←(exists_radical_matrix S m 1).choose_spec v,map_one,map_one]
    simp
  map_mul' r t := by
    apply naturalHom_injective
    apply LinearEquiv.ext
    intro v
    change (exists_radical_matrix S m (r*t)).choose • v =
      ((exists_radical_matrix S m r).choose * (exists_radical_matrix S m t).choose) • v
    rw [←(exists_radical_matrix S m (r*t)).choose_spec v,map_mul,map_mul,mul_smul]
    rw [←(exists_radical_matrix S m t).choose_spec v,
      ←(exists_radical_matrix S m r).choose_spec]
    rfl

theorem alignedRadicalMap_apply (r : (flag m S).Ri 1) (v : Vector S.field.Carrier) :
    alignedRadicalMap S m r • v = alignedOperator S m (radicalInclusion S m r) v :=
  ((exists_radical_matrix S m r).choose_spec v).symm

theorem alignedRadicalMap_mem (r : (flag m S).Ri 1) :
    alignedRadicalMap S m r ∈ Plane.radical.map planeLocal.subtype := by
  apply Model.mem_planeRadical_of_fixes
  intro v hv
  rw [alignedRadicalMap_apply,radical_aligned_fixes S m r v hv]

/-- The matrix uses the same alignment as the actual invariant flag. -/
def radicalMap : (flag m S).Ri 1 →* Sp S.field.Carrier :=
  (MulAut.conj (alignment m)).toMonoidHom.comp (alignedRadicalMap S m)

theorem radicalMap_apply (r : (flag m S).Ri 1) (v : Vector S.field.Carrier) :
    radicalMap S m r • v = ambientAction S m (radicalInclusion S m r) v := by
  change ((alignment m) * alignedRadicalMap S m r * (alignment m)⁻¹) • v = _
  rw [mul_smul,mul_smul,alignedRadicalMap_apply,alignedOperator_apply,
    smul_inv_smul,smul_inv_smul]

theorem radicalMap_fullAction (r : (flag m S).Ri 1) (w : D.space) :
    D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (radicalMap S m r) w)) =
      V.normalizerMonoidHom (inclusion (ambientJoin_normalizes_seed S)
        (radicalInclusion S m r)) (D.spaceEquiv (Multiplicative.ofAdd w)) := by
  obtain ⟨l,hl⟩ := (Coordinates.sp4 m).quotientMap_surjective (radicalMap S m r)
  have he : ambientAction S m (inclusion le_sup_left l) =
      ambientAction S m (radicalInclusion S m r) := by
    apply LinearMap.ext
    intro v
    rw [ambientAction_component,hl]
    exact radicalMap_apply S m r v
  have hfull := (ambientAction_eq_iff S m _ _).mp he
  rw [←hl]
  change D.spaceEquiv (Multiplicative.ofAdd
    (Preliminary.markedAction D m (m.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)) w)) = _
  rw [Preliminary.markedAction_mk,←hfull]
  apply Subtype.ext
  rw [D.spaceEquiv_apply]
  change (l : G) * (w.val.toMul.val : G) * (l : G)⁻¹ = _
  rw [←D.spaceEquiv_apply]
  rfl

theorem radical_centralizes_plane :
    (flag m S).Ri 1 ≤ centralizer ((flag m S).Vi 1 : Set G) := by
  intro r hr v hv
  let r' : (flag m S).Ri 1 := ⟨r,hr⟩
  let v' : V := ⟨v,D.centralQuotientPreimage_le _ hv⟩
  let w : D.space := (D.spaceEquiv.symm v').toAdd
  have hproj : Preliminary.markedProjection D m w ∈ (flag m S).space 1 :=
    ((Coordinates.sp4 m).mem_preimage _ v').mp hv
  have hfix : Preliminary.markedAction D m (radicalMap S m r') w = w := by
    apply markedAction_fixed_of_projection_fixed S m
    rw [←show radicalMap S m r' • Preliminary.markedProjection D m w =
      symplecticNatural 2 (radicalMap S m r') (Preliminary.markedProjection D m w) from rfl]
    rw [radicalMap_apply]
    exact radical_fixes_quotient_plane S m r' ⟨_,hproj⟩
  have he := radicalMap_fullAction S m r' w
  rw [hfix] at he
  change D.spaceEquiv (D.spaceEquiv.symm v') =
    V.normalizerMonoidHom (inclusion (ambientJoin_normalizes_seed S)
      (radicalInclusion S m r')) (D.spaceEquiv (D.spaceEquiv.symm v')) at he
  rw [D.spaceEquiv.apply_symm_apply] at he
  have hc : v = r*v*r⁻¹ := congrArg Subtype.val he
  exact (mul_inv_eq_iff_eq_mul.mp hc.symm).symm

theorem sylow_centralizer_plane :
    (T : Subgroup G) ⊓ centralizer ((flag m S).Vi 1 : Set G) = (flag m S).Ri 1 := by
  apply le_antisymm
  · intro x hx
    let a : localJoin S m := ⟨x,mem_sup_right hx.1⟩
    have ha : a ∈ (quotientPlaneAction S m).ker := by
      apply LinearMap.ext
      intro w
      apply Subtype.ext
      obtain ⟨v,hv⟩ := (Coordinates.sp4 m).projection_surjective (Multiplicative.ofAdd w.val)
      have hv' : ((Coordinates.sp4 m).projection v).toAdd = w.val := congrArg Multiplicative.toAdd hv
      have hvp : (v : G) ∈ (flag m S).Vi 1 :=
        ((Coordinates.sp4 m).mem_preimage _ v).mpr (hv'.symm ▸ w.property)
      change ambientAction S m (inclusion (localJoin_le_ambient S m) a) w.val = w.val
      rw [←hv']
      change (Coordinates.sp4 m).conjugationAction _ _ _ _ = _
      rw [Coordinates.conjugationAction_projection]
      congr 2
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hx.2 v.val hvp).symm
    rw [quotientPlaneAction_ker] at ha
    exact mem_map_of_mem _ ha
  · exact le_inf (localRadical_le_sylow _) (radical_centralizes_plane S m)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4.RadicalAction
