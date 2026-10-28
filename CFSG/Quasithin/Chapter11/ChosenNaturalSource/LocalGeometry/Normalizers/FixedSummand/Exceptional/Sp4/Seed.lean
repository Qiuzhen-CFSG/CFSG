module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.Sp4Core
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic.Cover

/-!
# The original symplectic point-core displacement

Every point-local displacement lies in the perpendicular hyperplane.
The literal point-radical matrices realize every vector of that hyperplane
as a displacement of the fourth basis vector. The long-root theorem for
the original central cover also puts its entire central kernel in this
commutator. Thus [V,O₂(L₁)]=[V,L₁]=V₃ for the caller's actual invariant
flag, even when V is a nonsplit central cover of the natural module.

These identities supply the intrinsic V₃ construction in the exceptional
point-radical argument. All projections and conjugations are the original
ones, with the actual symplectic alignment retained.
Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
11.1.5, printed p.766, using I.2.3(1b), printed p.413.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Matrix
open scoped IsMulCommutative commutatorElement
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Sp4
open PointCohomology.PointGeometry.Sp4Core
open WeakClosure.Nonnormalization.RootParabolic
open Representation.SymplecticFourOrthogonalCover
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (m : ActionEquiv D.centralQuotientAction
    (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
  (f : InvariantFlag (Coordinates.sp4 m))

private theorem root_image (t : S.field.Carrier) :
    LocalGeometry.Sp4.alignment m *
      Representation.OneCohomology.SymplecticFour.rootElement 0 t *
      (LocalGeometry.Sp4.alignment m)⁻¹ ∈ modelImage D S m ((f.Li 0).pCoreIn 2) := by
  rw [modelImage_core D S m (f.Li 0) ((localResidual_le _).trans inf_le_left),
    modelImage_point, ←map_pCoreIn_of_injective 2 _ _
      (MulAut.conj (LocalGeometry.Sp4.alignment m)).injective]
  exact mem_map_of_mem _ (root_mem_point_core D S t)

/-- The original central kernel occurs in the point-core commutator. -/
theorem central_le_core_commutator :
    V ⊓ centralizer (L : Set G) ≤ ⁅V,(f.Li 0).pCoreIn 2⁆ := by
  obtain ⟨a,ha⟩ := (Coordinates.sp4 m).quotientMap_surjective (LocalGeometry.Sp4.alignment m)
  let g := PointCohomology.SymplecticModel.actor D S m a
  have hg : g.val = LocalGeometry.Sp4.alignment m :=
    (PointCohomology.SymplecticModel.actor_val D S m a).trans ha
  let C : Submodule (ZMod 2) D.space := AddSubgroup.toZModSubmodule 2
    (AddSubgroup.toSubgroup.symm ((⁅(f.Li 0).pCoreIn 2,V⁆).comap
      (V.subtype.comp D.spaceEquiv.toMonoidHom)))
  have hC : Coinvariants.ker ((sp4CoverAction D S m).comp (Roots.conjugateGroup g).subtype) ≤ C := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨q,x⟩,rfl⟩
    obtain ⟨r,hr,he⟩ := q.property
    obtain ⟨t,ht⟩ := (RootSubgroup.mem_group_iff 0 r.val).mp hr
    have hq : q.val.val ∈ modelImage D S m ((f.Li 0).pCoreIn 2) := by
      rw [←he]
      change g.val*r.val*g.val⁻¹ ∈ _
      rw [hg,←ht]
      exact root_image D S m f t
    obtain ⟨l,hl,hlq⟩ := hq
    have hact : sp4CoverAction D S m q.val x = D.chosenAction l x := by
      change Preliminary.markedAction D m q.val.val x = _
      rw [←hlq]
      exact Preliminary.markedAction_mk D m l x
    change (D.spaceEquiv (Multiplicative.ofAdd (sp4CoverAction D S m q.val x-x)) : G) ∈
      ⁅(f.Li 0).pCoreIn 2,V⁆
    rw [hact,ofAdd_sub,div_eq_mul_inv,map_mul,map_inv]
    simp only [Subgroup.coe_mul,Subgroup.coe_inv]
    rw [D.spaceEquiv_apply]
    change (l : G)*(x.val.toMul.val : G)*(l : G)⁻¹*
      (D.spaceEquiv (Multiplicative.ofAdd x) : G)⁻¹ ∈ _
    rw [←D.spaceEquiv_apply]
    exact commutator_mem_commutator hl (D.spaceEquiv (Multiplicative.ofAdd x)).property
  have hcard : 2 < Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    simpa only [pow_one] using pow_lt_pow_right₀ (by decide : 1 < (2 : ℕ)) S.nonbinary
  have hroot := (Roots.cover_conjugate_root_geometry hcard g
    (sp4CoverProjection D S m) (sp4CoverProjection_isCover D S m)).2.1
  rw [←hroot] at hC
  intro v hv
  let v' : V := ⟨v,hv.1⟩
  let w : D.space := (D.spaceEquiv.symm v').toAdd
  have hz : sp4CoverProjection D S m w = 0 := by
    change (Coordinates.sp4 m).projection v' = 1
    exact ((Coordinates.sp4 m).projection_eq_one_iff v').mpr hv.2
  have hw : w ∈ ((Roots.conjugateLine g).restrictScalars (ZMod 2)).comap
      (sp4CoverProjection D S m).toLinearMap := by
    change sp4CoverProjection D S m w ∈ Roots.conjugateLine g
    rw [hz]
    exact Submodule.zero_mem _
  have hh := hC hw
  change (D.spaceEquiv (D.spaceEquiv.symm v') : G) ∈ ⁅(f.Li 0).pCoreIn 2,V⁆ at hh
  rw [D.spaceEquiv.apply_symm_apply,commutator_comm] at hh
  exact hh

private theorem third_space :
    f.space 2 = LocalGeometry.Sp4.space m 3 :=
  LocalGeometry.Sp4.space_inner_unique m 2 (f.space 2) (f.dimension 2)
    (inf_le_left.trans (f.invariant 2))

private theorem model_first_displacement (l : L) (hl : (l : G) ∈ f.Li 0)
    (x : Vector S.field.Carrier) :
    (show Sp S.field.Carrier from (Coordinates.sp4 m).quotientMap l) • x-x ∈ f.space 2 := by
  have hi : (Coordinates.sp4 m).quotientMap l ∈ modelImage D S m (f.Li 0) :=
    mem_map_of_mem _ hl
  rw [modelImage_point] at hi
  obtain ⟨b,hb,he⟩ := hi
  let g := LocalGeometry.Sp4.alignment m
  have hd : b • (g⁻¹ • x) - g⁻¹ • x ∈ LocalGeometry.Sp4.ModelFlag.hyperplane := by
    rw [LocalGeometry.Sp4.ModelFlag.mem_hyperplane]
    change (b.val *ᵥ (g⁻¹ • x)) (.inr 0) - (g⁻¹ • x) (.inr 0) = 0
    have hr (j) : b.val (.inr 0) j = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) S.field.Carrier) (.inr 0) j :=
      pointLocal_row (⟨b,hb⟩ : pointLocal) j
    simp only [Matrix.mulVec,dotProduct,hr]
    simp
  rw [third_space]
  apply (LocalGeometry.Sp4.ModelFlag.mem_movedStage g 3 _).mpr
  rw [←he]
  change toLinear g⁻¹ ((g*b*g⁻¹) • x-x) ∈ _
  rw [map_sub]
  change g⁻¹ • ((g*b*g⁻¹) • x) - g⁻¹ • x ∈ LocalGeometry.Sp4.ModelFlag.hyperplane
  simpa only [mul_smul,inv_smul_smul] using hd

/-- Every displacement of the point residual lies in the original third space. -/
theorem seed_first_commutator_le : ⁅V,f.Li 0⁆ ≤ f.Vi 2 := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro l hl v hv
  let l' : L := ⟨l,((localResidual_le _).trans inf_le_left) hl⟩
  let v' : V := ⟨v,hv⟩
  let d : V := V.normalizerMonoidHom (inclusion D.normalizes l') v' * v'⁻¹
  change (d : G) ∈ (Coordinates.sp4 m).preimage (f.space 2)
  apply ((Coordinates.sp4 m).mem_preimage _ d).mpr
  change ((Coordinates.sp4 m).projection d).toAdd ∈ f.space 2
  rw [map_mul,map_inv]
  simp only [toAdd_mul,toAdd_inv,←sub_eq_add_neg]
  rw [(Coordinates.sp4 m).projection_component_conjugation]
  exact model_first_displacement D S m f l' hl _

private theorem model_core_displacement (u : Vector S.field.Carrier)
    (hu : u ∈ LocalGeometry.Sp4.ModelFlag.hyperplane) :
    ∃ q : Sp S.field.Carrier, q ∈ (pointLocal (F := S.field.Carrier)).pCoreIn 2 ∧
      ∃ x : Vector S.field.Carrier, q • x-x=u := by
  let r := pointRadicalElement (u (.inl 1)) (u (.inr 1)) (u (.inl 0))
  refine ⟨r.val,?_,Pi.single (.inr 0) 1,?_⟩
  · change r.val ∈ (pCore 2 (pointLocal (F := S.field.Carrier))).map pointLocal.subtype
    rw [pointLocal_core_eq S.field.card_eq S.nonbinary]
    exact mem_map_of_mem _ (pointRadicalElement_mem _ _ _)
  · have hz := (LocalGeometry.Sp4.ModelFlag.mem_hyperplane u).mp hu
    ext i
    fin_cases i <;> simp [r,pointRadicalElement,pointRadicalMatrix,
      Matrix.mulVec_single,hz]

/-- The original third space is generated by point-core displacements,
including the entire central kernel of the original module. -/
theorem seed_core_commutator : ⁅V,(f.Li 0).pCoreIn 2⁆ = f.Vi 2 := by
  apply le_antisymm ((commutator_mono le_rfl (pCoreIn_le 2 _)).trans
    (seed_first_commutator_le D S m f))
  intro v hv
  let v' : V := ⟨v,D.centralQuotientPreimage_le _ hv⟩
  let u : Vector S.field.Carrier := ((Coordinates.sp4 m).projection v').toAdd
  let g := LocalGeometry.Sp4.alignment m
  have hu : g⁻¹ • u ∈ LocalGeometry.Sp4.ModelFlag.hyperplane := by
    have h := ((Coordinates.sp4 m).mem_preimage _ v').mp hv
    rw [third_space] at h
    exact (LocalGeometry.Sp4.ModelFlag.mem_movedStage g 3 u).mp h
  obtain ⟨q,hq,x,hx⟩ := model_core_displacement D S (g⁻¹ • u) hu
  have hi : g*q*g⁻¹ ∈ modelImage D S m ((f.Li 0).pCoreIn 2) := by
    rw [modelImage_core D S m (f.Li 0) ((localResidual_le _).trans inf_le_left),
      modelImage_point,←map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective]
    exact mem_map_of_mem _ hq
  obtain ⟨l,hl,hlq⟩ := hi
  obtain ⟨w,hw⟩ := (Coordinates.sp4 m).projection_surjective (Multiplicative.ofAdd (g • x))
  let d : V := V.normalizerMonoidHom (inclusion D.normalizes l) w * w⁻¹
  have hd : ((Coordinates.sp4 m).projection d).toAdd = u := by
    rw [map_mul,map_inv]
    simp only [toAdd_mul,toAdd_inv,←sub_eq_add_neg]
    rw [(Coordinates.sp4 m).projection_component_conjugation,hw]
    change m.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) • (g • x)-g • x = u
    change m.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) = g*q*g⁻¹ at hlq
    rw [hlq,mul_smul,mul_smul,inv_smul_smul]
    change toLinear g (q • x)-toLinear g x=u
    rw [←map_sub,hx]
    exact smul_inv_smul g u
  have hk : (v'*d⁻¹ : V) ∈ (Coordinates.sp4 m).projection.ker := by
    change (Coordinates.sp4 m).projection (v'*d⁻¹) = 1
    rw [map_mul,map_inv]
    exact mul_inv_eq_one.mpr (Multiplicative.toAdd.injective hd.symm)
  have hc : (v'*d⁻¹ : V).val ∈ ⁅V,(f.Li 0).pCoreIn 2⁆ := by
    apply central_le_core_commutator D S m f
    exact ⟨(v'*d⁻¹).property,((Coordinates.sp4 m).projection_eq_one_iff _).mp hk⟩
  have hdc : (d : G) ∈ ⁅V,(f.Li 0).pCoreIn 2⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator hl w.property
  simpa only [Subgroup.coe_mul,Subgroup.coe_inv,inv_mul_cancel_right] using
    (⁅V,(f.Li 0).pCoreIn 2⁆).mul_mem hc hdc

/-- The literal point residual has exactly V₃ as its moved space. -/
theorem seed_first_commutator : ⁅V,f.Li 0⁆ = f.Vi 2 :=
  le_antisymm (seed_first_commutator_le D S m f)
    ((seed_core_commutator D S m f).symm.le.trans
      (commutator_mono le_rfl (pCoreIn_le 2 _)))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Sp4
