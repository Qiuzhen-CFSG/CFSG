module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Exceptional.SL3.CentralLayer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.Quotient.ModelCocycles
/-!
# The second natural section of the literal SL₃ point residual

Conjugating the original component marking to the caller's first line gives
an onto map L₁ → F² ⋊ SL₂(F). Its kernel is VZ(L₁): the cohomological
identity O₂(LT)=VC_T(L) proves one containment, and the centerless marked
point residual proves the other. Restricting to the two-cores and then
factoring by the original center produces an equivariant onto map whose
kernel is precisely the original seed image. Both factors have order q²,
so the literal central core section has order q⁴, including at q=4 and
without assuming a splitting of the central extension.

The final theorem applies this count to the existing exceptional escape
contradiction, removing its section-order premise. The central-commutator
bound, fixed-free-five action, Sp₄ action, TI centralizer control and final
assembly remain with qt-d-1222-natural-point-fixed-summand. The enclosing
source assembly owner is qt-d-1222-natural-normalizer-source.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004, 11.1.5,
printed p.766, using the point-local geometry of pp.760–761 and the
corrected C.1.13 denominator on pp.124–125.
-/

open Subgroup Theory.GroupTheory Representation Matrix
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.SL3
open Matrix.PSL3.LinearThree Matrix.PSL3.PointRadicalGeneration
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

private theorem point_center_trivial {F : Type*} [Field F] :
    center (pointLocalSL F) = ⊥ := by
  apply (center (pointLocalSL F)).eq_bot_iff_forall.mpr
  intro z hz
  have ht (i j : Fin 3) (hij : i ≠ j) (hj : j ≠ 0) :
      SpecialLinearGroup.transvection hij (1 : F) ∈ pointLocalSL F := by
    apply (mem_pointLocalSL_iff F _).mpr
    simp [SpecialLinearGroup.transvection_coe, Matrix.single, hj]
  have he (i j : Fin 3) (hij : i ≠ j) (hj : j ≠ 0) :
      z.val.val * (1 + Matrix.single i j 1) =
        (1 + Matrix.single i j 1) * z.val.val := by
    have h := congrArg (fun g : pointLocalSL F => g.val.val)
      (mem_center_iff.mp hz ⟨SpecialLinearGroup.transvection hij (1 : F),ht i j hij hj⟩)
    change (SpecialLinearGroup.transvection hij (1 : F)).val * z.val.val =
      z.val.val * (SpecialLinearGroup.transvection hij (1 : F)).val at h
    simpa only [SpecialLinearGroup.transvection_coe] using h.symm
  have h01 := he 0 1 (by decide) (by decide)
  have h02 := he 0 2 (by decide) (by decide)
  have h12 := he 1 2 (by decide) (by decide)
  have h21 := he 2 1 (by decide) (by decide)
  have hc := (mem_pointLocalSL_iff F z.val).mp z.property
  have h11 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 1) h01
  have h22 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 2) h02
  have h12' := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 2) h01
  have h21' := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 1) h02
  have h01' := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 2) h12
  have h02' := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 1) h21
  simp [Matrix.mul_apply,Fin.sum_univ_three, Matrix.single, hc.1] at h11 h22 h12' h21' h01' h02'
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (Coordinates.sl3 m))
    (a : SL(3,S.field.Carrier)) (ha : conjugatePoint standardPoint a = f.space 0)

include ha in
private theorem marked_mem (l : f.Li 0) :
    a * PointCohomology.PointGeometry.SL3Core.componentMap D S m
      ⟨l, ((localResidual_le _).trans inf_le_left) l.property⟩ * a⁻¹ ∈
      pointLocalSL S.field.Carrier := by
  have hi := PointCohomology.PointGeometry.SL3Core.componentImage_residual_conjugate D S m f a ha
  have hl : PointCohomology.PointGeometry.SL3Core.componentMap D S m
      ⟨l, ((localResidual_le _).trans inf_le_left) l.property⟩ ∈
        PointCohomology.PointGeometry.SL3Core.componentImage D S m (f.Li 0) :=
    ⟨_,l.property,rfl⟩
  rw [hi] at hl
  obtain ⟨t,ht,he⟩ := hl
  change t ∈ pointLocalSL S.field.Carrier at ht
  change a⁻¹*t*a⁻¹⁻¹ = _ at he
  rw [←he,inv_inv]
  simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using ht

def pointProjection : f.Li 0 →* pointLocalSL S.field.Carrier :=
  (((MulAut.conj a).toMonoidHom.comp
    (PointCohomology.PointGeometry.SL3Core.componentMap D S m)).comp
      (inclusion ((localResidual_le _).trans inf_le_left))).codRestrict _ (by exact marked_mem D S m f a ha)

theorem pointProjection_surjective : Function.Surjective (pointProjection D S m f a ha) := by
  intro t
  have hi := PointCohomology.PointGeometry.SL3Core.componentImage_residual_conjugate D S m f a ha
  have ht : a⁻¹*t.val*a ∈
      PointCohomology.PointGeometry.SL3Core.componentImage D S m (f.Li 0) := by
    rw [hi]
    exact ⟨t.val,t.property,by simp⟩
  obtain ⟨l,hl,he⟩ := ht
  refine ⟨⟨l,hl⟩,Subtype.ext ?_⟩
  change a * PointCohomology.PointGeometry.SL3Core.componentMap D S m l * a⁻¹ = t.val
  change PointCohomology.PointGeometry.SL3Core.componentMap D S m l = a⁻¹*t.val*a at he
  rw [he]
  group

theorem pointProjection_kernel_mem (l : f.Li 0) :
    l ∈ (pointProjection D S m f a ha).ker ↔ (l : G) ∈ L.pCoreIn 2 := by
  change pointProjection D S m f a ha l = 1 ↔ _
  rw [Subtype.ext_iff]
  change a * PointCohomology.PointGeometry.SL3Core.componentMap D S m
    ⟨l, ((localResidual_le _).trans inf_le_left) l.property⟩ * a⁻¹ = 1 ↔ _
  rw [mul_inv_eq_one, mul_eq_left]
  change _ ∈ (PointCohomology.PointGeometry.SL3Core.componentMap D S m).ker ↔ _
  rw [PointCohomology.PointGeometry.SL3Core.componentMap_ker]
  constructor
  · intro h
    exact mem_map_of_mem L.subtype h
  · rintro ⟨x,hx,he⟩
    have he' : x = (⟨l,((localResidual_le _).trans inf_le_left) l.property⟩ : L) :=
      Subtype.ext he
    exact he' ▸ hx

theorem pointProjection_kernel_pgroup : IsPGroup 2 (pointProjection D S m f a ha).ker := by
  let j : (pointProjection D S m f a ha).ker →* L.pCoreIn 2 :=
    { toFun := fun x => ⟨x.val.val,(pointProjection_kernel_mem D S m f a ha x.val).mp x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  apply (isPGroup_pCoreIn 2 L).of_injective j
  intro x y h
  have he := congrArg (fun z : L.pCoreIn 2 => (z : G)) h
  exact Subtype.ext (Subtype.ext he)

theorem pointProjection_center_le_kernel :
    center (f.Li 0) ≤ (pointProjection D S m f a ha).ker := by
  intro z hz
  have hc : pointProjection D S m f a ha z ∈ center (pointLocalSL S.field.Carrier) := by
    apply mem_center_iff.mpr
    intro x
    obtain ⟨y,rfl⟩ := pointProjection_surjective D S m f a ha x
    simpa only [map_mul] using congrArg (pointProjection D S m f a ha) (mem_center_iff.mp hz y)
  rwa [point_center_trivial,mem_bot] at hc

/-- The entire center is a two-subgroup, so the source central denominator
agrees with its intersection with the intrinsic two-core. -/
theorem first_center_le_core : center (f.Li 0) ≤ pCore 2 (f.Li 0) := by
  obtain ⟨a,ha⟩ := exists_standardPoint_conjugator (f.space 0) (f.dimension 0)
  exact (pointProjection_center_le_kernel D S m f a ha).trans
    (le_sSup ⟨inferInstance,pointProjection_kernel_pgroup D S m f a ha⟩)

theorem pointProjection_kernel (hb : ChapterC.IsShort L) :
    (pointProjection D S m f a ha).ker = V.subgroupOf (f.Li 0) ⊔ center (f.Li 0) := by
  apply le_antisymm
  · intro l hl
    have hlP := (pointProjection_kernel_mem D S m f a ha l).mp hl
    have hPQ : L.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
      pCoreIn_mono_of_normalizes le_sup_left (sup_le L.le_normalizer D.sylow_normalizes_component)
    have hlQ := hPQ hlP
    rw [PointCohomology.sl3_core_eq_denominator D S m hb] at hlQ
    obtain ⟨v,hv,z,hz,he⟩ := PointCohomology.denominator_factor D hlQ
    have hvA := (seed_le_first_core D S m f).trans (pCoreIn_le 2 _) hv
    have hzA : z ∈ f.Li 0 := by
      have h := (f.Li 0).mul_mem ((f.Li 0).inv_mem hvA) l.property
      rwa [←he,inv_mul_cancel_left] at h
    have hzZ : (⟨z,hzA⟩ : f.Li 0) ∈ center (f.Li 0) := by
      apply mem_center_iff.mpr
      intro x
      exact Subtype.ext (hz.2 x ((localResidual_le _).trans inf_le_left x.property))
    have h := (V.subgroupOf (f.Li 0) ⊔ center (f.Li 0)).mul_mem
      ((le_sup_left : V.subgroupOf (f.Li 0) ≤ _) (show (⟨v,hvA⟩ : f.Li 0) ∈ V.subgroupOf (f.Li 0) from hv))
      ((le_sup_right : center (f.Li 0) ≤ _) hzZ)
    exact (Subtype.ext he : (⟨v,hvA⟩ : f.Li 0) * ⟨z,hzA⟩ = l) ▸ h
  · apply sup_le
    · intro v hv
      exact (pointProjection_kernel_mem D S m f a ha v).mpr (D.le_componentCore hv)
    · exact pointProjection_center_le_kernel D S m f a ha

/-- The core image under the original marked point map is the full model core. -/
theorem pointProjection_core_image :
    (pCore 2 (f.Li 0)).map (pointProjection D S m f a ha) =
      pCore 2 (pointLocalSL S.field.Carrier) := by
  rw [← (pointProjection D S m f a ha).comap_pCore_of_ker_isPGroup
    (pointProjection_surjective D S m f a ha) (pointProjection_kernel_pgroup D S m f a ha),
    map_comap_eq_self_of_surjective (pointProjection_surjective D S m f a ha)]

/-- The marked point map restricted to the intrinsic two-core. -/
def corePointProjection : pCore 2 (f.Li 0) →* pCore 2 (pointLocalSL S.field.Carrier) :=
  ((pointProjection D S m f a ha).comp (pCore 2 (f.Li 0)).subtype).codRestrict _ (by
    intro x
    rw [← pointProjection_core_image D S m f a ha]
    exact mem_map_of_mem _ x.property)

theorem corePointProjection_surjective :
    Function.Surjective (corePointProjection D S m f a ha) := by
  intro x
  have hx : x.val ∈ (pCore 2 (f.Li 0)).map (pointProjection D S m f a ha) := by
    rw [pointProjection_core_image D S m f a ha]
    exact x.property
  obtain ⟨y,hy,he⟩ := hx
  exact ⟨⟨y,hy⟩,Subtype.ext he⟩

private theorem corePointProjection_kills_center :
    (center (f.Li 0)).subgroupOf (pCore 2 (f.Li 0)) ≤
      (corePointProjection D S m f a ha).ker := by
  intro x hx
  exact Subtype.ext (pointProjection_center_le_kernel D S m f a ha hx)

/-- The second-factor projection on the literal central core section. -/
def sectionPointProjection : CoreCentralSection (f.Li 0) →*
    pCore 2 (pointLocalSL S.field.Carrier) :=
  QuotientGroup.lift _ (corePointProjection D S m f a ha)
    (by exact corePointProjection_kills_center D S m f a ha)

theorem sectionPointProjection_surjective :
    Function.Surjective (sectionPointProjection D S m f a ha) :=
  QuotientGroup.lift_surjective_of_surjective _ _
    (corePointProjection_surjective D S m f a ha) _

/-- The seed inclusion has precisely its original subgroup as range in the core. -/
theorem seedCoreMap_range :
    (seedCoreMap D S m f).range = (V.subgroupOf (f.Li 0)).subgroupOf (pCore 2 (f.Li 0)) := by
  ext x
  constructor
  · rintro ⟨v,rfl⟩
    exact v.property
  · intro hx
    refine ⟨⟨x.val.val,hx⟩,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl

private theorem corePointProjection_kernel (hb : ChapterC.IsShort L) :
    (corePointProjection D S m f a ha).ker =
      (V.subgroupOf (f.Li 0)).subgroupOf (pCore 2 (f.Li 0)) ⊔
      (center (f.Li 0)).subgroupOf (pCore 2 (f.Li 0)) := by
  have hK : (pointProjection D S m f a ha).ker ≤ pCore 2 (f.Li 0) :=
    le_sSup ⟨inferInstance,pointProjection_kernel_pgroup D S m f a ha⟩
  have he : (corePointProjection D S m f a ha).ker =
      ((pointProjection D S m f a ha).ker).subgroupOf (pCore 2 (f.Li 0)) := by
    ext x
    exact Subtype.ext_iff
  rw [he,pointProjection_kernel D S m f a ha hb]
  rw [pointProjection_kernel D S m f a ha hb] at hK
  exact subgroupOf_sup (le_sup_left.trans hK) (le_sup_right.trans hK)

/-- The second-factor kernel is the actual seed image in O₂(L₁)/Z(L₁). -/
theorem sectionPointProjection_kernel (hb : ChapterC.IsShort L) :
    (sectionPointProjection D S m f a ha).ker = (seedSectionMap D S m f).range := by
  rw [sectionPointProjection,QuotientGroup.ker_lift,
    corePointProjection_kernel D S m f a ha hb,Subgroup.map_sup,QuotientGroup.map_mk'_self,sup_bot_eq]
  change _ = ((QuotientGroup.mk' _).comp (seedCoreMap D S m f)).range
  rw [MonoidHom.range_comp,seedCoreMap_range D S m f]

/-- The projection is equivariant for the same original inner action. -/
theorem sectionPointProjection_conjugation (l : f.Li 0) (x : CoreCentralSection (f.Li 0)) :
    sectionPointProjection D S m f a ha (ChiefSection.innerAction (f.Li 0) l x) =
      MulAut.characteristic (pCore 2 (pointLocalSL S.field.Carrier))
        (MulAut.conj (pointProjection D S m f a ha l))
        (sectionPointProjection D S m f a ha x) := by
  obtain ⟨q,rfl⟩ := QuotientGroup.mk'_surjective
    ((center (f.Li 0)).subgroupOf (pCore 2 (f.Li 0))) x
  apply Subtype.ext
  change pointProjection D S m f a ha (l * q.val * l⁻¹) = _
  simp only [map_mul,map_inv]
  rfl

private theorem point_core_card {F : Type*} [Field F] [Finite F] [CharP F 2] :
    Nat.card (pCore 2 (pointLocalSL F)) = Nat.card F ^ 2 := by
  let e := pointLocalAffineEquiv F
  calc
    _ = Nat.card ((pCore 2 (pointLocalSL F)).map e.toMonoidHom) :=
      Nat.card_congr ((pCore 2 (pointLocalSL F)).equivMapOfInjective e.toMonoidHom e.injective).toEquiv
    _ = Nat.card (Matrix.SL2.translations F) := by
      rw [pCore_map_iso, Matrix.SL2.affine_twoCore_eq]
    _ = Nat.card (Multiplicative (Fin 2 → F)) :=
      Nat.card_congr (Matrix.SL2.translationsEquiv F).symm.toEquiv
    _ = Nat.card F ^ 2 := by
      change Nat.card (Fin 2 → F) = _
      rw [Nat.card_fun, Nat.card_fin]

/-- The second literal chief section has order q², including the central kernel. -/
theorem seedSectionMap_range_index (hb : ChapterC.IsShort L) :
    (seedSectionMap D S m f).range.index = (2 ^ S.field.degree) ^ 2 := by
  obtain ⟨a,ha⟩ := exists_standardPoint_conjugator (f.space 0) (f.dimension 0)
  let Q := pCore 2 (f.Li 0)
  let U := V.subgroupOf (f.Li 0)
  let Z := center (f.Li 0)
  let q := QuotientGroup.mk' (Z.subgroupOf Q)
  let p := (pointProjection D S m f a ha).comp Q.subtype
  have hK : (pointProjection D S m f a ha).ker ≤ Q :=
    le_sSup ⟨inferInstance, pointProjection_kernel_pgroup D S m f a ha⟩
  have hUZ : U ⊔ Z ≤ Q := by
    rw [← pointProjection_kernel D S m f a ha hb]
    exact hK
  have hr : (seedSectionMap D S m f).range = (U.subgroupOf Q).map q := by
    change (q.comp (seedCoreMap D S m f)).range = _
    rw [MonoidHom.range_comp,seedCoreMap_range D S m f]
  have hker : p.ker = U.subgroupOf Q ⊔ Z.subgroupOf Q := by
    change ((pointProjection D S m f a ha).ker).subgroupOf Q = _
    rw [pointProjection_kernel D S m f a ha hb,
      subgroupOf_sup (le_sup_left.trans hUZ) (le_sup_right.trans hUZ)]
  have hp : p.range = pCore 2 (pointLocalSL S.field.Carrier) := by
    rw [MonoidHom.range_comp, range_subtype]
    exact pointProjection_core_image D S m f a ha
  rw [hr, index_map, QuotientGroup.ker_mk',
    MonoidHom.range_eq_top_of_surjective q (QuotientGroup.mk'_surjective _), index_top,mul_one,
    ←hker,index_ker,hp,point_core_card,S.field.card_eq]

/-- Both literal factors together have order q⁴. -/
theorem coreCentralSection_card (hb : ChapterC.IsShort L) :
    Nat.card (CoreCentralSection (f.Li 0)) = (2 ^ S.field.degree) ^ 4 := by
  rw [←(seedSectionMap D S m f).range.card_mul_index,
    seedSectionMap_range_card D S m f, seedSectionMap_range_index D S m f hb]
  ring

open Representation.GoldschmidtONan Representation.BinaryOffender

/-- In the exceptional GO case the literal central section has order 256. -/
theorem exceptional_coreCentralSection_card (hb : ChapterC.IsShort L) (X : Subgroup G)
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (hfixed : fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) =
      fixedSubspace (f.Ri 0) L)
    (he : ExceptionalCase (representation (f.Ri 0)) (cartanImage (f.Ri 0) X)) :
    Nat.card (CoreCentralSection (f.Li 0)) = 256 := by
  rw [coreCentralSection_card D S m f hb,
    (chosen_exceptional_parameters D S f X hcenter hfixed he).1]
  norm_num

/-- Application to the original exceptional contradiction, with the entire
section-order premise discharged by the two literal factors. -/
theorem exceptional_escape_of_short_actions (hb : ChapterC.IsShort L)
    (X : Subgroup G)
    (hescape : ¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G))
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (h : Input (representation (f.Ri 0)) (cartanImage (f.Ri 0) X))
    (hfixed : fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) =
      fixedSubspace (f.Ri 0) L)
    (he : ExceptionalCase (representation (f.Ri 0)) (cartanImage (f.Ri 0) X))
    (hc : ⁅pCore 2 (f.Li 0), pCore 2 (f.Li 0)⁆ ≤ center (f.Li 0))
    (B : Subgroup (MulAut (CoreCentralSection (f.Li 0))))
    (hB : B ≤ (ChiefSection.innerAction (f.Li 0)).range)
    (hBcard : Nat.card B = 5)
    (hBfixed : FixedPoints.subgroup B (CoreCentralSection (f.Li 0)) = ⊥) : False :=
  exceptional_escape_of_short_sections D S m f hb X hescape hcenter h hfixed he hc
    (exceptional_coreCentralSection_card D S m f hb X hcenter hfixed he) B hB hBcard hBfixed

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.SL3
