module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.SL3Core.Point
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.SL3Core.Transport

/-!
# The original SL₃ point-radical product

The marked point residual becomes the standard inner local in the actual
projective action. Its normalizing Sylow image introduces no additional
local core. Lifting this image comparison through the Sylow intersection
of the original action kernel gives R₁=O₂(L₁)O₂(LT).

Source: Aschbacher–Smith 11.1.5, printed pp.765–766. This uses the same
model comparison as Closure.Linear.Outside.Multiplicity.RadicalImage.Comparison,
with the original invariant flag throughout.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Matrix
open scoped MatrixGroups
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.SL3Core
open LocalGeometry Matrix.PSL3 Matrix.PSL3.PointRadicalGeneration
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
  (a : SL(3, S.field.Carrier))

/-- On subgroups of L, the projective action is the marked inner action. -/
theorem image_component (A : Subgroup G) (hA : A ≤ L) :
    image D S m a A = ((componentImage D S m A).map (MulAut.conj a).toMonoidHom).map
      (MulAut.conj.comp (projection S.field.Carrier)) := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨MulAut.conj a (componentMap D S m ⟨x,hA hx⟩),
      ⟨componentMap D S m ⟨x,hA hx⟩,⟨⟨x,hA hx⟩,hx,rfl⟩,rfl⟩,?_⟩
    exact (projectiveAction_component D S m a ⟨x,hA hx⟩).symm
  · rintro ⟨y,⟨s,⟨l,hl,rfl⟩,rfl⟩,rfl⟩
    refine ⟨inclusion le_sup_left l,hl,?_⟩
    exact projectiveAction_component D S m a l

/-- Rotating the genuine line sends the actual L₁ image to the standard inner local. -/
theorem image_residual
    (f : InvariantFlag (Coordinates.sl3 m))
    (ha : conjugatePoint standardPoint a = f.space 0) :
    image D S m a (f.Li 0) = (LinearThree.OuterExtensions.localFactor S.field.Carrier true).map MulAut.conj := by
  rw [image_component D S m a (f.Li 0) ((localResidual_le _).trans inf_le_left),
    componentImage_residual_conjugate D S m f a ha]
  have he : (MulAut.conj a).toMonoidHom.comp (MulAut.conj a⁻¹).toMonoidHom =
      MonoidHom.id SL(3,S.field.Carrier) := by
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  rw [Subgroup.map_map _ (MulAut.conj a).toMonoidHom,he,Subgroup.map_id,← Subgroup.map_map]
  rfl

private theorem image_sup (A B : Subgroup G)
    (hA : A ≤ L ⊔ (T : Subgroup G)) (hB : B ≤ L ⊔ (T : Subgroup G)) :
    image D S m a (A ⊔ B) = image D S m a A ⊔ image D S m a B := by
  unfold image
  rw [subgroupOf_sup hA hB,Subgroup.map_sup]

private theorem preserves_of_normalizes_inner
    (U : Subgroup PSL(3,S.field.Carrier))
    (b : MulAut PSL(3,S.field.Carrier))
    (hb : b ∈ normalizer (U.map MulAut.conj : Set _)) : U.map b.toMonoidHom = U := by
  rw [mem_normalizer_iff_map_conj_eq] at hb
  have he : (MulAut.conj b : MulAut PSL(3,S.field.Carrier) →* _).comp MulAut.conj =
      MulAut.conj.comp b.toMonoidHom := by
    ext x y
    simp
  rw [Subgroup.map_map,he,←Subgroup.map_map] at hb
  exact map_injective (Matrix.PSL3.ExtensionBorel.inner_injective S.field.Carrier) hb

/-- The native outer-extension core calculation now applies to the original R₁. -/
theorem radical_image_le_closure (f : InvariantFlag (Coordinates.sl3 m))
    (ha : conjugatePoint standardPoint a = f.space 0) :
    image D S m a (f.Ri 0) ≤ image D S m a ((f.Li 0).pCoreIn 2) := by
  have hKL' : (f.Li 0) ≤ L := (localResidual_le _).trans inf_le_left
  have hlocal : image D S m a (f.Li 0) =
      (LinearThree.OuterExtensions.localFactor S.field.Carrier true).map MulAut.conj := by
    exact image_residual D S m a f ha
  have hn := image_normalizes D S m a (f.Li 0) (T : Subgroup G) (f.sylow_normalizes_Li 0)
  rw [hlocal] at hn
  have hc := LinearThree.OuterExtensions.AmbientLocalCores.local_join_core_in_aut
    S.field.Carrier S.field.degree_pos S.field.card_eq true
    (image D S m a (T : Subgroup G)) (fun b hb => preserves_of_normalizes_inner D S _ b (hn hb))
  rw [closure_image_core D S m a f,hlocal]
  have hr : (f.Ri 0) = ((f.Li 0) ⊔ (T : Subgroup G)).pCoreIn 2 := by rfl
  rw [hr]
  have hh := core_image_le D S m a ((f.Li 0) ⊔ (T : Subgroup G))
    (sup_le (hKL'.trans le_sup_left) le_sup_right)
  rw [image_sup D S m a (f.Li 0) (T : Subgroup G) (hKL'.trans le_sup_left) le_sup_right,
    hlocal,hc] at hh
  exact hh

/-- Lift the actual projective image comparison through the original quotient kernel. -/
theorem radical_le_closure_join_core (f : InvariantFlag (Coordinates.sl3 m)) :
    (f.Ri 0) ≤ ((f.Li 0).pCoreIn 2) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  obtain ⟨a,ha⟩ := exists_standardPoint_conjugator (f.space 0) (f.dimension 0)
  have hi := radical_image_le_closure D S m a f ha
  have hRT : (f.Ri 0) ≤ (T : Subgroup G) := by
    change (f.Li 0 ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow ((f.Li 0) ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hWR : ((f.Li 0).pCoreIn 2) ≤ (f.Ri 0) := by
    change (f.Li 0).pCoreIn 2 ≤ (f.Li 0 ⊔ (T : Subgroup G)).pCoreIn 2
    exact pCoreIn_mono_of_normalizes le_sup_left
      (sup_le (f.Li 0).le_normalizer (f.sylow_normalizes_Li 0))
  intro r hr
  let r' : (L ⊔ (T : Subgroup G) : Subgroup G) := ⟨r,mem_sup_right (hRT hr)⟩
  obtain ⟨w,hw,he⟩ := hi ⟨r',hr,rfl⟩
  have hk : r' * w⁻¹ ∈ (projectiveAction D S m a).ker := by
    change projectiveAction D S m a (r' * w⁻¹) = 1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  have hd : r * (w : G)⁻¹ ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    sylow_inf_projective_kernel_le_core D S m a
      ⟨(T : Subgroup G).mul_mem (hRT hr) ((T : Subgroup G).inv_mem (hRT (hWR hw))),
        r' * w⁻¹,hk,rfl⟩
  have hh := (((f.Li 0).pCoreIn 2) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2).mul_mem
    (mem_sup_right hd) (mem_sup_left hw)
  change r * (w : G)⁻¹ * (w : G) ∈ _ at hh
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh

/-- The original point radical is the product of the local core and the global core,
including the full outer Sylow action. -/
theorem core_product (f : InvariantFlag (Coordinates.sl3 m)) :
    f.Ri 0 = (f.Li 0).pCoreIn 2 ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  apply le_antisymm (radical_le_closure_join_core D S m f)
  apply sup_le
  · exact pCoreIn_mono_of_normalizes le_sup_left
      (sup_le (f.Li 0).le_normalizer (f.sylow_normalizes_Li 0))
  · have hQT : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
        pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
    intro q hq
    exact inf_pCoreIn_le_of_le 2
      (sup_le (((localResidual_le _).trans inf_le_left).trans le_sup_left) le_sup_right)
      ⟨mem_sup_right (hQT hq),hq⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.SL3Core
