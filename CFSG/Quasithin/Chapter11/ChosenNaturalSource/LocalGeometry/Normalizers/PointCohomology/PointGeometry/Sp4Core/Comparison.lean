module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.Sp4Core.Action
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.Sp4Core.AutomorphismCore

/-!
# The original symplectic point-radical product

The actual point residual maps onto the aligned symplectic point local.
Faithfulness of inner Sp₄ and the two-group projection kernel preserve its
core. The local-preserving automorphism calculation controls the full outer
Sylow supplement. Lifting through the original action kernel gives
R₁=O₂(L₁)O₂(LT), with the original nonsplit central kernel retained.

Source: Aschbacher–Smith 11.1.5, printed pp.765–766.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Matrix
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.Sp4Core
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (m : ActionEquiv D.centralQuotientAction
    (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
  (a : Sp S.field.Carrier)

/-- Actual subgroup images in the automorphism group of the marked quotient. -/
def image (A : Subgroup G) : Subgroup (MulAut (Sp S.field.Carrier)) :=
  (A.subgroupOf (L ⊔ (T : Subgroup G))).map (quotientAction D S m a)

theorem image_normalizes (A B : Subgroup G) (hn : B ≤ normalizer (A : Set G)) :
    image D S m a B ≤ normalizer (image D S m a A : Set _) :=
  (map_mono ((comap_mono hn).trans (A.le_normalizer_comap _))).trans (le_normalizer_map _)

theorem core_image_le (A : Subgroup G) (hA : A ≤ L ⊔ (T : Subgroup G)) :
    image D S m a (A.pCoreIn 2) ≤ (image D S m a A).pCoreIn 2 := by
  let B := A.subgroupOf (L ⊔ (T : Subgroup G))
  let f := (quotientAction D S m a).subgroupMap B
  have hn : ((pCore 2 B).map f).Normal :=
    Normal.map inferInstance f ((quotientAction D S m a).subgroupMap_surjective B)
  have h : (pCore 2 B).map f ≤ pCore 2 (image D S m a A) :=
    le_sSup ⟨hn,pCore_isPGroup.map f⟩
  have hh := map_mono (f := (image D S m a A).subtype) h
  change ((pCore 2 B).map f).map (B.map (quotientAction D S m a)).subtype ≤
    (B.map (quotientAction D S m a)).pCoreIn 2 at hh
  rw [Subgroup.map_map] at hh
  change (pCore 2 B).map ((quotientAction D S m a).comp B.subtype) ≤ _ at hh
  rw [← Subgroup.map_map] at hh
  change ((A.pCoreIn 2).subgroupOf (L ⊔ (T : Subgroup G))).map _ ≤ _
  rwa [← pCoreIn_subgroupOf 2 A (L ⊔ (T : Subgroup G)) hA]

/-- On the component, the automorphism image is the literal marked inner image. -/
theorem image_component (A : Subgroup G) (hA : A ≤ L) :
    image D S m a A = ((modelImage D S m A).map (MulAut.conj a).toMonoidHom).map
      MulAut.conj := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨MulAut.conj a ((Coordinates.sp4 m).quotientMap ⟨x,hA hx⟩),
      ⟨(Coordinates.sp4 m).quotientMap ⟨x,hA hx⟩,⟨⟨x,hA hx⟩,hx,rfl⟩,rfl⟩,?_⟩
    exact (quotientAction_component D S m a ⟨x,hA hx⟩).symm
  · rintro ⟨y,⟨s,⟨l,hl,rfl⟩,rfl⟩,rfl⟩
    refine ⟨inclusion le_sup_left l,hl,?_⟩
    exact quotientAction_component D S m a l

/-- Two-cores inside L have exact images, since inner Sp₄ is faithful. -/
theorem component_image_core (A : Subgroup G) (hA : A ≤ L) :
    image D S m a (A.pCoreIn 2) = (image D S m a A).pCoreIn 2 := by
  rw [image_component D S m a _ ((pCoreIn_le _ _).trans hA),image_component D S m a A hA,
    modelImage_core D S m A hA,
    map_pCoreIn_of_injective 2 _ _ (MulAut.conj a).injective,
    map_pCoreIn_of_injective 2 _ _ inner_injective]

/-- Rotate the original invariant point to the standard point local. -/
theorem image_residual (f : InvariantFlag (Coordinates.sp4 m)) :
    image D S m (Sp4.alignment m)⁻¹ (f.Li 0) =
      (pointLocal (F := S.field.Carrier)).map MulAut.conj := by
  have hL : f.Li 0 ≤ L := (localResidual_le _).trans inf_le_left
  rw [image_component D S m (Sp4.alignment m)⁻¹ (f.Li 0) hL,modelImage_point]
  have he : (MulAut.conj (Sp4.alignment m)⁻¹).toMonoidHom.comp
      (MulAut.conj (Sp4.alignment m)).toMonoidHom = MonoidHom.id (Sp S.field.Carrier) := by
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  rw [Subgroup.map_map _ (MulAut.conj (Sp4.alignment m)⁻¹).toMonoidHom,he,Subgroup.map_id]

private theorem image_sup (A B : Subgroup G)
    (hA : A ≤ L ⊔ (T : Subgroup G)) (hB : B ≤ L ⊔ (T : Subgroup G)) :
    image D S m a (A ⊔ B) = image D S m a A ⊔ image D S m a B := by
  unfold image
  rw [subgroupOf_sup hA hB,Subgroup.map_sup]

/-- The full outer Sylow supplement introduces no new point-local core image. -/
theorem radical_image_le_local_core (f : InvariantFlag (Coordinates.sp4 m)) :
    image D S m (Sp4.alignment m)⁻¹ (f.Ri 0) ≤
      image D S m (Sp4.alignment m)⁻¹ ((f.Li 0).pCoreIn 2) := by
  let a := (Sp4.alignment m)⁻¹
  have hL : f.Li 0 ≤ L := (localResidual_le _).trans inf_le_left
  have hlocal := image_residual D S m f
  have hn := image_normalizes D S m a (f.Li 0) (T : Subgroup G) (f.sylow_normalizes_Li 0)
  change image D S m a (f.Li 0) = _ at hlocal
  rw [hlocal] at hn
  have hc := local_join_core_in_aut S.field.card_eq S.nonbinary
    (image D S m a (T : Subgroup G))
    (fun b hb => preserves_of_normalizes_inner _ b (hn hb))
  rw [component_image_core D S m a (f.Li 0) hL,hlocal]
  change image D S m a ((f.Li 0 ⊔ (T : Subgroup G)).pCoreIn 2) ≤ _
  have hh := core_image_le D S m a (f.Li 0 ⊔ (T : Subgroup G))
    (sup_le (hL.trans le_sup_left) le_sup_right)
  rw [image_sup D S m a _ _ (hL.trans le_sup_left) le_sup_right,hlocal,hc] at hh
  exact hh

/-- The exact original radical product, with no splitting of its central kernel. -/
theorem core_product (f : InvariantFlag (Coordinates.sp4 m)) :
    f.Ri 0 = (f.Li 0).pCoreIn 2 ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let a := (Sp4.alignment m)⁻¹
  have hRT : f.Ri 0 ≤ (T : Subgroup G) := by
    change (f.Li 0 ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (f.Li 0 ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hWR : (f.Li 0).pCoreIn 2 ≤ f.Ri 0 :=
    pCoreIn_mono_of_normalizes le_sup_left
      (sup_le (f.Li 0).le_normalizer (f.sylow_normalizes_Li 0))
  apply le_antisymm
  · intro r hr
    let r' : (L ⊔ (T : Subgroup G) : Subgroup G) := ⟨r,mem_sup_right (hRT hr)⟩
    obtain ⟨w,hw,he⟩ := radical_image_le_local_core D S m f ⟨r',hr,rfl⟩
    have hk : r' * w⁻¹ ∈ (quotientAction D S m a).ker := by
      change quotientAction D S m a (r' * w⁻¹) = 1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    have hd : r * (w : G)⁻¹ ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
      sylow_inf_quotient_kernel_le_core D S m a
        ⟨(T : Subgroup G).mul_mem (hRT hr) ((T : Subgroup G).inv_mem (hRT (hWR hw))),
          r' * w⁻¹,hk,rfl⟩
    have hh := ((f.Li 0).pCoreIn 2 ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2).mul_mem
      (mem_sup_right hd) (mem_sup_left hw)
    change r * (w : G)⁻¹ * (w : G) ∈ _ at hh
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh
  · apply sup_le hWR
    have hQT : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
        pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
    intro q hq
    exact inf_pCoreIn_le_of_le 2
      (sup_le (((localResidual_le _).trans inf_le_left).trans le_sup_left) le_sup_right)
      ⟨mem_sup_right (hQT hq),hq⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.Sp4Core
