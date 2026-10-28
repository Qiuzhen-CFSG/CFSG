module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.G2.Model
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.G2.Action
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.ResidualIncidence.Marked
public import Theory.GroupTheory.PCoreRestriction

/-!
# The original G₂ point-radical product

The constructed flag and its original quotient map identify L₁ with the
aligned long local. The faithful inner action preserves its two-core, and
the model automorphism calculation controls the entire Sylow supplement.
Lifting through the original action kernel proves
R₁ = O₂(L₁) O₂(LT), with the literal subgroups in G throughout.

The line-action consumer in LineAction.G2 applies this product to centralize
the full line preimage and construct its section-kernel Sylow.
Source: Aschbacher--Smith 11.1.5 and 11.2.3, printed pp.765--766,768--769.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.G2Line
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (m : ActionEquiv D.centralQuotientAction
    (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
  (a : Atlas.G2.Model S.field.Carrier)
/-- The component marking applied to an actual ambient subgroup. -/
private def modelImage (A : Subgroup G) : Subgroup (Atlas.G2.Model S.field.Carrier) :=
  (A.subgroupOf L).map (Coordinates.g2 m).quotientMap

/-- Two-core images retain the literal original projection. -/
private theorem modelImage_core (A : Subgroup G) (hA : A ≤ L) :
    modelImage D S m (A.pCoreIn 2) = (modelImage D S m A).pCoreIn 2 := by
  have hk : IsPGroup 2 (Coordinates.g2 m).quotientMap.ker := by
    have he : (Coordinates.g2 m).quotientMap.ker = pCore 2 L := by
      ext l
      change m.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) = 1 ↔ l ∈ pCore 2 L
      rw [←m.groupEquiv.map_one,m.groupEquiv.injective.eq_iff]
      exact QuotientGroup.eq_one_iff l
    rw [he]
    exact pCore_isPGroup
  change ((A.pCoreIn 2).subgroupOf L).map _ = _
  rw [←pCoreIn_subgroupOf 2 A L hA]
  exact map_pCoreIn_of_ker_isPGroup _ hk _

/-- Actual subgroup images in the automorphism group of the marked quotient. -/
private def image (A : Subgroup G) : Subgroup (MulAut (Atlas.G2.Model S.field.Carrier)) :=
  (A.subgroupOf (L ⊔ (T : Subgroup G))).map (quotientAction D S m a)

private theorem image_normalizes (A B : Subgroup G) (hn : B ≤ normalizer (A : Set G)) :
    image D S m a B ≤ normalizer (image D S m a A : Set _) :=
  (map_mono ((comap_mono hn).trans (A.le_normalizer_comap _))).trans (le_normalizer_map _)

private theorem core_image_le (A : Subgroup G) (hA : A ≤ L ⊔ (T : Subgroup G)) :
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
private theorem image_component (A : Subgroup G) (hA : A ≤ L) :
    image D S m a A = ((modelImage D S m A).map (MulAut.conj a).toMonoidHom).map
      MulAut.conj := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨MulAut.conj a ((Coordinates.g2 m).quotientMap ⟨x,hA hx⟩),
      ⟨(Coordinates.g2 m).quotientMap ⟨x,hA hx⟩,⟨⟨x,hA hx⟩,hx,rfl⟩,rfl⟩,?_⟩
    exact (quotientAction_component D S m a ⟨x,hA hx⟩).symm
  · rintro ⟨y,⟨s,⟨l,hl,rfl⟩,rfl⟩,rfl⟩
    refine ⟨inclusion le_sup_left l,hl,?_⟩
    exact quotientAction_component D S m a l

/-- Two-cores inside L have exact images, since inner G₂ is faithful. -/
private theorem component_image_core (A : Subgroup G) (hA : A ≤ L) :
    image D S m a (A.pCoreIn 2) = (image D S m a A).pCoreIn 2 := by
  rw [image_component D S m a _ ((pCoreIn_le _ _).trans hA),image_component D S m a A hA,
    modelImage_core D S m A hA,
    map_pCoreIn_of_injective 2 _ _ (MulAut.conj a).injective,
    map_pCoreIn_of_injective 2 _ _ (inner_injective (G2.field_card_gt_two S))]


/-- The aligned original point residual maps onto the actual long local. -/
private theorem modelImage_point (f : InvariantFlag (Coordinates.g2 m)) :
    modelImage D S m (f.Li 0) =
      (Atlas.G2.LieParabolicSetup.local₂ (F := S.field.Carrier)).map
        (MulAut.conj (G2.ResidualIncidence.alignment S m).val).toMonoidHom := by
  have hf : f = G2.flag S m := by
    let g := G2.flag S m
    have hs : f.space = g.space :=
      funext fun i => G2.flag_unique S m i (f.space i) (f.dimension i) (f.invariant i)
    cases f; cases g; cases hs; rfl
  subst f
  let a := (G2.ResidualIncidence.alignment S m).val
  have hproj (l : (G2.flag S m).Li 0) :
      (G2.ResidualIncidence.localProjection S m 0 l).val =
        a⁻¹ * m.groupEquiv (QuotientGroup.mk' (pCore 2 L)
          ⟨l,(localResidual_le _ l.property).1⟩) * a :=
    G2.ResidualIncidence.localProjection_coe S m 0 l
  ext x
  constructor
  · rintro ⟨l,hl,rfl⟩
    let y : (G2.flag S m).Li 0 := ⟨l,hl⟩
    refine ⟨G2.ResidualIncidence.localProjection S m 0 y,
      (G2.ResidualIncidence.localProjection S m 0 y).property,?_⟩
    change a * (G2.ResidualIncidence.localProjection S m 0 y).val * a⁻¹ =
      m.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)
    rw [hproj]
    change a * (a⁻¹ * m.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) * a) * a⁻¹ = _
    group
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨l,hl⟩ := G2.ResidualIncidence.localProjection_surjective S m 0 ⟨y,hy⟩
    refine ⟨⟨l,(localResidual_le _ l.property).1⟩,l.property,?_⟩
    have he := (hproj l).symm.trans (congrArg (fun z => z.val) hl)
    change m.groupEquiv (QuotientGroup.mk' (pCore 2 L)
      ⟨l,(localResidual_le _ l.property).1⟩) = a * y * a⁻¹
    let q : Atlas.G2.Model S.field.Carrier := m.groupEquiv
      (QuotientGroup.mk' (pCore 2 L) ⟨l,(localResidual_le _ l.property).1⟩)
    change q = a * y * a⁻¹
    have he' : a⁻¹ * q * a = y := he
    calc
      q = a * (a⁻¹ * q * a) * a⁻¹ := by group
      _ = a * y * a⁻¹ := congrArg (fun z => a * z * a⁻¹) he'

/-- The same alignment transports the residual to its inner automorphisms. -/
private theorem image_residual (f : InvariantFlag (Coordinates.g2 m)) :
    image D S m (G2.ResidualIncidence.alignment S m).val⁻¹ (f.Li 0) =
      (Atlas.G2.LieParabolicSetup.local₂ (F := S.field.Carrier)).map MulAut.conj := by
  have hL : f.Li 0 ≤ L := (localResidual_le _).trans inf_le_left
  rw [image_component D S m (G2.ResidualIncidence.alignment S m).val⁻¹ (f.Li 0) hL,
    modelImage_point]
  have he : (MulAut.conj (G2.ResidualIncidence.alignment S m).val⁻¹).toMonoidHom.comp
      (MulAut.conj (G2.ResidualIncidence.alignment S m).val).toMonoidHom =
        MonoidHom.id (Atlas.G2.Model S.field.Carrier) := by
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  rw [Subgroup.map_map _ (MulAut.conj (G2.ResidualIncidence.alignment S m).val⁻¹).toMonoidHom,
    he,Subgroup.map_id]

private theorem image_sup (A B : Subgroup G)
    (hA : A ≤ L ⊔ (T : Subgroup G)) (hB : B ≤ L ⊔ (T : Subgroup G)) :
    image D S m a (A ⊔ B) = image D S m a A ⊔ image D S m a B := by
  unfold image
  rw [subgroupOf_sup hA hB,Subgroup.map_sup]

/-- The full Sylow supplement has no additional local two-core image. -/
private theorem radical_image_le_local_core (f : InvariantFlag (Coordinates.g2 m)) :
    image D S m (G2.ResidualIncidence.alignment S m).val⁻¹ (f.Ri 0) ≤
      image D S m (G2.ResidualIncidence.alignment S m).val⁻¹ ((f.Li 0).pCoreIn 2) := by
  let a := (G2.ResidualIncidence.alignment S m).val⁻¹
  have hL : f.Li 0 ≤ L := (localResidual_le _).trans inf_le_left
  have hlocal := image_residual D S m f
  have hn := image_normalizes D S m a (f.Li 0) (T : Subgroup G) (f.sylow_normalizes_Li 0)
  change image D S m a (f.Li 0) = _ at hlocal
  rw [hlocal] at hn
  have hc := local_join_core_in_aut (G2.field_card_gt_two S)
    (image D S m a (T : Subgroup G))
    (fun b hb => preserves_of_normalizes_inner (G2.field_card_gt_two S) _ b (hn hb))
  rw [component_image_core D S m a (f.Li 0) hL,hlocal]
  change image D S m a ((f.Li 0 ⊔ (T : Subgroup G)).pCoreIn 2) ≤ _
  have hh := core_image_le D S m a (f.Li 0 ⊔ (T : Subgroup G))
    (sup_le (hL.trans le_sup_left) le_sup_right)
  rw [image_sup D S m a _ _ (hL.trans le_sup_left) le_sup_right,hlocal,hc] at hh
  exact hh
/-- The exact original radical product, with no splitting of its central kernel. -/
theorem core_product (f : InvariantFlag (Coordinates.g2 m)) :
    f.Ri 0 = (f.Li 0).pCoreIn 2 ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let a := (G2.ResidualIncidence.alignment S m).val⁻¹
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

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.G2Line
