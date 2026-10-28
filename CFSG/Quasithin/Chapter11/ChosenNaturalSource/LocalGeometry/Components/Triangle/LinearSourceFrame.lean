module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.LinearPointNormalizer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Frame.Lattice
public import Theory.Representation.SpecialLinearThreeFrameGeometry.Transitivity
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Source

/-!
# The original point frame and marked G.2.5 input

Complete the given field line to a direct frame and lift the two SL₃ maps
through the original quotient. Transport by the right-conjugation convention
preserves both directness and the full original V. Restricting the star map
to L has kernel O₂(L), so it retains the original full SL₃ marking, including
its center. An escaping U then supplies every hypothesis of G.2.5.

The result records equalities of the chosen group model, vector coordinates,
and point with their original markings. LinearChiefLayers discharges escape
from the already proved extraspecial cubic displacement in the central-core
branch and applies the genuine G.2.5 layer theorems.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed p.763, and G.2.5, printed pp.335--336.
-/

open Subgroup Theory.GroupTheory Representation Matrix
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

open Matrix.SpecialLinearGroup.FrameGeometry in
/-- Three direct conjugates of the original point, with the source right action. -/
theorem linear_point_direct_frame (f : InvariantFlag (.sl3 m)) :
    ∃ g h : G, g ∈ L ∧ h ∈ L ∧
      Disjoint (f.Vi 0) (ChapterG.Section02.Setup.conjugate (f.Vi 0) g) ∧
      Disjoint (f.Vi 0 ⊔ ChapterG.Section02.Setup.conjugate (f.Vi 0) g)
        (ChapterG.Section02.Setup.conjugate (f.Vi 0) h) ∧
      (f.Vi 0 ⊔ ChapterG.Section02.Setup.conjugate (f.Vi 0) g) ⊔
        ChapterG.Section02.Setup.conjugate (f.Vi 0) h = V := by
  let c := Coordinates.sl3 m
  obtain ⟨P,hP,hne,_⟩ := exists_point_complement (f.space 0) (f.space 1)
    (f.dimension 0) (f.dimension 1) (f.nested (by decide : (0 : Fin 3) ≤ 1))
  obtain ⟨b,hb0,hb1⟩ := exists_frame_of_pair (f.space 0) P (f.dimension 0) hP hne
  obtain ⟨a,ha⟩ := exists_point_map (f.space 0) (b.point 1) (f.dimension 0) (b.dimension 1)
  obtain ⟨d,hd⟩ := exists_point_map (f.space 0) (b.point 2) (f.dimension 0) (b.dimension 2)
  obtain ⟨g,hg⟩ := c.quotientMap_surjective a⁻¹
  obtain ⟨h,hh⟩ := c.quotientMap_surjective d⁻¹
  have h1 : ChapterG.Section02.Setup.conjugate (f.Vi 0) (g : G) = c.preimage (b.point 1) := by
    change ChapterG.Section02.Setup.conjugate (c.preimage (f.space 0)) (g : G) = _
    calc
      _ = c.preimage ((f.space 0).map (specialLinearNatural 3 (c.quotientMap g⁻¹))) :=
        (c.preimage_map_action g⁻¹ (f.space 0)).symm
      _ = _ := by rw [map_inv,hg,inv_inv]; exact congrArg c.preimage ha
  have h2 : ChapterG.Section02.Setup.conjugate (f.Vi 0) (h : G) = c.preimage (b.point 2) := by
    change ChapterG.Section02.Setup.conjugate (c.preimage (f.space 0)) (h : G) = _
    calc
      _ = c.preimage ((f.space 0).map (specialLinearNatural 3 (c.quotientMap h⁻¹))) :=
        (c.preimage_map_action h⁻¹ (f.space 0)).symm
      _ = _ := by rw [map_inv,hh,inv_inv]; exact congrArg c.preimage hd
  have h0 : f.Vi 0 = c.preimage (b.point 0) := congrArg c.preimage hb0.symm
  have hbot : c.preimage ⊥ = ⊥ := c.preimage_bot.trans (Preliminary.sl3_centralizer_eq_bot D S m)
  refine ⟨g,h,g.property,h.property,?_,?_,?_⟩
  · rw [h1,h0,disjoint_iff,←c.preimage_inf,b.disjoint.eq_bot,hbot]
  · rw [h1,h2,h0,disjoint_iff,←c.preimage_sup,←c.preimage_inf,b.third_disjoint.eq_bot,hbot]
  · rw [h1,h2,h0,←c.preimage_sup,←c.preimage_sup,b.span,c.preimage_top]

abbrev linearPointSetup (f : InvariantFlag (.sl3 m)) : ChapterG.Section02.Setup G :=
  .mk V (f.Vi 0) L (T : Subgroup G) (normalizer (f.Vi 0 : Set G))

/-- Restriction of the literal star map has exactly the original two-core kernel. -/
theorem linear_point_star_kernel (f : InvariantFlag (.sl3 m)) :
    (ChapterG.Section02.LinearThree.starProjection (linearPointSetup D S m f)).ker = pCore 2 L := by
  let B := linearPointSetup D S m f
  have hmono : L.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left
      (sup_le L.le_normalizer D.sylow_normalizes_component)
  ext l
  have hmem : l ∈ (ChapterG.Section02.LinearThree.starProjection B).ker ↔
      (l : G) ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    change ChapterG.Section02.LinearThree.starProjection B l = 1 ↔ _
    rw [Subtype.ext_iff]
    change QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
      (inclusion le_sup_left l) = 1 ↔ _
    constructor
    · intro h
      exact ⟨_,(QuotientGroup.eq_one_iff _).mp h,rfl⟩
    · rintro ⟨a,ha,he⟩
      apply (QuotientGroup.eq_one_iff _).mpr
      have hh : a = inclusion (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) l := Subtype.ext he
      rwa [hh] at ha
  rw [hmem]
  constructor
  · intro h
    obtain ⟨a,ha,he⟩ := inf_pCoreIn_le_of_le 2
      (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) ⟨l.property,h⟩
    have hh : a = l := Subtype.ext he
    rwa [hh] at ha
  · intro h
    exact hmono ⟨l,h,rfl⟩

/-- The original starred SL₃ model, not a projectivization of its center. -/
def linearPointStarModel (f : InvariantFlag (.sl3 m)) :
    (linearPointSetup D S m f).star L ≃* SL(3,S.field.Carrier) :=
  (QuotientGroup.quotientKerEquivOfSurjective _
    (ChapterG.Section02.LinearThree.starProjection_surjective (linearPointSetup D S m f))).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (linear_point_star_kernel D S m f)).trans m.groupEquiv)

theorem linearPointStarModel_projection (f : InvariantFlag (.sl3 m)) (l : L) :
    linearPointStarModel D S m f (ChapterG.Section02.LinearThree.starProjection (linearPointSetup D S m f) l) =
      (Coordinates.sl3 m).quotientMap l := by
  let p := ChapterG.Section02.LinearThree.starProjection (linearPointSetup D S m f)
  let e := QuotientGroup.quotientKerEquivOfSurjective p
    (ChapterG.Section02.LinearThree.starProjection_surjective (linearPointSetup D S m f))
  have he : e (QuotientGroup.mk' p.ker l) = p l := rfl
  change m.groupEquiv (QuotientGroup.quotientMulEquivOfEq _ (e.symm (p l))) = _
  rw [←he,e.symm_apply_apply]
  rfl

/-- The direct point frame and escaping original U give all inputs of G.2.5. -/
theorem linear_point_source_frame (f : InvariantFlag (.sl3 m))
    (hescape : ¬ (linearPointSetup D S m f).U ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hUT : (linearPointSetup D S m f).U ≤ (T : Subgroup G)) :
    ∃ g h : G, ∃ d : ChapterG.Section02.LinearThree.Hypothesis
      (linearPointSetup D S m f) S.field.Carrier S.field.degree g h,
      d.model = linearPointStarModel D S m f ∧
      d.coordinates = SL3.naturalEquiv D S m ∧ d.point = f.space 0 := by
  let B := linearPointSetup D S m f
  obtain ⟨g,h,hg,hh,hdis,hthird,hspan⟩ := linear_point_direct_frame D S m f
  have hsp : B.VL = V := by
    apply le_antisymm (conjugateSpanBy_le (D.centralQuotientPreimage_le _) D.normalizes)
    apply hspan.symm.le.trans
    apply sup_le (sup_le (le_conjugateSpanBy _ _) ?_) ?_
    · rintro _ ⟨v,hv,rfl⟩
      exact le_normalizer_iff.mp (le_normalizer_conjugateSpanBy (f.Vi 0) L)
        g⁻¹ (L.inv_mem hg) v (le_conjugateSpanBy _ _ hv)
    · rintro _ ⟨v,hv,rfl⟩
      exact le_normalizer_iff.mp (le_normalizer_conjugateSpanBy (f.Vi 0) L)
        h⁻¹ (L.inv_mem hh) v (le_conjugateSpanBy _ _ hv)
  have hstar : B.star B.U ≠ ⊥ := by
    intro hz
    apply hescape
    intro u hu
    let u' : B.LT := ⟨u,mem_sup_right (hUT hu)⟩
    have hm : QuotientGroup.mk' (pCore 2 B.LT) u' ∈ B.star B.U := mem_map_of_mem _ hu
    have hm1 := mem_bot.mp (hz ▸ hm)
    exact ⟨u',(QuotientGroup.eq_one_iff _).mp hm1,rfl⟩
  refine ⟨g,h,{
    setup := linear_point_source_hypothesis D S m f
    exponent_pos := S.field.degree_pos
    field_card := S.field.card_eq
    span_eq := hsp
    model := linearPointStarModel D S m f
    coordinates := SL3.naturalEquiv D S m
    equivariant := ?_
    point := f.space 0
    point_dimension := f.dimension 0
    point_mem := (Coordinates.sl3 m).mem_preimage (f.space 0)
    star_U_ne_bot := hstar
    g_mem := hg
    h_mem := hh
    points_disjoint := hdis
    third_disjoint := hthird
    points_span := hspan },rfl,rfl,rfl⟩
  intro l v
  rw [linearPointStarModel_projection]
  exact SL3.naturalEquiv_conjugation D S m l v

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
