module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.Localization.Source
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic

/-!
# The original G₂ point radical in a common model frame

One conjugator aligns the first and third flag spaces and the image of the
original inner Sylow subgroup. The perfect long local group fixes the first
line, so it lifts through the original point residual. Its normalization of
R₁ places the inner image of R₁ in the concrete five-root two-core. This
discharges the geometric premise of the fixed-family localization and hence
11.2.2(6), preserving the full central preimage of the third space.

The combined weak-closure and rank-one applications retain only the separate
reciprocal root-plane input and preceding source conclusions. The remaining
root-plane reconstruction belongs to qt-d-1222-natural-weak-closure-source.
Source: Aschbacher--Smith B.4.6(3,12), pp.88--90, and 11.2.2(6), p.768.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.Localization
open Atlas.G2 Atlas.G2.Natural.OrthogonalCover.SylowFlag
open LieParabolicSetup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
private theorem local_fixes_line {b : Model F} (hb : b ∈ local₂)
    {v : Natural.Space F} (hv : v ∈ N1 F) : Natural.action F b v = v := by
  rw [N1_eq_span] at hv
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [map_smul]
  congr 1
  change Natural.mk F (Natural.traceZeroAction F b (pointVector F)) = Natural.mk F (pointVector F)
  congr 1
  apply Subtype.ext
  have hpoint : (pointVector F).val = Atlas.SplitOctonion.basisVector 0 := by
    ext i
    fin_cases i <;> simp [pointVector,Natural.OrthogonalCover.planeLift,Atlas.SplitOctonion.basisVector]
  change b.val (pointVector F).val = (pointVector F).val
  rw [hpoint]
  rw [local₂_eq_fixingFirstVector] at hb
  exact hb

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (f : InvariantFlag (Coordinates.g2 m))

/-- One actual model conjugator aligns the first and third spaces and the
image of the original T intersect L. -/
theorem exists_common_frame :
    ∃ g : Model S.field.Carrier,
      f.space 0 = (N1 S.field.Carrier).map (Natural.action S.field.Carrier g) ∧
      f.space 2 = (naturalThreeSpace S.field.Carrier).map (Natural.action S.field.Carrier g) ∧
      ((T : Subgroup G).subgroupOf L).map (Coordinates.g2 m).quotientMap =
        (unipotent (K := S.field.Carrier)).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨d,hd⟩ := exists_marking S.field.Carrier (G2.modelSylow S m)
  have hfirst : f.space 0 = movedLine S.field.Carrier d := by
    apply (G2.flag_unique S m 0 (f.space 0) (f.dimension 0) (f.invariant 0)).trans
    apply movedLine_unique S.field.Carrier d _
    · intro q
      exact (G2.modelFlag S m).invariant 0 ⟨q,hd.symm ▸ q.property⟩
    · exact (G2.modelFlag S m).dimension 0
  have hthird : f.space 2 = movedThreeSpace S.field.Carrier d := by
    apply (G2.flag_unique S m 2 (f.space 2) (f.dimension 2) (f.invariant 2)).trans
    apply movedThreeSpace_unique S.field.Carrier d _
    · intro q
      exact (G2.modelFlag S m).invariant 2 ⟨q,hd.symm ▸ q.property⟩
    · exact (G2.modelFlag S m).dimension 2
  refine ⟨d.val,hfirst,hthird,?_⟩
  let c := Coordinates.g2 m
  have hmap : (G2.modelSylow S m : Subgroup _).map (Natural.OrthogonalCover.SylowFlag.D S.field.Carrier).subtype =
      ((T : Subgroup G).subgroupOf L).map c.quotientMap := by
    change ((G2.innerSylow (D := D) : Subgroup L).map (G2.derivedMap S m)).map _ = _
    rw [map_map, G2.innerSylow_coe]
    rfl
  rw [hd] at hmap
  rw [← hmap]
  change ((U S.field.Carrier).map (MulAut.conj d).toMonoidHom).map
    (Natural.OrthogonalCover.SylowFlag.D S.field.Carrier).subtype = _
  have he : ((MulAut.conj d.val).toMonoidHom.comp (Natural.OrthogonalCover.SylowFlag.D S.field.Carrier).subtype) =
      (Natural.OrthogonalCover.SylowFlag.D S.field.Carrier).subtype.comp (MulAut.conj d).toMonoidHom := rfl
  rw [map_map, ← he, ← map_map]
  congr 1
  apply map_subgroupOf_eq_of_le
  let := Atlas.G2.isPerfect (G2.field_card_gt_two S)
  exact fun _ _ => Group.IsPerfect.mem_commutator

/-- The point residual supplies the perfect long local group in the same
model frame; no identification of the whole ambient normalizer is needed. -/
theorem point_residual_image_contains
    (g : Model S.field.Carrier)
    (hfirst : f.space 0 = (N1 S.field.Carrier).map (Natural.action S.field.Carrier g)) :
    local₂ ≤ ((f.Li 0).subgroupOf L).map
      ((MulAut.conj g⁻¹).toMonoidHom.comp (Coordinates.g2 m).quotientMap) := by
  let c := Coordinates.g2 m
  let J := (local₂ (F := S.field.Carrier)).map (MulAut.conj g).toMonoidHom
  have hJ : J ≤ c.modelStabilizer (f.space 0) := by
    apply le_subspaceStabilizer
    rintro a ⟨b,hb,rfl⟩ v hv
    change v ∈ f.space 0 at hv
    rw [hfirst] at hv
    obtain ⟨w,hw,rfl⟩ := hv
    have he : c.modelAction ((MulAut.conj g) b)
        (Natural.action S.field.Carrier g w) = Natural.action S.field.Carrier g w := by
      change Natural.action S.field.Carrier ((MulAut.conj g) b)
        (Natural.action S.field.Carrier g w) = _
      rw [Transport.conjugate_action, local_fixes_line hb hw]
    change c.modelAction ((MulAut.conj g) b) _ ∈ f.space 0
    rw [he,hfirst]
    exact ⟨w,hw,rfl⟩
  let := local₂_isPerfect (G2.field_card_gt_two S)
  let : Group.IsPerfect J := Group.IsPerfect.ofSurjective
    (f := (MulAut.conj g).toMonoidHom.subgroupMap local₂)
    ((MulAut.conj g).toMonoidHom.subgroupMap_surjective _)
  have hres := le_map_solvableResidual_of_isPerfect J (c.modelStabilizer (f.space 0)) hJ
  intro b hb
  obtain ⟨y,hy,hyb⟩ := hres (mem_map_of_mem (MulAut.conj g).toMonoidHom hb)
  obtain ⟨l,hl⟩ := c.residualProjection_surjective (f.space 0) ⟨y,hy⟩
  let l' : L := ⟨l,(localResidual_le _ l.property).1⟩
  refine ⟨l',l.property,?_⟩
  have hh := congrArg (fun z : solvableResidual (c.modelStabilizer (f.space 0)) =>
    (z.val : c.ModelGroup)) hl
  rw [c.residualProjection_coe] at hh
  change c.quotientMap l' = y.val at hh
  change (MulAut.conj g⁻¹) (c.quotientMap l') = b
  have he : c.quotientMap l' = (MulAut.conj g) b := hh.trans hyb
  rw [he]
  simp [MulAut.conj_apply,mul_assoc]

/-- Normality of the actual R₁ under its point residual places its inner
quotient image in the actual five-root radical. -/
theorem radical_image_of_common_frame
    (g : Model S.field.Carrier)
    (hfirst : f.space 0 = (N1 S.field.Carrier).map (Natural.action S.field.Carrier g))
    (hsylow : ((T : Subgroup G).subgroupOf L).map (Coordinates.g2 m).quotientMap =
      (unipotent (K := S.field.Carrier)).map (MulAut.conj g).toMonoidHom) :
    ((f.Ri 0).subgroupOf L).map (Coordinates.g2 m).quotientMap ≤
      (radical₂ (F := S.field.Carrier)).map (MulAut.conj g).toMonoidHom := by
  let c := Coordinates.g2 m
  let q := (MulAut.conj g⁻¹).toMonoidHom.comp c.quotientMap
  let K := ((f.Ri 0).subgroupOf L).map q
  have hKU : K ≤ unipotent := by
    rintro _ ⟨l,hl,rfl⟩
    have ht : c.quotientMap l ∈ ((T : Subgroup G).subgroupOf L).map c.quotientMap :=
      mem_map_of_mem _ ((localRadical_le_sylow _) hl)
    rw [hsylow] at ht
    obtain ⟨u,hu,he⟩ := ht
    change (MulAut.conj g⁻¹) (c.quotientMap l) ∈ _
    rw [← he]
    simpa [MulAut.conj_apply,mul_assoc] using hu
  have hLnorm : f.Li 0 ≤ normalizer (f.Ri 0 : Set G) :=
    le_sup_left.trans ((f.Li 0 ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hN : local₂ (F := S.field.Carrier) ≤ normalizer (K : Set _) := by
    intro b hb
    obtain ⟨l,hl,rfl⟩ := point_residual_image_contains D S m f g hfirst hb
    change q l ∈ normalizer (K : Set _)
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · rintro ⟨u,hu,rfl⟩
      refine ⟨l * u * l⁻¹, (hLnorm hl u.val).mp hu, ?_⟩
      simp [map_mul,map_inv]
    · intro hx
      have hlinv : (l⁻¹ : L).val ∈ f.Li 0 := (f.Li 0).inv_mem hl
      obtain ⟨u,hu,he⟩ := hx
      refine ⟨l⁻¹ * u * l, ?_, ?_⟩
      · change l.val⁻¹ * u.val * l.val ∈ f.Ri 0
        simpa using (hLnorm hlinv u.val).mp hu
      · simp only [map_mul,map_inv,he]
        group
  have hK2 : IsPGroup 2 K :=
    ((isPGroup_pCoreIn 2 (f.Li 0 ⊔ (T : Subgroup G))).comap_subtype (K := L)).map q
  have hKR : K ≤ radical₂ := by
    rw [← local₂_pCoreIn]
    exact le_pCoreIn_of_normalizes hK2 (hKU.trans unipotent_le_local₂) hN
  rintro _ ⟨l,hl,rfl⟩
  refine ⟨q l,hKR (mem_map_of_mem _ hl),?_⟩
  simp [q,c,MulAut.conj_apply,mul_assoc]
  rfl

/-- The original point-radical image and the full third preimage share one
actual conjugator. This discharges the geometric premise of localization. -/
theorem exists_pointRadicalImage :
    ∃ g : Model S.field.Carrier, PointRadicalImage D S m f g := by
  obtain ⟨g,hfirst,hthird,hsylow⟩ := exists_common_frame D S m f
  exact ⟨g,hthird,radical_image_of_common_frame D S m f g hfirst hsylow⟩

/-- Complete R₁ fixed-family localization, preserving the original central
kernel, quotient marking and source radical. -/
theorem r1FamilyLocalization : R1FamilyLocalization D S f := by
  obtain ⟨g,hg⟩ := exists_pointRadicalImage D S m f
  exact r1FamilyLocalization_of_pointRadicalImage D S m f g hg

/-- Source 11.2.2(6), retaining only the earlier value s=2n and the
11.1.4 three-space centralizer bound. All R₁ geometry is discharged. -/
theorem source_clause_six
    (hs : @globalS G _ V D.elementary = (2 * S.field.degree : ℕ))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G)) :
    centralizer (weakCentralizer V (f.Ri 0) 1 : Set G) ≤ normalizer (L : Set G) :=
  weakCentralizer_centralizer_le_of_family D S f hs
    (r1FamilyLocalization D S m f) hthree

/-- The literal combined source consumer no longer assumes R₁ localization.
The independent reciprocal root-plane reconstruction remains with this owner. -/
theorem source_clauses_of_root_planes
    (hr : (2 * S.field.degree : ℕ∞) < @globalR G _ V)
    (hs : @globalS G _ V D.elementary = (2 * S.field.degree : ℕ))
    (hcomponent : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (localResidual L (f.Vi 1)))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hroots : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) →
      Nonempty (RootPlaneData D S m f g)) :
    indexedWeakClosure V (T : Subgroup G) 0 ≤
        (T : Subgroup G) ⊓ centralizer (V : Set G) ∧
      normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤ normalizer (L : Set G) ∧
      0 < globalW V (T : Subgroup G) ∧
      centralizer (weakCentralizer V (f.Ri 0) 1 : Set G) ≤ normalizer (L : Set G) ∧
      indexedWeakClosure V (f.Ri 0) 0 = indexedWeakClosure V (T : Subgroup G) 0 ∧
      normalizer (indexedWeakClosure V (f.Ri 0) 0 : Set G) ≤ normalizer (L : Set G) :=
  clauses_of_source_component D S m f hr hs hcomponent hthree
    (r1FamilyLocalization D S m f) hroots

/-- Both normalizer and relative-centralizer conclusions apply to the original
rank-one R₁ consumer. Only the independent clause-(5) root-plane argument remains. -/
theorem rankOne_impossible_of_root_plane_source
    (hr : (2 * S.field.degree : ℕ∞) < @globalR G _ V)
    (hs : @globalS G _ V D.elementary = (2 * S.field.degree : ℕ))
    (hcomponent : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (localResidual L (f.Vi 1)))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hroots : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) →
      Nonempty (RootPlaneData D S m f g))
    (H₁ : Subgroup G) (P : Sylow 2 H₁)
    (hP : (P : Subgroup H₁).map H₁.subtype = f.Ri 0)
    (hn : generationParameter H₁ = 1) (hout : ¬ H₁ ≤ normalizer (L : Set G)) : False :=
  rankOne_impossible_of_source_component D S m f hr hs hcomponent hthree
    (r1FamilyLocalization D S m f) hroots H₁ P hP hn hout

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.Localization
