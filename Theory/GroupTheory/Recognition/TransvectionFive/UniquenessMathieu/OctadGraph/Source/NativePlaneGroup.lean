module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.HexacodeCoordinates
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.PlaneSplitting
public import Theory.Mathieu.M24.ChapterHStabilizers.SextetAction

/-!
# The actual source plane group in native sextet coordinates

The full rectangle quotient is identified with the monomial hexacode group
through its faithful action on the six-bit rectangle. The already proved
splitting then reconstructs the affine hexacode extension, whose native
realization is the standard sextet stabilizer in M24. The kernel coordinates
are prescribed on every element. Their faithful conjugation action forces
the quotient coordinate to be exactly the original quotient map.

Transport through the marking interchange gives the map for the original
oriented A₂. The 21/45 orientation is retained. This constructs the actual
plane-group isomorphism used in source 41.4; alignment of its common flags
and agreement with the vertex map remain further obligations.

Source: Aschbacher, *Sporadic Groups* (1994), 41.4, p.222, with the
hexacode realization of the sextet group in 19.9, pp.96–97. The native
affine model uses the ATLAS ports by Gerald Höhn and ATLAS contributors,
revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`, under the ATLAS Research
and Attribution License 1.0; see `LICENSES/ATLAS.txt`.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer UniquenessLinear.PlaneTensor
open UniquenessLinear.PlaneCensus (Code)
open Atlas.Codes
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
namespace PlaneComparison
variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)

/-- The actual rectangle with its six binary coordinates replaced by hexacode coordinates. -/
def planeHexCoordinates : F.plane ≃* Multiplicative hexacode where
  toEquiv := (sourceEquiv F).symm.trans (hexCoordinates.trans Multiplicative.ofAdd)
  map_mul' a b := by
    obtain ⟨x,rfl⟩ := (sourceEquiv F).surjective a
    obtain ⟨y,rfl⟩ := (sourceEquiv F).surjective b
    have he : sourceEquiv F x * sourceEquiv F y = sourceEquiv F (x ^^^ y) :=
      Subtype.ext (element_xor F x y).symm
    change Multiplicative.ofAdd (hexCoordinates ((sourceEquiv F).symm
      (sourceEquiv F x * sourceEquiv F y))) =
      Multiplicative.ofAdd (hexCoordinates ((sourceEquiv F).symm (sourceEquiv F x))) *
        Multiplicative.ofAdd (hexCoordinates ((sourceEquiv F).symm (sourceEquiv F y)))
    rw [he,Equiv.symm_apply_apply,Equiv.symm_apply_apply,Equiv.symm_apply_apply]
    exact congrArg Multiplicative.ofAdd (hexCoordinates_xor x y)

theorem planeHexCoordinates_source (x : Code) :
    planeHexCoordinates F (sourceEquiv F x) = Multiplicative.ofAdd (hexCoordinates x) :=
  congrArg (fun y => Multiplicative.ofAdd (hexCoordinates y)) ((sourceEquiv F).symm_apply_apply x)

variable [Finite G] (hc : (F.fusion F.plane).ncard = 45)

/-- The full original rectangle quotient, including its cubic kernel. -/
def planeHexQuotientEquiv : planeQuotient F ≃* HexAutomorphisms :=
  (MulEquiv.ofBijective (planeSextetRepresentation F hc)
    ⟨planeSextetRepresentation_injective F hc,
      planeSextetRepresentation_surjective F hc⟩).trans symmetryHexEquiv

/-- The quotient isomorphism intertwines literal conjugation on every rectangle element. -/
theorem planeHexQuotientEquiv_action (n : planeNormalizer F) (a : F.plane) :
    planeHexCoordinates F (F.plane.normalizerMonoidHom n a) =
      hexAffineAction (planeHexQuotientEquiv F hc (QuotientGroup.mk n))
        (planeHexCoordinates F a) := by
  obtain ⟨x,rfl⟩ := (sourceEquiv F).surjective a
  have he : F.plane.normalizerMonoidHom n (sourceEquiv F x) =
      sourceEquiv F (normalizerAction F n x) :=
    Subtype.ext (normalizerAction_element F n x).symm
  rw [he,planeHexCoordinates_source,planeHexCoordinates_source]
  apply congrArg Multiplicative.ofAdd
  have hh := symmetryHexEquiv_action (planeSextetRepresentation F hc (QuotientGroup.mk n)) x
  rw [planeSextetRepresentation_val,quotientCodeAction_mk] at hh
  exact hh

include hc in
/-- Reconstruct the source plane normalizer as the actual affine hexacode group. -/
theorem exists_plane_affine_equiv :
    ∃ e : planeNormalizer F ≃* SextetAffineGroup,
      ∀ a : F.plane, e (inclusion F.plane.le_normalizer a) =
        SemidirectProduct.inl (planeHexCoordinates F a) := by
  obtain ⟨X,_,hX⟩ := plane_splits_of_forty_five F hc
  obtain ⟨e,he,_⟩ := exists_marked_semidirect_equiv_of_split_coordinates
    (F.plane.subgroupOf (planeNormalizer F)) (normalizer (X : Set (planeNormalizer F))) hX
    (planeHexQuotientEquiv F hc)
    ((subgroupOfEquivOfLe F.plane.le_normalizer).trans (planeHexCoordinates F))
    hexAffineAction (by
      intro g a
      exact planeHexQuotientEquiv_action F hc g
        ((subgroupOfEquivOfLe F.plane.le_normalizer) a))
  exact ⟨e,fun a => he ⟨inclusion F.plane.le_normalizer a,a.property⟩⟩

/-- The native stabilizer has the same literal affine coordinates. -/
def nativeAffineEquiv : SextetAffineGroup ≃* sextetStabilizer standardSextet :=
  sextetAffineEquiv.trans SextetCore.sextetEquiv.symm

theorem nativeAffineEquiv_inl (a : Multiplicative hexacode) :
    nativeAffineEquiv (SemidirectProduct.inl a) =
      (M24ChapterHStabilizers.SextetAction.translationEquiv a : sextetStabilizer standardSextet) := by
  unfold nativeAffineEquiv
  rfl

theorem nativeAffineEquiv_quotient (a : SextetAffineGroup) :
    SextetCore.quotientHom (nativeAffineEquiv a) = a.right := by
  change sextetQuotient (SextetCore.sextetEquiv (SextetCore.sextetEquiv.symm
    (sextetAffineEquiv a))) = _
  rw [MulEquiv.apply_symm_apply,sextetQuotient_affine]

/-- Matching the kernel forces the original quotient coordinate, by faithfulness. -/
theorem plane_affine_quotient (e : planeNormalizer F ≃* SextetAffineGroup)
    (he : ∀ a : F.plane, e (inclusion F.plane.le_normalizer a) =
      SemidirectProduct.inl (planeHexCoordinates F a)) (n : planeNormalizer F) :
    (e n).right = planeHexQuotientEquiv F hc (QuotientGroup.mk n) := by
  apply hexAction_injective
  apply LinearEquiv.ext
  intro v
  let a := (planeHexCoordinates F).symm (Multiplicative.ofAdd v)
  have hh := congrArg e (show inclusion F.plane.le_normalizer
    (F.plane.normalizerMonoidHom n a) =
      n * inclusion F.plane.le_normalizer a * n⁻¹ from rfl)
  rw [he,map_mul,map_mul,map_inv,he] at hh
  have hl := congrArg SemidirectProduct.left hh
  simp only [SemidirectProduct.left_inl, SemidirectProduct.mul_left,
    SemidirectProduct.mul_right, SemidirectProduct.right_inl, mul_one,
    SemidirectProduct.inv_left, ← MulAut.mul_apply, ← map_mul,
    mul_inv_cancel, map_one, MulAut.one_apply] at hl
  rw [mul_comm (e n).left, mul_inv_cancel_right, planeHexQuotientEquiv_action F hc] at hl
  have ha : planeHexCoordinates F a = Multiplicative.ofAdd v :=
    (planeHexCoordinates F).apply_symm_apply _
  rw [ha] at hl
  exact congrArg Multiplicative.toAdd hl.symm

include hc in
/-- An actual source/native plane isomorphism preserves the entire rectangle. -/
theorem exists_plane_native_equiv :
    ∃ e : planeNormalizer F ≃* sextetStabilizer standardSextet,
      ∀ a : F.plane, e (inclusion F.plane.le_normalizer a) =
        (M24ChapterHStabilizers.SextetAction.translationEquiv
          (planeHexCoordinates F a) : sextetStabilizer standardSextet) := by
  obtain ⟨e,he⟩ := exists_plane_affine_equiv F hc
  exact ⟨e.trans nativeAffineEquiv,fun a => by
    rw [MulEquiv.trans_apply,he,nativeAffineEquiv_inl]⟩

/-- The same native isomorphism preserves both the rectangle and the full quotient map. -/
theorem exists_plane_native_equiv_quotient :
    ∃ e : planeNormalizer F ≃* sextetStabilizer standardSextet,
      (∀ a : F.plane, e (inclusion F.plane.le_normalizer a) =
        (M24ChapterHStabilizers.SextetAction.translationEquiv
          (planeHexCoordinates F a) : sextetStabilizer standardSextet)) ∧
      ∀ n, SextetCore.quotientHom (e n) = planeHexQuotientEquiv F hc (QuotientGroup.mk n) := by
  obtain ⟨e,he⟩ := exists_plane_affine_equiv F hc
  refine ⟨e.trans nativeAffineEquiv,fun a => ?_,fun n => ?_⟩
  · rw [MulEquiv.trans_apply,he,nativeAffineEquiv_inl]
  · rw [MulEquiv.trans_apply,nativeAffineEquiv_quotient]
    exact plane_affine_quotient F hc e he n


end PlaneComparison
open PlaneComparison
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

/-- Hexacode coordinates on the original oriented A₂, using exactly its marking interchange. -/
def threeSpaceHexCoordinates : F.threeSpace ≃* Multiplicative hexacode :=
  (MulEquiv.subgroupCongr (oppositeMarking_plane F).symm).trans
    (planeHexCoordinates (oppositeMarking F))

/-- The original oriented plane quotient as the full monomial hexacode group. -/
def threeSpaceHexQuotientEquiv (D : LocalData F) : threeSpaceQuotient F ≃* HexAutomorphisms :=
  (threeSpacePlaneQuotientEquiv F).trans
    (planeHexQuotientEquiv (oppositeMarking F) (by
      simpa only [MarkedCentralizer.fusion,oppositeMarking_plane] using D.orientation.2))

omit [Finite G] in
/-- The distinguished involution remains the original marked vector in hexacode coordinates. -/
theorem threeSpaceHexCoordinates_point :
    threeSpaceHexCoordinates F ⟨z,point_mem_threeSpace F⟩ =
      Multiplicative.ofAdd (PlaneComparison.hexCoordinates 4) := by
  have hp : (MulEquiv.subgroupCongr (oppositeMarking_plane F).symm)
      (⟨z,point_mem_threeSpace F⟩ : F.threeSpace) = sourceEquiv (oppositeMarking F) 4 :=
    Subtype.ext (element_point (oppositeMarking F)).symm
  rw [threeSpaceHexCoordinates,MulEquiv.trans_apply,hp,planeHexCoordinates_source]

/-- The actual source plane group and native sextet stabilizer, with original kernel
and quotient maps retained simultaneously. This is the plane-group isomorphism
in source 41.4 before alignment of the common flags. -/
theorem exists_native_plane_equiv (D : LocalData F) :
    ∃ e : threeSpaceNormalizer F ≃* sextetStabilizer standardSextet,
      (∀ a : F.threeSpace, e (inclusion F.threeSpace.le_normalizer a) =
        (M24ChapterHStabilizers.SextetAction.translationEquiv
          (threeSpaceHexCoordinates F a) : sextetStabilizer standardSextet)) ∧
      ∀ n, SextetCore.quotientHom (e n) = threeSpaceHexQuotientEquiv F D (QuotientGroup.mk n) := by
  have hc : ((oppositeMarking F).fusion (oppositeMarking F).plane).ncard = 45 := by
    simpa only [MarkedCentralizer.fusion,oppositeMarking_plane] using D.orientation.2
  obtain ⟨e,hker,hq⟩ := exists_plane_native_equiv_quotient (oppositeMarking F) hc
  let n : threeSpaceNormalizer F ≃* planeNormalizer (oppositeMarking F) :=
    MulEquiv.subgroupCongr (congrArg (fun A : Subgroup G => normalizer (A : Set G))
      (oppositeMarking_plane F).symm)
  refine ⟨n.trans e,fun a => ?_,fun a => ?_⟩
  · exact hker ((MulEquiv.subgroupCongr (oppositeMarking_plane F).symm) a)
  · simp only [threeSpaceHexQuotientEquiv,MulEquiv.trans_apply,threeSpacePlaneQuotientEquiv_mk]
    exact hq (n a)

/-- The same quotient coordinates intertwine the original oriented rectangle action. -/
theorem threeSpaceHexQuotientEquiv_action (D : LocalData F)
    (n : threeSpaceNormalizer F) (a : F.threeSpace) :
    threeSpaceHexCoordinates F (F.threeSpace.normalizerMonoidHom n a) =
      hexAffineAction (threeSpaceHexQuotientEquiv F D (QuotientGroup.mk n))
        (threeSpaceHexCoordinates F a) := by
  obtain ⟨e,hker,hq⟩ := exists_native_plane_equiv F D
  have hh := congrArg e (show inclusion F.threeSpace.le_normalizer
    (F.threeSpace.normalizerMonoidHom n a) =
      n * inclusion F.threeSpace.le_normalizer a * n⁻¹ from rfl)
  rw [hker,map_mul,map_mul,map_inv,hker] at hh
  apply M24ChapterHStabilizers.SextetAction.translationEquiv.injective
  apply Subtype.ext
  calc
    _ = e n * (M24ChapterHStabilizers.SextetAction.translationEquiv
          (threeSpaceHexCoordinates F a) : sextetStabilizer standardSextet) * (e n)⁻¹ := hh
    _ = _ := by
      rw [M24ChapterHStabilizers.SextetAction.translationEquiv_conjugation,hq]


end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
