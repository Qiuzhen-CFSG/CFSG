module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.PlaneAction.Natural
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Cover
public import Theory.Representation.SymplecticFourOrthogonalCover.FixedLifting

/-!
# Fixed lifts and the original plane two-core

The marked full symplectic group is perfect because it is a quotient of the
actual perfect component. Restriction of the chosen central cover to the
symplectic derived group therefore loses no actors or commutator generation.
The orthogonal-cover fixed-lifting theorem then fixes every original lift of
a fixed natural vector. Applied to the actual plane quotient, it proves that
O₂(L₂) centralizes all of V₂, including C_V(L).

The final theorem discharges the plane-core centralization premise used by
the local radical and orbit arguments. The zero fiber of the binary plane
map is also identified with the literal ambient centralizer.

Source: Aschbacher--Smith, I.2.3(1), 11.1.3 and 11.2.4,
printed pp.413,765,769--770.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.OneCohomology
open scoped MatrixGroups IsMulCommutative
open Matrix
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4.PlaneAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

include m in
private theorem model_isPerfect : Group.IsPerfect (Sp S.field.Carrier) := by
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect S.source.maximal_faithful.1.1
  exact Group.IsPerfect.ofSurjective (Coordinates.sp4 m).quotientMap_surjective

private def derivedProjection :
    Representation.IntertwiningMap
      ((Preliminary.markedAction D m).comp (commutator (Sp S.field.Carrier)).subtype)
      (SymplecticFourOrthogonalCover.binaryNatural (K := S.field.Carrier)) where
  toLinearMap := (Preliminary.markedProjection D m).toLinearMap
  isIntertwining' g := (Preliminary.markedProjection D m).isIntertwining' g.val

private theorem derivedProjection_isCover : IsCover (derivedProjection S m) := by
  let := model_isPerfect S m
  have hp := Preliminary.markedProjection_isCover D m
  refine ⟨hp.1, ?_, ?_⟩
  · intro v hv g
    exact hp.2.1 hv g.val
  · apply top_unique
    rw [← hp.2.2]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,w⟩,rfl⟩
    let g' : commutator (Sp S.field.Carrier) :=
      ⟨g, by rw [Group.IsPerfect.commutator_eq_top]; trivial⟩
    exact Coinvariants.sub_mem_ker g' w

/-- The binary plane map has the literal relative centralizer as its zero fiber. -/
theorem planeMap_eq_zero_iff (v : Additive ((flag m S).Vi 1)) :
    planeMap S m v = 0 ↔ (v.toMul : G) ∈ centralizer (L : Set G) := by
  change naturalPlaneVectorProjection S m v.toMul = 1 ↔ _
  rw [← MonoidHom.mem_ker, naturalPlaneVectorProjection_ker]
  rfl

/-- In the ambient group the vector kernel is exactly V intersect C_G(L). -/
theorem naturalPlaneVectorProjection_ker_map :
    (naturalPlaneVectorProjection S m).ker.map ((flag m S).Vi 1).subtype =
      V ⊓ centralizer (L : Set G) := by
  rw [naturalPlaneVectorProjection_ker]
  ext x
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact ⟨D.centralQuotientPreimage_le _ v.property,hv⟩
  · intro hx
    exact ⟨⟨x,(flag m S).centralizer_le_Vi 1 hx⟩,hx.2,rfl⟩

/-- Every lift in the original central cover is fixed when its natural image is fixed. -/
theorem markedAction_fixed_of_projection_fixed (g : Sp S.field.Carrier) (w : D.space)
    (hw : symplecticNatural 2 g (Preliminary.markedProjection D m w) =
      Preliminary.markedProjection D m w) :
    Preliminary.markedAction D m g w = w := by
  let := model_isPerfect S m
  let g' : SymplecticFourOrthogonalCover.L (K := S.field.Carrier) :=
    ⟨g, by rw [Group.IsPerfect.commutator_eq_top]; trivial⟩
  exact SymplecticFourOrthogonalCover.cover_fixed_of_projection_fixed
    (derivedProjection S m) (derivedProjection_isCover S m) g' w hw

/-- Fixed-vector lifting is transported through the original chosen-space equivalence. -/
theorem component_fixed_of_projection_fixed (l : L) (v : V)
    (hv : (Coordinates.sp4 m).modelAction ((Coordinates.sp4 m).quotientMap l)
      ((Coordinates.sp4 m).projection v).toAdd = ((Coordinates.sp4 m).projection v).toAdd) :
    V.normalizerMonoidHom (inclusion D.normalizes l) v = v := by
  let w : D.space := (D.spaceEquiv.symm v).toAdd
  have hw : (w.val.toMul.val : G) = (v : G) :=
    (D.spaceEquiv_apply w).symm.trans
      (congrArg Subtype.val (D.spaceEquiv.apply_symm_apply v))
  have he : D.spaceEquiv (Multiplicative.ofAdd (D.chosenAction l w)) =
      V.normalizerMonoidHom (inclusion D.normalizes l) v := by
    apply Subtype.ext
    rw [D.spaceEquiv_apply]
    change (l : G) * (w.val.toMul.val : G) * (l : G)⁻¹ = _
    rw [hw]
    rfl
  have hf := markedAction_fixed_of_projection_fixed S m
    ((Coordinates.sp4 m).quotientMap l) w hv
  change Preliminary.markedAction D m
    (m.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)) w = w at hf
  rw [Preliminary.markedAction_mk] at hf
  rw [← he, hf]
  exact D.spaceEquiv.apply_symm_apply v

/-- The actual quotient-plane action has precisely its two-core as kernel. -/
theorem planeAction_fixes_iff (l : (flag m S).Li 1) :
    (∀ v, planeAction S m l v = v) ↔ l ∈ pCore 2 ((flag m S).Li 1) := by
  rw [← planeProjection_ker S m]
  change (∀ v, planeAction S m l v = v) ↔ planeProjection S m l = 1
  constructor
  · intro h
    apply specialLinearNatural_injective 2
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := (alignedPlaneCoordinates S m).surjective w
    rw [← alignedPlaneCoordinates_intertwines, h]
    simp
  · intro h v
    apply (alignedPlaneCoordinates S m).injective
    rw [alignedPlaneCoordinates_intertwines]
    rw [show planeProjection S m l = 1 from h, map_one]
    rfl

/-- The full original plane preimage, including C_V(L), is centralized by O₂(L₂). -/
theorem planeCore_centralizes :
    ((flag m S).Li 1).pCoreIn 2 ≤ centralizer ((flag m S).Vi 1 : Set G) := by
  rintro x ⟨l,hl,rfl⟩ v hv
  let v' : V := ⟨v,D.centralQuotientPreimage_le _ hv⟩
  have hvq : ((Coordinates.sp4 m).projection v').toAdd ∈ (flag m S).space 1 :=
    ((Coordinates.sp4 m).mem_preimage _ _).mp hv
  have hfix := (planeAction_fixes_iff S m l).mpr hl
    ⟨((Coordinates.sp4 m).projection v').toAdd,hvq⟩
  have h := component_fixed_of_projection_fixed S m
    ⟨l.val,(localResidual_le _ l.property).1⟩ v' (congrArg Subtype.val hfix)
  have he : (l : G) * v * (l : G)⁻¹ = v := congrArg Subtype.val h
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4.PlaneAction
