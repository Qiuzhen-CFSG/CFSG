module

public import Theory.Representation.HexacodeAction.Field
public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeLocalSimple

/-!
# The local hexacode kernel on its natural F4 plane

The kernel of the first systematic coordinate is a two-dimensional subspace
of the genuine hexacode F4 module. Its remaining two systematic coordinates
give a concrete linear equivalence to F4 squared. The local letter kernel is
even, so its action on this space is F4-linear. Its geometric A5 identification
gives perfectness and therefore determinant one. Faithfulness and the matching
orders 60 make these very matrices an equivalence with SL2(4).

The native application, including its literal quotient and conjugation map,
is in `Quintet.Natural`. The coordinate map is fixed by the hexacode geometry;
no arbitrary vector-space equivalence is used for the action identification.

Source: Aschbacher--Smith H.14.3(2), printed p.397, deduced there from H.14.1(2).
The underlying hexacode, local kernel, and faithfulness results are the licensed
ATLAS ports of Gerald Höhn and ATLAS contributors, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`; see `LICENSES/ATLAS.txt` and the
attribution in `HexacodeLocalSimple`. The F4 structure and matrix carrier reuse
`Representation.HexacodeAction.Field` and `SL2FourNaturalOrbits.Model`.
-/

public section

noncomputable section
open Atlas.Codes
open Representation.Hexacode
namespace Representation.Hexacode.ZeroNatural

abbrev index : HexIndex := firstThree 0

/-- The first-coordinate kernel as a genuine F4 subspace of the hexacode. -/
def fieldSpace : Submodule F hexacode :=
  ((LinearMap.proj (0 : Fin 3)).comp fieldCoordinates.toLinearMap).ker

theorem mem_fieldSpace (w : hexacode) : w ∈ fieldSpace ↔ w.val index = 0 := by
  change orientedLetter index (w.val index) = 0 ↔ _
  exact (orientedLetter index).map_eq_zero_iff

/-- The same coordinate kernel, retaining its original binary structure. -/
def fieldSpaceBinary : hexZeroCoordinate index ≃ₗ[Bit] fieldSpace where
  toFun w := ⟨w.val, (mem_fieldSpace w.val).mpr w.property⟩
  invFun w := ⟨w.val, (mem_fieldSpace w.val).mp w.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The two remaining systematic field coordinates. -/
def fieldVectorCoordinates : fieldSpace ≃ₗ[F] SL2FourNatural.V where
  toFun w j := fieldCoordinates w.val j.succ
  invFun v := ⟨fieldCoordinates.symm (Fin.cons 0 v), by
    change fieldCoordinates (fieldCoordinates.symm (Fin.cons 0 v)) 0 = 0
    rw [fieldCoordinates.apply_symm_apply]
    rfl⟩
  left_inv w := by
    apply Subtype.ext
    apply fieldCoordinates.injective
    rw [fieldCoordinates.apply_symm_apply]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact w.property.symm
    · rfl
  right_inv v := by
    funext i
    change fieldCoordinates (fieldCoordinates.symm (Fin.cons 0 v)) i.succ = v i
    rw [fieldCoordinates.apply_symm_apply]
    rfl
  map_add' u v := by
    funext i
    exact congrFun (fieldCoordinates.map_add u.val v.val) i.succ
  map_smul' c v := by
    funext i
    exact congrFun (fieldCoordinates.map_smul c v.val) i.succ

/-- An explicit binary equivalence to the natural two-dimensional F4 vector space. -/
def vectorCoordinates : hexZeroCoordinate index ≃ₗ[Bit] SL2FourNatural.V :=
  fieldSpaceBinary.trans (fieldVectorCoordinates.restrictScalars Bit)

private theorem fieldSpace_stable (g : hexPointKernel index) (w : fieldSpace) :
    action g.val.val w.val ∈ fieldSpace := by
  rw [mem_fieldSpace]
  change g.val.val.val.localMap index (w.val.val (g.val.val.val.perm.symm index)) = 0
  rw [hexPointStabilizer_inv_fixed]
  rw [(mem_fieldSpace w.val).mp w.property, map_zero]

/-- The geometric local kernel acts F4-linearly on its coordinate-zero space. -/
def fieldAction : hexPointKernel index →* (fieldSpace ≃ₗ[F] fieldSpace) where
  toFun g :=
    { toFun w := ⟨action g.val.val w.val, fieldSpace_stable g w⟩
      invFun w := ⟨action g.val.val⁻¹ w.val, fieldSpace_stable g⁻¹ w⟩
      left_inv w := by
        apply Subtype.ext
        change hexAction g.val.val⁻¹ (hexAction g.val.val w.val) = w.val
        rw [map_inv]
        exact LinearEquiv.symm_apply_apply (hexAction g.val.val) w.val
      right_inv w := by
        apply Subtype.ext
        change hexAction g.val.val (hexAction g.val.val⁻¹ w.val) = w.val
        rw [map_inv]
        exact LinearEquiv.apply_symm_apply (hexAction g.val.val) w.val
      map_add' u v := Subtype.ext (map_add (action g.val.val) u.val v.val)
      map_smul' c w := Subtype.ext (action_even_smul _ (hexPointKernel_even index g) c w.val) }
  map_one' := by
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    exact LinearEquiv.congr_fun hexAction.map_one w.val
  map_mul' g h := by
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    exact LinearEquiv.congr_fun (hexAction.map_mul g.val.val h.val.val) w.val

/-- The same action in the two actual systematic coordinates. -/
def vectorAction : hexPointKernel index →* (SL2FourNatural.V ≃ₗ[F] SL2FourNatural.V) where
  toFun g := fieldVectorCoordinates.symm.trans ((fieldAction g).trans fieldVectorCoordinates)
  map_one' := by
    apply LinearEquiv.ext
    intro v
    simp
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    simp

theorem vectorAction_equivariant (g : hexPointKernel index) (w : hexZeroCoordinate index) :
    vectorAction g (vectorCoordinates w) = vectorCoordinates (hexZeroLinear index g.val w) := by
  change fieldVectorCoordinates (fieldAction g
    (fieldVectorCoordinates.symm (fieldVectorCoordinates (fieldSpaceBinary w)))) = _
  rw [fieldVectorCoordinates.symm_apply_apply]
  rfl

theorem vectorAction_injective : Function.Injective vectorAction := by
  intro g h he
  apply hexZeroAffineAction_injective index
  apply MulEquiv.ext
  intro w
  apply Multiplicative.toAdd.injective
  apply vectorCoordinates.injective
  exact (vectorAction_equivariant g w.toAdd).symm.trans
    ((LinearEquiv.congr_fun he (vectorCoordinates w.toAdd)).trans
      (vectorAction_equivariant h w.toAdd))

private theorem localPerfect : Group.IsPerfect (hexPointKernel index) := by
  let e := hexPointKernelA5Equiv index
  have : Group.IsPerfect (alternatingGroup (({index} : Finset HexIndex)ᶜ : Finset HexIndex)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp [Nat.card_eq_fintype_card, HexIndex])⟩
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem vectorAction_det (g : hexPointKernel index) : LinearEquiv.det (vectorAction g) = 1 := by
  let := localPerfect
  let f : hexPointKernel index →* Fˣ := LinearEquiv.det.comp vectorAction
  let := Group.IsPerfect.range f
  have h : (⟨f g, ⟨g, rfl⟩⟩ : f.range) = 1 := Subsingleton.elim _ _
  exact congrArg Subtype.val h

def matrixAction : hexPointKernel index →* SL2FourNatural.SL where
  toFun g := ⟨LinearMap.toMatrix' (vectorAction g).toLinearMap, by
    rw [LinearMap.det_toMatrix']
    simpa only [LinearEquiv.coe_det, Units.val_one] using congrArg Units.val (vectorAction_det g)⟩
  map_one' := by
    apply Subtype.ext
    simp [map_one]
  map_mul' g h := by
    apply Subtype.ext
    change LinearMap.toMatrix' (vectorAction (g * h)).toLinearMap =
      LinearMap.toMatrix' (vectorAction g).toLinearMap * LinearMap.toMatrix' (vectorAction h).toLinearMap
    rw [map_mul]
    exact LinearMap.toMatrix'_mul (vectorAction g).toLinearMap (vectorAction h).toLinearMap

theorem matrixAction_equivariant (g : hexPointKernel index) (w : hexZeroCoordinate index) :
    SL2FourNatural.action (matrixAction g) (vectorCoordinates w) =
      vectorCoordinates (hexZeroLinear index g.val w) := by
  rw [SL2FourNatural.action_apply]
  change (LinearMap.toMatrix' (vectorAction g).toLinearMap).mulVec (vectorCoordinates w) = _
  rw [LinearMap.toMatrix'_mulVec]
  exact vectorAction_equivariant g w

theorem matrixAction_bijective : Function.Bijective matrixAction := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  constructor
  · intro g h he
    apply vectorAction_injective
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.toMatrix'.injective
    exact congrArg Subtype.val he
  · rw [hexPointKernel_card, Nat.card_eq_fintype_card]
    decide +kernel

/-- The genuine local coordinate action group is SL2(4), via its natural matrices. -/
@[expose] def modelEquiv : hexPointKernel index ≃* SL2FourNatural.SL :=
  MulEquiv.ofBijective matrixAction matrixAction_bijective

end Representation.Hexacode.ZeroNatural
