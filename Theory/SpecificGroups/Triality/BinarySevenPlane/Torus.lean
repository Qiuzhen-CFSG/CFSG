module

public import Theory.SpecificGroups.Triality.BinarySevenPlane.Coefficients
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Torus.Diagonal
public import Theory.GroupAction.QuaternionSevenPlane

/-!
# The marked seven-plane in the original split triality torus

The cubic coefficient generator has seven distinct unit powers. Specializing
these units to the actual extension field, and then applying the faithful
simple-coroot coordinates, embeds the marked plane with columns
(5,5,1,0) and (3,1,0,1). The last two coordinates prove injectivity.

This constructs the split-torus input for the q = 2 nonsplit-torus argument
(ATLAS, printed p.89). Descent to graph-field fixed points still requires the
explicit Lang conjugation and the Weyl actions; this module asserts neither.
-/

@[expose] public section
namespace Triality.Standard.BinarySevenPlane
open Coefficients ConcreteBruhat.TorusCoordinates
open QuaternionSevenPlane
noncomputable section

def powerTable (z : ZMod 7) : Fin 8 := ![1,2,4,3,6,7,5] z
private theorem powerTable_mul : ∀ a b : ZMod 7,
    powerTable (a+b) = mulTable (powerTable a) (powerTable b) := by decide +kernel
private theorem powerTable_injective : Function.Injective powerTable := by decide +kernel

def coefficientUnit (z : ZMod 7) : Scalarˣ where
  val := ⟨powerTable z⟩
  inv := ⟨powerTable (-z)⟩
  val_inv := congrArg Scalar.mk (by rw [← powerTable_mul, add_neg_cancel]; rfl)
  inv_val := congrArg Scalar.mk (by rw [← powerTable_mul, neg_add_cancel]; rfl)

def coefficientUnitHom : Multiplicative (ZMod 7) →* Scalarˣ where
  toFun z := coefficientUnit z.toAdd
  map_one' := by apply Units.ext; rfl
  map_mul' a b := by
    apply Units.ext
    exact congrArg Scalar.mk (powerTable_mul a.toAdd b.toAdd)

lemma coefficientUnitHom_injective : Function.Injective coefficientUnitHom := by
  intro a b h
  have hv := congrArg (fun u : Scalarˣ => u.val.val) h
  exact powerTable_injective hv

def unitHom : Multiplicative (ZMod 7) →*
    (ExtensionField (binaryParameters 1 Nat.zero_lt_one))ˣ :=
  (Units.map actualMap.toMonoidHom).comp coefficientUnitHom

lemma unitHom_injective : Function.Injective unitHom := by
  intro a b h
  apply coefficientUnitHom_injective
  apply Units.ext
  apply actualMap_injective
  exact congrArg Units.val h

/-- The specified columns B = ((5,5,1,0),(3,1,0,1)). -/
def planeCoordinates (z : Plane) : Fin 4 → ZMod 7 :=
  ![5*z.1+3*z.2, 5*z.1+z.2, z.1, z.2]

private lemma planeCoordinates_add (z w : Plane) :
    planeCoordinates (z+w) = planeCoordinates z + planeCoordinates w := by
  funext i
  fin_cases i <;> simp [planeCoordinates] <;> ring

private lemma planeCoordinates_zero : planeCoordinates 0 = 0 := by
  funext i
  fin_cases i <;> simp [planeCoordinates]

private lemma planeCoordinates_injective : Function.Injective planeCoordinates := by
  intro z w h
  apply Prod.ext
  · exact congrFun h 2
  · exact congrFun h 3

def torusCoordinates : Multiplicative Plane →*
    Coordinates (binaryParameters 1 Nat.zero_lt_one) where
  toFun z i := unitHom (Multiplicative.ofAdd (planeCoordinates z.toAdd i))
  map_one' := by
    funext i
    change unitHom (Multiplicative.ofAdd (planeCoordinates 0 i)) = 1
    rw [planeCoordinates_zero]
    exact map_one unitHom
  map_mul' z w := by
    funext i
    change unitHom (Multiplicative.ofAdd (planeCoordinates (z.toAdd+w.toAdd) i)) = _
    rw [planeCoordinates_add]
    exact map_mul unitHom _ _

lemma torusCoordinates_injective : Function.Injective torusCoordinates := by
  intro z w h
  apply planeCoordinates_injective
  funext i
  exact unitHom_injective (congrFun h i)

/-- The exact marked plane inside the literal split torus, before Lang conjugation. -/
def splitEmbedding : Multiplicative Plane →*
    SplitGroup (binaryParameters 1 Nat.zero_lt_one) :=
  (productHom (binaryParameters 1 Nat.zero_lt_one) rfl).comp torusCoordinates

lemma splitEmbedding_injective : Function.Injective splitEmbedding :=
  (product_injective (binaryParameters 1 Nat.zero_lt_one) rfl).comp
    torusCoordinates_injective

theorem splitEmbedding_mem_splitTorus (z : Multiplicative Plane) :
    splitEmbedding z ∈ ConcreteBruhat.splitTorus (binaryParameters 1 Nat.zero_lt_one) :=
  product_mem _ (torusCoordinates z)

end
end Triality.Standard.BinarySevenPlane
