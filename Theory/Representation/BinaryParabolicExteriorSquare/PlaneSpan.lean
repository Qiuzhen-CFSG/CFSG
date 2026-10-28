module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.ExteriorAction
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# A plane stabilizer on the binary exterior six-space

The bivector coordinates are 01, 02, 03, 12, 13, 23. The three-space
01,02,03 generates the hyperplane with last coordinate zero under the
natural plane stabilizer. One shear generates the missing two coordinates;
the opposite shear forces every invariant kernel whose intersection with
the three-space lies in 01 to lie in that same line.

These calculations supply the five-dimensional span and its exact kernel
in Aschbacher–Smith 13.8.30, printed p.964. The source application uses
the original conjugation sections and the literal L₁ actors. The exterior
model is the attributed ATLAS model imported above.
-/

@[expose] public noncomputable section
open Atlas.Order20160A8.Bivectors
namespace Representation.BinaryParabolicExteriorSquare.PlaneSpan
abbrev Bit := ZMod 2
abbrev Six := Fin 6 → Bit

def firstSpace : Submodule Bit Six where
  carrier := {x | x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0}
  zero_mem' := by simp
  add_mem' := by rintro x y ⟨h3,h4,h5⟩ ⟨k3,k4,k5⟩; simp_all
  smul_mem' := by rintro a x ⟨h3,h4,h5⟩; simp_all

def planeSpace : Submodule Bit Six := LinearMap.ker (LinearMap.proj 5)

def pointSpace : Submodule Bit Six where
  carrier := {x | x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0}
  zero_mem' := by simp
  add_mem' := by rintro x y ⟨h1,h2,h3,h4,h5⟩ ⟨k1,k2,k3,k4,k5⟩; simp_all
  smul_mem' := by rintro a x ⟨h1,h2,h3,h4,h5⟩; simp_all

theorem firstSpace_le_planeSpace : firstSpace ≤ planeSpace := fun _ h => h.2.2

def delta (i j : Fin 4) (x : Six) : Six :=
  exteriorMap (Matrix.transvection i j (1 : Bit)) x - x

theorem delta_01 (x : Six) : delta 0 1 x = ![0,x 3,x 4,0,0,0] := by
  ext t
  fin_cases t <;>
    simp [delta, exteriorMap, compound, first, second, Matrix.transvection,
      Matrix.single, Matrix.one_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, sub_eq_add_neg, ZMod.neg_eq_self_mod_two] <;>
    ring_nf <;> simp [show (2 : Bit) = 0 from by decide]

theorem delta_10 (x : Six) : delta 1 0 x = ![0,0,0,x 1,x 2,0] := by
  ext t
  fin_cases t <;>
    simp [delta, exteriorMap, compound, first, second, Matrix.transvection,
      Matrix.single, Matrix.one_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, sub_eq_add_neg, ZMod.neg_eq_self_mod_two] <;>
    ring_nf <;> simp [show (2 : Bit) = 0 from by decide]

/-- A matrix preserving the natural plane preserves its exterior hyperplane. -/
theorem planeSpace_preserved (A : Matrix (Fin 4) (Fin 4) Bit)
    (h20 : A 2 0 = 0) (h21 : A 2 1 = 0) (h30 : A 3 0 = 0) (h31 : A 3 1 = 0)
    (x : Six) (hx : x ∈ planeSpace) : exteriorMap A x ∈ planeSpace := by
  change x 5 = 0 at hx
  change exteriorMap A x 5 = 0
  simp [exteriorMap, compound, first, second, Matrix.toLin'_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h20, h21, h30, h31, hx]

/-- One opposite shear generates the five-space from the first three-space. -/
theorem planeSpace_le_of_shear (P : Submodule Bit Six) (hfirst : firstSpace ≤ P)
    (hshear : ∀ x ∈ P, exteriorMap (Matrix.transvection 1 0 (1 : Bit)) x ∈ P) :
    planeSpace ≤ P := by
  intro x hx
  change x 5 = 0 at hx
  let u : Six := ![x 0,x 1,x 2,0,0,0]
  let v : Six := ![0,x 3,x 4,0,0,0]
  have hu : u ∈ P := hfirst (by change _ ∧ _ ∧ _; simp [u])
  have hv : v ∈ P := hfirst (by change _ ∧ _ ∧ _; simp [v])
  have hd : delta 1 0 v ∈ P := P.sub_mem (hshear v hv) hv
  have he : x = u + delta 1 0 v := by
    rw [delta_10]
    ext i
    fin_cases i <;> simp [u, v, hx]
  rw [he]
  exact P.add_mem hu hd

/-- Invariance under the other shear forces the kernel back into the known point. -/
theorem kernel_le_point (P : Submodule Bit Six) (hP : P ≤ planeSpace)
    (hfirst : P ⊓ firstSpace ≤ pointSpace)
    (hshear : ∀ x ∈ P, exteriorMap (Matrix.transvection 0 1 (1 : Bit)) x ∈ P) :
    P ≤ pointSpace := by
  intro x hx
  have hd : delta 0 1 x ∈ P := P.sub_mem (hshear x hx) hx
  have hdA : delta 0 1 x ∈ firstSpace := by
    rw [delta_01]; change _ ∧ _ ∧ _; simp
  have hdC := hfirst ⟨hd,hdA⟩
  have h3 : x 3 = 0 := by simpa [delta_01] using hdC.1
  have h4 : x 4 = 0 := by simpa [delta_01] using hdC.2.1
  exact hfirst ⟨hx,h3,h4,hP hx⟩

def planeCoordinates : (Fin 5 → Bit) ≃ₗ[Bit] planeSpace where
  toFun x := ⟨![x 0,x 1,x 2,x 3,x 4,0],rfl⟩
  invFun x := ![x.val 0,x.val 1,x.val 2,x.val 3,x.val 4]
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv x := by
    apply Subtype.ext
    ext i
    fin_cases i <;> try rfl
    exact x.property.symm
  map_add' x y := by apply Subtype.ext; ext i; fin_cases i <;> simp
  map_smul' a x := by apply Subtype.ext; ext i; fin_cases i <;> simp

def firstCoordinates : (Fin 3 → Bit) ≃ₗ[Bit] firstSpace where
  toFun x := ⟨![x 0,x 1,x 2,0,0,0],by change _ ∧ _ ∧ _; simp⟩
  invFun x := ![x.val 0,x.val 1,x.val 2]
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv x := by
    apply Subtype.ext
    ext i
    fin_cases i <;> try rfl
    · exact x.property.1.symm
    · exact x.property.2.1.symm
    · exact x.property.2.2.symm
  map_add' x y := by apply Subtype.ext; ext i; fin_cases i <;> simp
  map_smul' a x := by apply Subtype.ext; ext i; fin_cases i <;> simp

theorem firstSpace_finrank : Module.finrank Bit firstSpace = 3 := by
  rw [← firstCoordinates.finrank_eq, Module.finrank_pi]
  simp

theorem planeSpace_finrank : Module.finrank Bit planeSpace = 5 := by
  rw [← planeCoordinates.finrank_eq, Module.finrank_pi]
  simp

end Representation.BinaryParabolicExteriorSquare.PlaneSpan
