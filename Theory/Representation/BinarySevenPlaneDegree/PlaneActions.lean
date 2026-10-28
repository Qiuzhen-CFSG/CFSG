module

public import Theory.GroupAction.QuaternionSevenPlane
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

/-!
# Twenty-four separating maps on the seven-plane

The maps are the eight quaternion words U^j V^k followed by the three
scalar powers of two. Distinct words have invertible differences. We check
the 2-by-2 determinants over F7, then use surjectivity of the differences
to show that their pullbacks of any nontrivial character are distinct.

The marking U,V is the one in `QuaternionSevenPlane.Data`, motivated by
the triality normalizer in ATLAS, printed p.89. Pullbacks by U,V will be
realized by the inverse ambient elements in the representation application.
-/

public section

namespace Representation.BinarySevenPlaneDegree
open QuaternionSevenPlane
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

@[expose] def firstLinear : Module.End (ZMod 7) Plane where
  toFun := firstMap
  map_add' x y := by ext <;> simp [firstMap, mul_add]
  map_smul' a x := by ext <;> simp [firstMap, mul_left_comm]

@[expose] def secondLinear : Module.End (ZMod 7) Plane where
  toFun := secondMap
  map_add' x y := by ext <;> simp [secondMap] <;> ring
  map_smul' a x := by ext <;> simp [secondMap] <;> ring

@[expose] def doubleLinear : Module.End (ZMod 7) Plane := 2 • 1

abbrev OrbitIndex := Fin 3 × Fin 4 × Fin 2
@[expose] def orbitMap (i : OrbitIndex) : Module.End (ZMod 7) Plane :=
  (firstLinear ^ i.2.1.val * secondLinear ^ i.2.2.val) * doubleLinear ^ i.1.val

private def determinant (f : Module.End (ZMod 7) Plane) : ZMod 7 :=
  (f (1, 0)).1 * (f (0, 1)).2 - (f (0, 1)).1 * (f (1, 0)).2

private lemma map_coordinates (f : Module.End (ZMod 7) Plane) (z : Plane) :
    f z = (z.1 * (f (1, 0)).1 + z.2 * (f (0, 1)).1,
      z.1 * (f (1, 0)).2 + z.2 * (f (0, 1)).2) := by
  have hz : z = z.1 • ((1, 0) : Plane) + z.2 • ((0, 1) : Plane) := by
    ext <;> simp
  rw [hz, map_add, map_smul, map_smul]
  ext <;> simp [smul_eq_mul]

private lemma surjective_of_determinant_ne (f : Module.End (ZMod 7) Plane)
    (h : determinant f ≠ 0) : Function.Surjective f := by
  intro z
  refine ⟨(((f (0, 1)).2 * z.1 - (f (0, 1)).1 * z.2) / determinant f,
    ((f (1, 0)).1 * z.2 - (f (1, 0)).2 * z.1) / determinant f), ?_⟩
  rw [map_coordinates]
  ext <;> dsimp only <;> field_simp [h] <;> simp only [determinant] <;> ring

private lemma orbit_differences : ∀ i j : OrbitIndex, i ≠ j →
    determinant (orbitMap i - orbitMap j) ≠ 0 := by decide

lemma orbit_difference_surjective (i j : OrbitIndex) (h : i ≠ j) :
    Function.Surjective (fun z => orbitMap i z - orbitMap j z) :=
  surjective_of_determinant_ne _ (orbit_differences i j h)

@[expose] def pullback {H : Type*} [Group H] (chi : Multiplicative Plane →* H)
    (f : Module.End (ZMod 7) Plane) : Multiplicative Plane →* H :=
  chi.comp (AddMonoidHom.toMultiplicative f.toAddMonoidHom)

lemma pullback_mul {H : Type*} [Group H] (chi : Multiplicative Plane →* H)
    (f g : Module.End (ZMod 7) Plane) :
    pullback (pullback chi f) g = pullback chi (f * g) := rfl

lemma pullback_one {H : Type*} [Group H] (chi : Multiplicative Plane →* H) :
    pullback chi 1 = chi := rfl

lemma pullback_double {H : Type*} [CommGroup H] (chi : Multiplicative Plane →* H) :
    pullback chi doubleLinear = chi ^ 2 := by
  apply MonoidHom.ext
  intro x
  change chi (Multiplicative.ofAdd (2 • Multiplicative.toAdd x)) = chi x ^ 2
  rw [two_smul]
  change chi (x * x) = chi x ^ 2
  rw [map_mul, pow_two]

lemma orbit_pullback_injective {H : Type*} [Group H]
    (chi : Multiplicative Plane →* H) (hchi : chi ≠ 1) :
    Function.Injective (fun i => pullback chi (orbitMap i)) := by
  intro i j hij
  by_contra hne
  apply hchi
  apply MonoidHom.ext
  intro x
  obtain ⟨z, hz⟩ := orbit_difference_surjective i j hne (Multiplicative.toAdd x)
  have he := DFunLike.congr_fun hij (Multiplicative.ofAdd z)
  change chi (Multiplicative.ofAdd (orbitMap i z)) =
    chi (Multiplicative.ofAdd (orbitMap j z)) at he
  change chi x = 1
  rw [← ofAdd_toAdd x, ← hz]
  change chi (Multiplicative.ofAdd (orbitMap i z) /
    Multiplicative.ofAdd (orbitMap j z)) = 1
  rw [map_div, he, div_self']

end Representation.BinarySevenPlaneDegree
