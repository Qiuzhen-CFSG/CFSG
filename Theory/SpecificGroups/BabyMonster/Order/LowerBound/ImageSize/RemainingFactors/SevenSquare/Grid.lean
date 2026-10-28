module

public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.RemainingFactors.Assembly
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# A 49-vector certificate for the square of seven

Two elements of the fixed matrix subgroup shift the two coordinates of an
injectively indexed `ZMod 7 × ZMod 7` grid of row vectors. They preserve its
range, and their powers make the action on that range transitive. Applying
orbit–stabilizer inside the set stabilizer, followed by Lagrange, proves that
49 divides the standard subgroup's order.

Only the action on these vectors is required: the elements need not commute,
or have order seven, on the full 4370-dimensional space. The two-cycle
constructor reduces the grid transitions to 28 row-vector equations using
linearity. All concrete witnesses and equations remain obligations of a
`GridCertificate`.

The matrices use the unchanged ATLAS row convention recorded in
`LowerBound/source/README.md`. The candidate local subgroup program is recorded
in `RemainingFactors/source/README.md`; no identification with its proposed
abstract group is used here.
-/

@[expose] public section

open scoped Pointwise
namespace BabyMonster.OrderLowerBound.RemainingFactors.SevenSquare

section
variable {G X : Type*} [Group G] [MulAction G X]

private theorem card_dvd_of_grid_action (v : ZMod 7 × ZMod 7 → X) (hv : Function.Injective v)
    (x y : G) (hx : ∀ i j, x • v (i,j) = v (i+1,j))
    (hy : ∀ i j, y • v (i,j) = v (i,j+1)) :
    7 ^ 2 ∣ Nat.card G := by
  let S := Set.range v
  let H := MulAction.stabilizer G S
  have hxH : x ∈ H := by
    apply MulAction.mem_stabilizer_iff.mpr
    apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨⟨i,j⟩, rfl⟩, rfl⟩
      exact ⟨(i+1,j), (hx i j).symm⟩
    · rintro _ ⟨⟨i,j⟩, rfl⟩
      refine ⟨v (i-1,j), ⟨(i-1,j), rfl⟩, ?_⟩
      simpa using hx (i-1) j
  have hyH : y ∈ H := by
    apply MulAction.mem_stabilizer_iff.mpr
    apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨⟨i,j⟩, rfl⟩, rfl⟩
      exact ⟨(i,j+1), (hy i j).symm⟩
    · rintro _ ⟨⟨i,j⟩, rfl⟩
      refine ⟨v (i,j-1), ⟨(i,j-1), rfl⟩, ?_⟩
      simpa using hy i (j-1)
  have hxp (n : ℕ) (i j : ZMod 7) : x ^ n • v (i,j) = v (i+n,j) := by
    induction n with
    | zero => simp
    | succ n ih => simp [pow_succ', mul_smul, ih, hx, Nat.cast_add, add_assoc]
  have hyp (n : ℕ) (i j : ZMod 7) : y ^ n • v (i,j) = v (i,j+n) := by
    induction n with
    | zero => simp
    | succ n ih => simp [pow_succ', mul_smul, ih, hy, Nat.cast_add, add_assoc]
  have horbit : MulAction.orbit H (v (0,0)) = S := by
    apply Set.Subset.antisymm
    · rintro _ ⟨g, rfl⟩
      have hmem : (g : G) • v (0,0) ∈ (g : G) • S :=
        ⟨v (0,0), ⟨(0,0),rfl⟩, rfl⟩
      rwa [MulAction.mem_stabilizer_iff.mp g.property] at hmem
    · rintro _ ⟨⟨i,j⟩,rfl⟩
      refine ⟨⟨y ^ j.val * x ^ i.val, H.mul_mem (H.pow_mem hyH _) (H.pow_mem hxH _)⟩, ?_⟩
      change (y ^ j.val * x ^ i.val) • v (0,0) = v (i,j)
      simp only [mul_smul, hxp, hyp, ZMod.natCast_zmod_val, zero_add]
  have hcard : Nat.card (MulAction.orbit H (v (0,0))) = 7 ^ 2 := by
    rw [horbit]
    change Nat.card (Set.range v) = _
    rw [← Nat.card_congr (Equiv.ofInjective v hv)]
    simp
  have hdvd : Nat.card (MulAction.orbit H (v (0,0))) ∣ Nat.card H := by
    refine ⟨Nat.card (MulAction.stabilizer H (v (0,0))), ?_⟩
    rw [← Nat.card_prod]
    exact (Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H (v (0,0)))).symm
  exact hcard ▸ hdvd.trans H.card_subgroup_dvd_card
end

/-- Concrete row-vector data witnessing a transitive set of size 49.
Membership must be proved in the fixed standard matrix subgroup. -/
structure GridCertificate (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1) where
  x : MatrixGroup
  y : MatrixGroup
  x_mem : x ∈ standardImage ha hb
  y_mem : y ∈ standardImage ha hb
  vector : ZMod 7 × ZMod 7 → Fin 4370 → ZMod 2
  injective : Function.Injective vector
  shiftX : ∀ i j, Matrix.vecMul (vector (i,j)) (x : AtlasMatrix) = vector (i+1,j)
  shiftY : ∀ i j, Matrix.vecMul (vector (i,j)) (y : AtlasMatrix) = vector (i,j+1)

/-- A checked grid forces the full square of seven to divide the image order. -/
theorem GridCertificate.card_dvd {ha : atlasA ^ 2 = 1} {hb : atlasB ^ 3 = 1}
    (c : GridCertificate ha hb) : 7 ^ 2 ∣ Nat.card (standardImage ha hb) := by
  let : MulAction (standardImage ha hb) (Fin 4370 → ZMod 2) := {
    smul g w := Matrix.vecMul w (↑((g : MatrixGroup)⁻¹) : AtlasMatrix)
    one_smul w := Matrix.vecMul_one w
    mul_smul g h w := by
      change Matrix.vecMul w (↑(((g : MatrixGroup) * (h : MatrixGroup))⁻¹) : AtlasMatrix) = _
      rw [mul_inv_rev, Units.val_mul, ← Matrix.vecMul_vecMul]
      rfl }
  let x' : standardImage ha hb := ⟨c.x⁻¹, (standardImage ha hb).inv_mem c.x_mem⟩
  let y' : standardImage ha hb := ⟨c.y⁻¹, (standardImage ha hb).inv_mem c.y_mem⟩
  apply card_dvd_of_grid_action c.vector c.injective x' y'
  · intro i j
    change Matrix.vecMul (c.vector (i,j)) (↑((c.x⁻¹)⁻¹) : AtlasMatrix) = _
    simpa only [inv_inv] using c.shiftX i j
  · intro i j
    change Matrix.vecMul (c.vector (i,j)) (↑((c.y⁻¹)⁻¹) : AtlasMatrix) = _
    simpa only [inv_inv] using c.shiftY i j

/-- Two seven-cycles, each fixed by the other generator, give a grid by addition.
Injectivity is required for the sums, so two copies of the same cycle do not
suffice. This constructor requires 28 vector equations instead of 98. -/
def GridCertificate.ofTwoCycles {ha : atlasA ^ 2 = 1} {hb : atlasB ^ 3 = 1}
    (x y : MatrixGroup) (hxmem : x ∈ standardImage ha hb) (hymem : y ∈ standardImage ha hb)
    (u w : ZMod 7 → Fin 4370 → ZMod 2)
    (hinj : Function.Injective (fun ij : ZMod 7 × ZMod 7 => u ij.1 + w ij.2))
    (hxu : ∀ i, Matrix.vecMul (u i) (x : AtlasMatrix) = u (i+1))
    (hxw : ∀ j, Matrix.vecMul (w j) (x : AtlasMatrix) = w j)
    (hyu : ∀ i, Matrix.vecMul (u i) (y : AtlasMatrix) = u i)
    (hyw : ∀ j, Matrix.vecMul (w j) (y : AtlasMatrix) = w (j+1)) :
    GridCertificate ha hb where
  x := x
  y := y
  x_mem := hxmem
  y_mem := hymem
  vector ij := u ij.1 + w ij.2
  injective := hinj
  shiftX i j := by simp only [Matrix.add_vecMul, hxu, hxw]
  shiftY i j := by simp only [Matrix.add_vecMul, hyu, hyw]

end BabyMonster.OrderLowerBound.RemainingFactors.SevenSquare
