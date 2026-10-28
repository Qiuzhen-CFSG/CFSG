module
public import Theory.Representation.PSL3Two.AffineConstituents
public import Theory.SpecificGroups.PSL3.LinearThreeFlags
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
/-!
# Coinvariants for the point-parabolic natural and dual modules

Two explicit action differences span the binary natural module; cubic differences
span its dual annihilator plane. For a field with a nonidentity unit, two diagonal
elements span the whole natural and dual modules. The formulas work componentwise
for arbitrary families, so multiplicity zero requires no special argument.
These are statements about arbitrary additive subgroups, not just F-subspaces.

Source application: Aschbacher–Smith, G.2.5(8), printed pp.335–336.
-/
@[expose] public section
set_option linter.unusedSimpArgs false
open Matrix Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.PointParabolicCoinvariants
open Matrix.PSL3Two.MarkedAutomorphisms
open Matrix.PSL3Two.MarkedAutomorphisms.AffineConstituents
private def shear : pointA := ⟨⟨!![1,1,0; 0,1,0; 0,0,1], by decide +kernel⟩, by exact ⟨rfl,rfl,Or.inl ⟨rfl,rfl,rfl,rfl⟩⟩⟩
private theorem binary_natural_split : ∀ v : V,
    v = (natural shear ![0,v 0,0] - ![0,v 0,0]) +
      (natural ⟨cubic,cubic_mem⟩ ![0,v 2,v 1 + v 2] - ![0,v 2,v 1 + v 2]) := by
  decide +kernel
private theorem binary_dual_split : ∀ v : V, v 0 = 0 →
    v = dual ⟨cubic,cubic_mem⟩ ![0,v 1 + v 2,v 1] - ![0,v 1 + v 2,v 1] := by
  decide +kernel

/-- The binary natural module has no nonzero trivial quotient. -/
theorem binary_natural_full (C : AddSubgroup V)
    (hc : ∀ a : pointA, ∀ v : V, natural a v - v ∈ C) : C = ⊤ := by
  apply top_unique
  intro v _
  rw [binary_natural_split v]
  exact C.add_mem (hc _ _) (hc _ _)

theorem binary_natural_copies_full {ι : Type*} (C : AddSubgroup (ι → V))
    (hc : ∀ a : pointA, ∀ v : ι → V, (fun i => natural a (v i) - v i) ∈ C) : C = ⊤ := by
  apply top_unique
  intro v _
  have h1 := hc shear (fun i => ![0,v i 0,0])
  have h2 := hc ⟨cubic,cubic_mem⟩ (fun i => ![0,v i 2,v i 1 + v i 2])
  have he : v = (fun i => natural shear ![0,v i 0,0] - ![0,v i 0,0]) +
      (fun i => natural ⟨cubic,cubic_mem⟩ ![0,v i 2,v i 1 + v i 2] - ![0,v i 2,v i 1 + v i 2]) :=
    funext fun i => binary_natural_split (v i)
  rw [he]
  exact C.add_mem h1 h2

theorem binary_dual_planes_mem {ι : Type*} (C : AddSubgroup (ι → V))
    (hc : ∀ a : pointA, ∀ v : ι → V, (fun i => dual a (v i) - v i) ∈ C)
    (v : ι → V) (hv : ∀ i, v i 0 = 0) : v ∈ C := by
  have he : v = fun i => dual ⟨cubic,cubic_mem⟩ ![0,v i 1 + v i 2,v i 1] -
      ![0,v i 1 + v i 2,v i 1] := funext fun i => binary_dual_split (v i) (hv i)
  rw [he]
  exact hc _ _
end Matrix.PSL3.PointParabolicCoinvariants


namespace Matrix.PSL3.PointParabolicCoinvariants
open Matrix.PSL3.LinearThree
variable {F : Type*} [Field F] [Finite F]
private def torusOne (u : Fˣ) : pointParabolicSL F :=
  ⟨pointTorus F u, (pointTorus_mem_borel F u).1⟩
private def torusTwo (u : Fˣ) : pointParabolicSL F :=
  ⟨lineTorus F u, (lineTorus_mem_borel F u).1⟩
private theorem natural_split (u : Fˣ) (hu : (u : F) ≠ 1) (v : Fin 3 → F) :
    v = ((torusOne u).val.val *ᵥ ![v 0 / (u - 1), v 1 / (↑u⁻¹ - 1), 0] -
      ![v 0 / (u - 1), v 1 / (↑u⁻¹ - 1), 0]) +
      ((torusTwo u).val.val *ᵥ ![0,0,v 2 / (u - 1)] - ![0,0,v 2 / (u - 1)]) := by
  have hu' : (↑u⁻¹ : F) ≠ 1 := by simpa using hu
  ext i
  simp only [torusOne, torusTwo, pointTorus, lineTorus, Pi.add_apply, Pi.sub_apply,
    mulVec_diagonal]
  fin_cases i <;> simp
  all_goals field_simp [sub_ne_zero.mpr hu, sub_ne_zero.mpr hu']

private theorem dual_split (u : Fˣ) (hu : (u : F) ≠ 1) (v : Fin 3 → F) :
    v = (((torusOne u)⁻¹).val⁻¹.val.transpose *ᵥ ![v 0 / (u - 1), v 1 / (↑u⁻¹ - 1), 0] -
      ![v 0 / (u - 1), v 1 / (↑u⁻¹ - 1), 0]) +
      (((torusTwo u)⁻¹).val⁻¹.val.transpose *ᵥ ![0,0,v 2 / (u - 1)] - ![0,0,v 2 / (u - 1)]) := by
  change v = ((pointTorus F u)⁻¹⁻¹.val.transpose *ᵥ _ - _) +
    ((lineTorus F u)⁻¹⁻¹.val.transpose *ᵥ _ - _)
  rw [inv_inv, inv_inv]
  simpa only [torusOne, torusTwo, pointTorus, lineTorus, diagonal_transpose]
    using natural_split u hu v

theorem natural_full (u : Fˣ) (hu : (u : F) ≠ 1) (C : AddSubgroup (Fin 3 → F))
    (hc : ∀ a : pointParabolicSL F, ∀ v : Fin 3 → F, a.val.val *ᵥ v - v ∈ C) : C = ⊤ := by
  apply top_unique
  intro v _
  rw [natural_split u hu v]
  exact C.add_mem (hc _ _) (hc _ _)

theorem natural_copies_full {ι : Type*} (u : Fˣ) (hu : (u : F) ≠ 1)
    (C : AddSubgroup (ι → Fin 3 → F))
    (hc : ∀ a : pointParabolicSL F, ∀ v : ι → Fin 3 → F,
      (fun i => a.val.val *ᵥ v i - v i) ∈ C) : C = ⊤ := by
  apply top_unique
  intro v _
  have he := funext fun i => natural_split u hu (v i)
  rw [he]
  exact C.add_mem (hc _ _) (hc _ _)

theorem dual_copies_full {ι : Type*} (u : Fˣ) (hu : (u : F) ≠ 1)
    (C : AddSubgroup (ι → Fin 3 → F))
    (hc : ∀ a : pointParabolicSL F, ∀ v : ι → Fin 3 → F,
      (fun i => a.val⁻¹.val.transpose *ᵥ v i - v i) ∈ C) : C = ⊤ := by
  apply top_unique
  intro v _
  have he := funext fun i => dual_split u hu (v i)
  rw [he]
  exact C.add_mem (hc _ _) (hc _ _)
end Matrix.PSL3.PointParabolicCoinvariants
