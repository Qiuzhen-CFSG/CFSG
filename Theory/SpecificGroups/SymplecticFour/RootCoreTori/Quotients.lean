module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearLocalKernel.Parabolics
public import Theory.GroupTheory.CharacteristicCoreCenter
public import Theory.SpecificGroups.PSL2.AutomorphismModel
import Mathlib.Tactic.FinCases

/-!
# Scalar tori in the centers of the symplectic Levi quotients

The point torus `diagonalTorus s 1` acts trivially on the middle-block
SL₂ quotient. The plane torus `diagonalTorus s s` restricts to a scalar
matrix, so its commutators with the full plane parabolic also lie in the
two-core. Determinant characters put these commutators in the local
factors, and the actual quotient kernels identify their core membership.

In each parabolic the embedded two-core is the local quotient kernel.
An element of the local factor central modulo this core therefore maps
to the center of SL₂, which is trivial in characteristic two. This gives
the separation needed for a compatible root-centralizer complement.
All cores and normality are relative to the stated parabolic or local factor.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the
symplectic case of E.6.11(3c), printed pp.249–250 (PDF pp.260–261),
and the commutator bound in E.6.25, printed p.255 (PDF p.266).
-/

public section

open Subgroup Matrix
open scoped commutatorElement
namespace Theory.SpecificGroups.SymplecticFour.RootCoreTori
open DiagramAutomorphisms

private theorem separation {G S : Type*} [Group G] [Group S]
    (P C : Subgroup G) (hCP : C ≤ P) (p : ℕ)
    (f : C →* S) (hf : Function.Surjective f)
    (hker : P.pCoreIn p = f.ker.map C.subtype) (hZ : center S = ⊥) :
    P.coreCenterIn p ⊓ C ≤ P.pCoreIn p := by
  rintro x ⟨hx, hxc⟩
  let c : C := ⟨x, hxc⟩
  have hc : f c ∈ center S := by
    apply mem_center_iff.mpr
    intro s
    obtain ⟨d, rfl⟩ := hf s
    have hh := ((mem_coreCenterIn_iff p P x).mp hx).2 d (hCP d.property)
    rw [hker] at hh
    have hm : ⁅c, d⁆ ∈ f.ker :=
      (mem_map_iff_mem C.subtype_injective).mp hh
    have he : ⁅f c, f d⁆ = 1 := by
      rw [← map_commutatorElement]
      exact hm
    exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm
  rw [hZ, mem_bot] at hc
  rw [hker]
  exact mem_map_of_mem C.subtype (show c ∈ f.ker from hc)

variable {F : Type*} [Field F]

private theorem commutator_mem_local (W : Submodule F (Vector F))
    (g h : stabilizer W) : ⁅g.val, h.val⁆ ∈ determinantKernel W := by
  refine ⟨⁅g, h⁆, ?_, rfl⟩
  change determinantCharacter W ⁅g, h⁆ = 1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)

variable [Finite F] [CharP F 2] {n : ℕ}

/-- The preimage of the point-parabolic quotient center meets the point local
only in the parabolic two-core. -/
theorem point_separation (hcard : Nat.card F = 2 ^ n) (hn : 1 < n) :
    (pointParabolic (F := F)).coreCenterIn 2 ⊓ pointLocal ≤
      pointParabolic.pCoreIn 2 := by
  apply separation pointParabolic pointLocal pointLocal_le 2 pointQuotient
    pointQuotient_surjective
  · exact pointParabolic_core_map_eq_radical hcard hn
  · exact Theory.PSL2.sl2_center_eq_bot F

/-- The preimage of the plane-parabolic quotient center meets the plane local
only in the parabolic two-core. -/
theorem plane_separation (hcard : Nat.card F = 2 ^ n) (hn : 1 < n) :
    (planeParabolic (F := F)).coreCenterIn 2 ⊓ planeLocal ≤
      planeParabolic.pCoreIn 2 := by
  apply separation planeParabolic planeLocal planeLocal_le 2 Plane.quotientMap
    Plane.quotientMap_surjective
  · exact planeParabolic_core_map_eq_radical hcard hn
  · exact Theory.PSL2.sl2_center_eq_bot F

/-- The long-root scalar torus acts trivially on the point Levi quotient. -/
theorem point_scalar_mem_coreCenter (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)
    (s : Fˣ) : diagonalTorus s 1 ∈ (pointParabolic (F := F)).coreCenterIn 2 := by
  let z : pointParabolic (F := F) :=
    ⟨diagonalTorus s 1, (diagonalTorus_mem_borel s 1).1⟩
  have hz : pointParabolicQuotient z = 1 := by
    apply Subtype.ext
    rw [pointParabolicQuotient_torus]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  apply (mem_coreCenterIn_iff 2 pointParabolic _).mpr
  refine ⟨z.property, ?_⟩
  intro b hb
  let g : pointParabolic (F := F) := ⟨b, hb⟩
  have hc : ⁅z.val, g.val⁆ ∈ pointLocal := commutator_mem_local (point F) z g
  change ⁅z.val, g.val⁆ ∈ (pCore 2 pointParabolic).map pointParabolic.subtype
  rw [pointParabolic_core_map_eq_radical hcard hn]
  refine ⟨⟨⁅z.val, g.val⁆, hc⟩, ?_, rfl⟩
  change pointQuotient ⟨⁅z.val, g.val⁆, hc⟩ = 1
  change pointParabolicQuotient ⁅z, g⁆ = 1
  rw [map_commutatorElement, hz]
  simp

/-- Equal plane coordinates give a scalar Levi action, central modulo the two-core. -/
theorem plane_scalar_mem_coreCenter (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)
    (s : Fˣ) : diagonalTorus s s ∈ (planeParabolic (F := F)).coreCenterIn 2 := by
  let z : planeParabolic (F := F) :=
    ⟨diagonalTorus s s, (diagonalTorus_mem_borel s s).2⟩
  have hz : Plane.upperLeft z = Matrix.scalar (Fin 2) (s : F) := by
    rw [planeUpperLeft_torus, Matrix.scalar_apply]
    congr 1
    funext i
    fin_cases i <;> rfl
  apply (mem_coreCenterIn_iff 2 planeParabolic _).mpr
  refine ⟨z.property, ?_⟩
  intro b hb
  let g : planeParabolic (F := F) := ⟨b, hb⟩
  have hc : ⁅z.val, g.val⁆ ∈ planeLocal := commutator_mem_local (plane F) z g
  change ⁅z.val, g.val⁆ ∈ (pCore 2 planeParabolic).map planeParabolic.subtype
  rw [planeParabolic_core_map_eq_radical hcard hn]
  refine ⟨⟨⁅z.val, g.val⁆, hc⟩, ?_, rfl⟩
  change Plane.quotientMap ⟨⁅z.val, g.val⁆, hc⟩ = 1
  apply Subtype.ext
  change Plane.upperLeft ⁅z, g⁆ = 1
  have hcomm : Plane.upperLeft z * Plane.upperLeft g =
      Plane.upperLeft g * Plane.upperLeft z := by
    rw [hz]
    exact (Matrix.scalar_commute (s : F) (Commute.all _) _).eq
  simp only [commutatorElement_def, map_mul]
  have hzi : Plane.upperLeft z * Plane.upperLeft z⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  rw [hcomm, mul_assoc (Plane.upperLeft g) (Plane.upperLeft z), hzi, mul_one,
    ← map_mul, mul_inv_cancel, map_one]

end Theory.SpecificGroups.SymplecticFour.RootCoreTori
