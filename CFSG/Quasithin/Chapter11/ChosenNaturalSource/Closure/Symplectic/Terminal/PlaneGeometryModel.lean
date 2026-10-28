module
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.Coordinates
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.Action
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.Geometry

/-!
# The two planes in the point-radical calculation

A point-radical element moving the point hyperplane has a nonzero pair of
middle coordinates. An actual SL₂ Levi element sends that pair to (1,0).
The resulting matrix has precisely the standard plane as both fixed space
and displacement image. Elements fixing the hyperplane have displacement
in the point. These identities are used in both orientations of the
crossing argument for the original chosen natural module.

Source: Aschbacher--Smith, 11.5.7, refs/quasithin.pdf, printed p.783.
-/

public noncomputable section
open Matrix
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal.PlaneModel
open Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [CharP F 2]

abbrev radical (u v z : F) : Sp F := (pointRadicalElement u v z).val
abbrev levi (a : Matrix.SpecialLinearGroup (Fin 2) F) : Sp F := (pointLevi a).val

/-- The point-radical matrix in the original hyperbolic coordinates. -/
theorem radical_apply (u v z : F) (x : Vector F) :
    radical u v z • x = Sum.elim ![x (.inl 0) + v*x (.inl 1) + z*x (.inr 0) + u*x (.inr 1),
      x (.inl 1) + u*x (.inr 0)] ![x (.inr 0), v*x (.inr 0) + x (.inr 1)] := by
  ext i
  fin_cases i <;>
    simp [radical, pointRadicalElement, pointRadicalMatrix,
      Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

/-- A noncentral radical element can be aligned by the literal point Levi. -/
theorem align_radical (u v z : F) (hne : u ≠ 0 ∨ v ≠ 0) :
    ∃ a : Matrix.SpecialLinearGroup (Fin 2) F,
      levi a * radical u v z * (levi a)⁻¹ = radical 1 0 z := by
  have hne' : (![u,v] : Fin 2 → F) ≠ 0 := by
    intro h
    exact hne.elim (fun hu => hu (congrFun h 0)) (fun hv => hv (congrFun h 1))
  have he : (Pi.single 0 (1 : F) : Fin 2 → F) ≠ 0 := by
    intro h
    exact one_ne_zero (congrFun h 0)
  obtain ⟨a,ha⟩ := natural_transitive hne' he
  have h0 : a 0 0*u+a 0 1*v=1 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun ha 0
  have h1 : a 1 0*u+a 1 1*v=0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun ha 1
  refine ⟨a, ?_⟩
  have h := congrArg Subtype.val (pointLevi_conj_radical a u v z)
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv,h0,h1] using h

/-- The aligned actor fixes exactly the standard plane. -/
theorem aligned_fixed (z : F) (x : Vector F) :
    radical 1 0 z • x = x ↔ x ∈ plane F := by
  rw [radical_apply]
  constructor
  · intro h
    have h0 : x (.inr 0) = 0 := by
      have := congrFun h (.inl 1)
      simpa using this
    have h1 : x (.inr 1) = 0 := by
      have := congrFun h (.inl 0)
      simpa [h0] using this
    intro i
    fin_cases i <;> assumption
  · intro h
    ext i
    fin_cases i <;> simp [h 0,h 1]

/-- Each vector of the plane is one displacement of the aligned actor. -/
theorem aligned_displacement (z : F) (x : Vector F) (hx : x ∈ plane F) :
    ∃ y : Vector F, radical 1 0 z • y - y = x := by
  refine ⟨Sum.elim ![0,0] ![x (.inl 1),x (.inl 0)-z*x (.inl 1)], ?_⟩
  rw [radical_apply]
  ext i
  fin_cases i <;> simp [hx 0,hx 1]

/-- Central radical elements have displacement in the original point. -/
theorem central_displacement (z : F) (x : Vector F) :
    radical 0 0 z • x - x ∈ point F := by
  rw [radical_apply, mem_point_iff]
  constructor
  · simp
  · intro i
    fin_cases i <;> simp

/-- Fixing the standard point hyperplane detects the central radical. -/
theorem radical_central_of_fixes_three (u v z : F)
    (h : ∀ x : Vector F, x (.inr 0)=0 → radical u v z • x=x) :
    u=0 ∧ v=0 := by
  have hv := congrFun (h (Theory.SpecificGroups.SymplecticFour.e 1) (by simp [Theory.SpecificGroups.SymplecticFour.e])) (.inl 0)
  have hu := congrFun (h (Pi.single (.inr 1) 1) (by simp)) (.inl 0)
  rw [radical_apply] at hu hv
  simpa [Theory.SpecificGroups.SymplecticFour.e] using And.intro hu hv

/-- Central elements fix the point hyperplane pointwise. -/
theorem central_fixes_three (z : F) (x : Vector F) (hx : x (.inr 0)=0) :
    radical 0 0 z • x=x := by
  rw [radical_apply]
  ext i
  fin_cases i <;> simp [hx]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal.PlaneModel
