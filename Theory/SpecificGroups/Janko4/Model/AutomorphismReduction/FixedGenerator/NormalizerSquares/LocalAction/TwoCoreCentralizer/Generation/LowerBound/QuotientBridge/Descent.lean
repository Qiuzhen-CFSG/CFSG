module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.QuotientModel

/-!
# Descent of a finite matrix group to a row subquotient

A row embedding with a right inverse gives unique coordinates on an invariant
subspace. A projection with a section then gives coordinates on its quotient.
The intertwining equations force the extracted matrices to multiply. In a
finite group the monoid and group closures agree, so generator certificates
suffice, including for inverse words. Units are recovered from the resulting
homomorphism on the source group, without assuming inverses for the witnesses.

This elementary matrix argument is used for the unchanged ATLAS max2 subgroup;
see `TwoCoreCentralizer/source/J4G1-max2W1` and GLS3 Table 5.3i, printed p.270.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound.QuotientBridge

structure Coordinates (n m k : ℕ) where
  basis : Matrix (Fin m) (Fin n) (ZMod 2)
  retract : Matrix (Fin n) (Fin m) (ZMod 2)
  project : Matrix (Fin m) (Fin k) (ZMod 2)
  section_ : Matrix (Fin k) (Fin m) (ZMod 2)
  basis_retract : basis * retract = 1
  section_project : section_ * project = 1

namespace Coordinates
variable {n m k : ℕ} (d : Coordinates n m k)

def Realizes (g : Matrix (Fin n) (Fin n) (ZMod 2))
    (q : Matrix (Fin k) (Fin k) (ZMod 2)) : Prop :=
  ∃ a : Matrix (Fin m) (Fin m) (ZMod 2),
    d.basis * g = a * d.basis ∧ a * d.project = d.project * q

def extract (g : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Matrix (Fin k) (Fin k) (ZMod 2) :=
  d.section_ * (d.basis * g * d.retract) * d.project

theorem extract_eq {g q} (h : d.Realizes g q) : d.extract g = q := by
  obtain ⟨a, ha, hq⟩ := h
  unfold extract
  rw [ha, Matrix.mul_assoc a, d.basis_retract, Matrix.mul_one,
    Matrix.mul_assoc, hq, ← Matrix.mul_assoc, d.section_project, Matrix.one_mul]

theorem realizes_one : d.Realizes 1 1 := by
  exact ⟨1, by simp, by simp⟩

theorem realizes_mul {g h q r} (hg : d.Realizes g q) (hh : d.Realizes h r) :
    d.Realizes (g * h) (q * r) := by
  obtain ⟨a, ha, hq⟩ := hg
  obtain ⟨b, hb, hr⟩ := hh
  refine ⟨a * b, ?_, ?_⟩
  · rw [← Matrix.mul_assoc, ha, Matrix.mul_assoc, hb, Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, hr, ← Matrix.mul_assoc, hq, Matrix.mul_assoc]

variable {G : Type*} [Group G] [Finite G]
variable (ρ : G →* Matrix (Fin n) (Fin n) (ZMod 2)) (s : Set G)
variable (hs : ∀ g ∈ s, ∃ q, d.Realizes (ρ g) q)

include hs in
theorem exists_realizes (g : Subgroup.closure s) : ∃ q, d.Realizes (ρ g) q := by
  have hg : (g : G) ∈ Submonoid.closure s := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact g.property
  refine Submonoid.closure_induction
    (motive := fun x _ => ∃ q, d.Realizes (ρ x) q) hs ?_ ?_ hg
  · exact ⟨1, by simpa only [map_one] using d.realizes_one⟩
  · intro x y _ _ hx hy
    obtain ⟨q, hq⟩ := hx
    obtain ⟨r, hr⟩ := hy
    exact ⟨q * r, by simpa only [map_mul] using d.realizes_mul hq hr⟩

def hom : Subgroup.closure s →* Matrix (Fin k) (Fin k) (ZMod 2) where
  toFun g := d.extract (ρ g)
  map_one' := by simpa only [OneMemClass.coe_one, map_one] using d.extract_eq d.realizes_one
  map_mul' g h := by
    obtain ⟨q, hq⟩ := d.exists_realizes ρ s hs g
    obtain ⟨r, hr⟩ := d.exists_realizes ρ s hs h
    change d.extract (ρ ((g : G) * h)) = d.extract (ρ g) * d.extract (ρ h)
    rw [map_mul, d.extract_eq hq, d.extract_eq hr]
    exact d.extract_eq (d.realizes_mul hq hr)

theorem hom_eq (g : Subgroup.closure s) (q) (h : d.Realizes (ρ g) q) :
    d.hom ρ s hs g = q := d.extract_eq h

end Coordinates
end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound.QuotientBridge
