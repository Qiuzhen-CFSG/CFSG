module

public import Theory.Representation.JankoTwo.SixDimensionalCertificate.WeightSpaces
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.CharP.Two

/-!
# Determinant constraints on the Hall--Janko cubic spectra

Restrict the actual centralizer to each eigenspace. A scalar commutator has
scalar determinant one, so its root order divides the eigenspace dimension.
Applied to the checked cubic central commutator, this forces every nontrivial
cubic multiplicity to be divisible by three.

The literal cubic and fifth-order triangle generator restrict to every
x-eigenspace and retain their (3,5,2) relations. Their determinants are one
in characteristic two. The remaining plane calculation and pattern exclusion
are not assumed by these statements.

Source: Aschbacher--Smith K.4.5, printed p.460; Hiss--Malle corrected Table 2.
See ../Source.md for the local spectral argument.
-/

@[expose] public noncomputable section
namespace Representation.JankoTwo.SixDimensionalCertificate.LocalSpectra
open Sporadic.LeechRelated.J2
open scoped commutatorElement
variable {E U G : Type*} [Field E] [Group G] [AddCommGroup U] [Module E U]

/-- The literal centralizer action restricted to an eigenspace. -/
def centralizerEigenspace (ρ : Representation E G U) (g : G) (a : E) :
    Representation E (Subgroup.centralizer {g}) (Module.End.eigenspace (ρ g) a) where
  toFun h := (ρ (h : G)).restrict (by
    intro v hv
    apply Module.End.mem_eigenspace_iff.mpr
    have hh := h.property g (Set.mem_singleton g)
    have hv := Module.End.mem_eigenspace_iff.mp hv
    rw [← Module.End.mul_apply, ← map_mul, hh, map_mul, Module.End.mul_apply, hv, map_smul])
  map_one' := by ext; simp
  map_mul' h k := by ext; simp

/-- A central commutator's scalar eigenvalue has order dividing the eigenspace dimension. -/
theorem central_commutator_eigenvalue_pow_finrank [FiniteDimensional E U]
    (ρ : Representation E G U) (c u v : G)
    (hcu : c * u = u * c) (hcv : c * v = v * c)
    (hc : v * u * v⁻¹ * u⁻¹ = c) (a : E) :
    a ^ Module.finrank E (Module.End.eigenspace (ρ c) a) = 1 := by
  let C := Subgroup.centralizer ({c} : Set G)
  let u' : C := ⟨u, by intro g hg; simpa only [Set.mem_singleton_iff.mp hg] using hcu⟩
  let v' : C := ⟨v, by intro g hg; simpa only [Set.mem_singleton_iff.mp hg] using hcv⟩
  let c' : C := ⟨c, by intro g hg; simp only [Set.mem_singleton_iff.mp hg]⟩
  let σ := centralizerEigenspace ρ c a
  let δ : C →* Eˣ := (LinearMap.det.comp σ).toHomUnits
  have he : ⁅v', u'⁆ = c' := by
    apply Subtype.ext
    exact hc
  have hd : δ c' = 1 := by
    rw [← he, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  have hscalar : σ c' = a • LinearMap.id := by
    ext w
    exact Module.End.mem_eigenspace_iff.mp w.property
  have hd' := congrArg (fun z : Eˣ => (z : E)) hd
  change LinearMap.det (σ c') = 1 at hd'
  simpa only [hscalar, LinearMap.det_smul, LinearMap.det_id, mul_one] using hd'

/-- The checked J₂ central commutator forces cubic multiplicities to be divisible by three. -/
theorem three_dvd_cubicMultiplicity [FiniteDimensional E U]
    (ρ : Representation E Carrier U) {a : E} (ha : IsPrimitiveRoot a 3) :
    3 ∣ Module.finrank E (Module.End.eigenspace (ρ TraceGeometry.c) a) := by
  apply (ha.pow_eq_one_iff_dvd _).mp
  exact central_commutator_eigenvalue_pow_finrank ρ
    TraceGeometry.c TraceGeometry.u TraceGeometry.v
    TraceGeometry.c_u_commute TraceGeometry.c_v_commute TraceGeometry.central_commutator a

/-- The (3,5,2) triangle relations give determinant one in characteristic two. -/
theorem triangle_determinants [CharP E 2]
    (A B : Module.End E U) (hA : A ^ 3 = 1) (hB : B ^ 5 = 1)
    (hAB : (A * B) ^ 2 = 1) : LinearMap.det A = 1 ∧ LinearMap.det B = 1 := by
  let a := LinearMap.det A
  let b := LinearMap.det B
  have ha : a ^ 3 = 1 := by simpa only [map_pow, map_one] using congrArg LinearMap.det hA
  have hb : b ^ 5 = 1 := by simpa only [map_pow, map_one] using congrArg LinearMap.det hB
  have habsq : (a * b) ^ 2 = 1 := by
    simpa only [map_pow, map_mul, map_one] using congrArg LinearMap.det hAB
  have hab : a * b = 1 := by
    rcases (sq_eq_one_iff).mp habsq with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  have ha5 : a ^ 5 = 1 := by
    have hh := congrArg (fun z : E => z ^ 5) hab
    simpa only [mul_pow, hb, mul_one, one_pow] using hh
  have ha1 : a = 1 := by
    have hh := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ha) (orderOf_dvd_of_pow_eq_one ha5)
    norm_num at hh
    exact hh
  exact ⟨ha1, by simpa only [ha1, one_mul] using hab⟩

/-- The checked cubic, regarded as an element of the centralizer of x. -/
def xCentralizerC : Subgroup.centralizer ({TraceGeometry.x} : Set Carrier) :=
  ⟨TraceGeometry.c, by
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    exact TraceGeometry.c_x_commute.symm⟩

/-- The checked fifth-order word d also centralizes x. -/
def xCentralizerD : Subgroup.centralizer ({TraceGeometry.x} : Set Carrier) :=
  ⟨TraceGeometry.d, by
    intro g hg
    rw [Set.mem_singleton_iff.mp hg, TraceGeometry.d_eq]
    have h : Commute TraceGeometry.x (TraceGeometry.y⁻¹ ^ 2) :=
      (show Commute TraceGeometry.x TraceGeometry.y from TraceGeometry.x_y_commute).inv_right.pow_right 2
    rw [mul_assoc, h.eq, ← mul_assoc]⟩

/-- Restriction of the literal cubic to an x-eigenspace. -/
def cOnXEigenspace (ρ : Representation E Carrier U) (a : E) :
    Module.End E (Module.End.eigenspace (ρ TraceGeometry.x) a) :=
  centralizerEigenspace ρ TraceGeometry.x a xCentralizerC

/-- Restriction of the literal fifth-order word to an x-eigenspace. -/
def dOnXEigenspace (ρ : Representation E Carrier U) (a : E) :
    Module.End E (Module.End.eigenspace (ρ TraceGeometry.x) a) :=
  centralizerEigenspace ρ TraceGeometry.x a xCentralizerD

@[simp] theorem cOnXEigenspace_apply (ρ : Representation E Carrier U) (a : E)
    (v : Module.End.eigenspace (ρ TraceGeometry.x) a) :
    (cOnXEigenspace ρ a v : U) = ρ TraceGeometry.c v := rfl

@[simp] theorem dOnXEigenspace_apply (ρ : Representation E Carrier U) (a : E)
    (v : Module.End.eigenspace (ρ TraceGeometry.x) a) :
    (dOnXEigenspace ρ a v : U) = ρ TraceGeometry.d v := rfl

/-- The triangle relations hold on every actual x-eigenspace. -/
theorem xEigenspace_triangle_relations (ρ : Representation E Carrier U) (a : E) :
    cOnXEigenspace ρ a ^ 3 = 1 ∧ dOnXEigenspace ρ a ^ 5 = 1 ∧
      (cOnXEigenspace ρ a * dOnXEigenspace ρ a) ^ 2 = 1 := by
  let σ := centralizerEigenspace ρ TraceGeometry.x a
  have hc : xCentralizerC ^ 3 = 1 := Subtype.ext TraceGeometry.c_pow_three
  have hd : xCentralizerD ^ 5 = 1 := Subtype.ext TraceGeometry.d_pow_five
  have hcd : (xCentralizerC * xCentralizerD) ^ 2 = 1 :=
    Subtype.ext TraceGeometry.cd_pow_two
  refine ⟨?_, ?_, ?_⟩
  · change σ xCentralizerC ^ 3 = 1
    rw [← map_pow, hc, map_one]
  · change σ xCentralizerD ^ 5 = 1
    rw [← map_pow, hd, map_one]
  · change (σ xCentralizerC * σ xCentralizerD) ^ 2 = 1
    rw [← map_mul, ← map_pow, hcd, map_one]

/-- The actual restricted cubic and fifth-order operators have determinant one. -/
theorem xEigenspace_triangle_determinants [CharP E 2]
    (ρ : Representation E Carrier U) (a : E) :
    LinearMap.det (cOnXEigenspace ρ a) = 1 ∧ LinearMap.det (dOnXEigenspace ρ a) = 1 := by
  obtain ⟨hc, hd, hcd⟩ := xEigenspace_triangle_relations ρ a
  exact triangle_determinants _ _ hc hd hcd

end Representation.JankoTwo.SixDimensionalCertificate.LocalSpectra
