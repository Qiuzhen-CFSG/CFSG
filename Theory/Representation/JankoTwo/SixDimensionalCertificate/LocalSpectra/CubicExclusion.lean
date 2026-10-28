module

public import Theory.Representation.JankoTwo.SixDimensionalCertificate.LocalSpectra.CubicExclusion.XSpaces
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Excluding two Hall–Janko weight patterns and computing mixed traces

The actual x-planes each contribute one copy of each nonidentity cubic
eigenvalue; x-lines contribute none. Decomposing the ambient c-eigenspace by x
therefore gives multiplicities three, three, two and two for the four patterns.
The checked scalar-commutator determinant constraint excludes the latter pair.
The trace on each surviving plane is one, giving the stated traces of c*x^j.

The weight-pattern hypothesis is explicit. Its unconditional construction and
final trace-rigidity assembly belong to `LocalSpectra`; no representation
catalogue or spectral conclusion is assumed here.

Source: Aschbacher–Smith K.4.5, printed p.460; Hiss–Malle corrected Table 2,
the characteristic-two degree-six J₂ entry. See ../Source.md.
-/

@[expose] public noncomputable section
open Module Sporadic.LeechRelated.J2
open scoped DirectSum BigOperators
namespace Representation.JankoTwo.SixDimensionalCertificate.LocalSpectra.CubicExclusion
variable {E U : Type*} [Field E] [AddCommGroup U] [Module E U]

private lemma cubic_multiplicity_sum [FiniteDimensional E U] [IsAlgClosed E] [CharP E 2]
    (ρ : Representation E Carrier U) {ζ : E} (hζ : IsPrimitiveRoot ζ 5) (a : E) :
    Module.finrank E (Module.End.eigenspace (ρ TraceGeometry.c) a) = ∑ e : Fin 5,
      Module.finrank E ((cOnXEigenspace ρ (ζ ^ e.val)).eigenspace a) := by
  have hc : Commute (ρ TraceGeometry.x) (ρ TraceGeometry.c) := by
    change ρ TraceGeometry.x * ρ TraceGeometry.c = ρ TraceGeometry.c * ρ TraceGeometry.x
    rw [← map_mul, ← map_mul, TraceGeometry.c_x_commute]
  have hp : ∀ v ∈ Module.End.eigenspace (ρ TraceGeometry.c) a,
      ρ TraceGeometry.x v ∈ Module.End.eigenspace (ρ TraceGeometry.c) a :=
    by
      intro v hv
      apply Module.End.mem_eigenspace_iff.mpr
      have hh := Module.End.mem_eigenspace_iff.mp hv
      rw [← Module.End.mul_apply, hc.symm.eq, Module.End.mul_apply, hh, map_smul]
  rw [finrank_invariant_eq_sum (ρ TraceGeometry.x)
    ((CharP.cast_eq_zero_iff E 2 5).not.mpr (by decide))
    (by rw [← map_pow, TraceGeometry.x_pow_five, map_one]) hζ _ hp]
  apply Finset.sum_congr rfl
  intro e _
  have he := finrank_restrict_eigenspace (ρ TraceGeometry.c)
    (Module.End.eigenspace (ρ TraceGeometry.x) (ζ ^ e.val))
    (fun v hv => (centralizerEigenspace ρ TraceGeometry.x (ζ ^ e.val) xCentralizerC ⟨v, hv⟩).property) a
  change Module.finrank E ((cOnXEigenspace ρ (ζ ^ e.val)).eigenspace a) = _ at he
  rw [he, inf_comm]

private lemma cubic_multiplicity_on_x [FiniteDimensional E U] [IsAlgClosed E] [CharP E 2]
    (ρ : Representation E Carrier U) {ζ : E} (hζ : IsPrimitiveRoot ζ 5)
    (i : Fin 4) (hi : ∀ w, weightMultiplicity ρ ζ w = Weights.pattern i w)
    (e : Fin 5) {a : E} (ha : IsPrimitiveRoot a 3) :
    Module.finrank E ((cOnXEigenspace ρ (ζ ^ e.val)).eigenspace a) =
      if Weights.xMultiplicity i (e.val : ZMod 5) = 2 then 1 else 0 := by
  have hd := x_space_dimension ρ hζ i hi e
  by_cases h2 : Weights.xMultiplicity i (e.val : ZMod 5) = 2
  · rw [if_pos h2]
    exact (cubic_plane _ (hd.trans h2)
      (xEigenspace_triangle_relations ρ _).1
      (xEigenspace_triangle_determinants ρ _).1
      (c_on_plane_ne_one ρ hζ i hi e h2) ha).1
  rw [if_neg h2]
  have hle := (by decide +kernel : ∀ (i : Fin 4) (e : Fin 5),
    Weights.xMultiplicity i (e.val : ZMod 5) ≤ 2) i e
  by_cases h0 : Weights.xMultiplicity i (e.val : ZMod 5) = 0
  · have hh := Submodule.finrank_le ((cOnXEigenspace ρ (ζ ^ e.val)).eigenspace a)
    omega
  have h1 : Weights.xMultiplicity i (e.val : ZMod 5) = 1 := by omega
  rw [c_on_line ρ hζ i hi e h1, eigenspace_one_nonidentity a (ha.ne_one (by decide)),
    finrank_bot]

/-- The actual nonidentity cubic eigenspaces have dimension three in the first
pair of patterns, and two in the second pair. -/
lemma cubic_multiplicity_of_pattern [FiniteDimensional E U] [IsAlgClosed E] [CharP E 2]
    (ρ : Representation E Carrier U) {ζ : E} (hζ : IsPrimitiveRoot ζ 5)
    (i : Fin 4) (hi : ∀ w, weightMultiplicity ρ ζ w = Weights.pattern i w)
    {a : E} (ha : IsPrimitiveRoot a 3) :
    Module.finrank E (Module.End.eigenspace (ρ TraceGeometry.c) a) =
      if i = 0 ∨ i = 1 then 3 else 2 := by
  rw [cubic_multiplicity_sum ρ hζ]
  simp_rw [cubic_multiplicity_on_x ρ hζ i hi _ ha]
  exact (by decide +kernel : ∀ i : Fin 4,
    (∑ e : Fin 5, if Weights.xMultiplicity i (e.val : ZMod 5) = 2 then 1 else 0) =
      if i = 0 ∨ i = 1 then 3 else 2) i

/-- The scalar-commutator determinant constraint excludes patterns two and three. -/
theorem pattern_zero_or_one [FiniteDimensional E U] [IsAlgClosed E] [CharP E 2]
    (ρ : Representation E Carrier U) {ζ : E} (hζ : IsPrimitiveRoot ζ 5)
    (i : Fin 4) (hi : ∀ w, weightMultiplicity ρ ζ w = Weights.pattern i w) :
    i = 0 ∨ i = 1 := by
  let : NeZero (3 : E) := ⟨(CharP.cast_eq_zero_iff E 2 3).not.mpr (by decide)⟩
  obtain ⟨a, ha⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot E 3
  have hd := three_dvd_cubicMultiplicity ρ ha
  rw [cubic_multiplicity_of_pattern ρ hζ i hi ha] at hd
  by_contra h
  rw [if_neg h] at hd
  norm_num at hd

private lemma trace_c_on_x_plane [FiniteDimensional E U] [IsAlgClosed E] [CharP E 2]
    (ρ : Representation E Carrier U) {ζ : E} (hζ : IsPrimitiveRoot ζ 5)
    (i : Fin 4) (hi : ∀ w, weightMultiplicity ρ ζ w = Weights.pattern i w)
    (e : Fin 5) (hdim : Weights.xMultiplicity i (e.val : ZMod 5) = 2) :
    LinearMap.trace E _ (cOnXEigenspace ρ (ζ ^ e.val)) = 1 := by
  let : NeZero (3 : E) := ⟨(CharP.cast_eq_zero_iff E 2 3).not.mpr (by decide)⟩
  obtain ⟨a, ha⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot E 3
  exact (cubic_plane _ ((x_space_dimension ρ hζ i hi e).trans hdim)
    (xEigenspace_triangle_relations ρ _).1
    (xEigenspace_triangle_determinants ρ _).1
    (c_on_plane_ne_one ρ hζ i hi e hdim) ha).2.2

private lemma mixed_trace_sum [FiniteDimensional E U] [IsAlgClosed E] [CharP E 2]
    (ρ : Representation E Carrier U) {ζ : E} (hζ : IsPrimitiveRoot ζ 5) (j : ℕ) :
    ρ.character (TraceGeometry.c * TraceGeometry.x ^ j) =
      ∑ e : Fin 5, ζ ^ (e.val * j) * LinearMap.trace E _ (cOnXEigenspace ρ (ζ ^ e.val)) := by
  classical
  have hx (e : Fin 5) (v : Module.End.eigenspace (ρ TraceGeometry.x) (ζ ^ e.val)) :
      ρ (TraceGeometry.x ^ j) v.val = ζ ^ (e.val * j) • v.val := by
    rw [map_pow]
    have hev : (ρ TraceGeometry.x) v.val = ζ ^ e.val • v.val :=
      Module.End.mem_eigenspace_iff.mp v.property
    have hh (n : ℕ) : ((ρ TraceGeometry.x) ^ n) v.val = (ζ ^ e.val) ^ n • v.val := by
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hev,
          smul_smul, pow_succ]
    simpa only [pow_mul] using hh j
  let f := ρ (TraceGeometry.c * TraceGeometry.x ^ j)
  have hf (e : Fin 5) : Set.MapsTo f (Module.End.eigenspace (ρ TraceGeometry.x) (ζ ^ e.val))
      (Module.End.eigenspace (ρ TraceGeometry.x) (ζ ^ e.val)) := by
    intro v hv
    change ρ (TraceGeometry.c * TraceGeometry.x ^ j) v ∈ _
    rw [map_mul, Module.End.mul_apply, hx e ⟨v, hv⟩, map_smul]
    exact (Module.End.eigenspace (ρ TraceGeometry.x) (ζ ^ e.val)).smul_mem _
      (cOnXEigenspace ρ (ζ ^ e.val) ⟨v, hv⟩).property
  change LinearMap.trace E U f = _
  rw [LinearMap.trace_eq_sum_trace_restrict (x_spaces_internal ρ hζ) hf]
  apply Finset.sum_congr rfl
  intro e _
  have he : f.restrict (hf e) = ζ ^ (e.val * j) • cOnXEigenspace ρ (ζ ^ e.val) := by
    ext v
    change ρ (TraceGeometry.c * TraceGeometry.x ^ j) v.val = _
    rw [map_mul, Module.End.mul_apply, hx, map_smul]
    rfl
  rw [he, map_smul, smul_eq_mul]

private lemma trace_c_on_x [FiniteDimensional E U] [IsAlgClosed E] [CharP E 2]
    (ρ : Representation E Carrier U) {ζ : E} (hζ : IsPrimitiveRoot ζ 5)
    (i : Fin 4) (hi : ∀ w, weightMultiplicity ρ ζ w = Weights.pattern i w)
    (e : Fin 5) :
    LinearMap.trace E _ (cOnXEigenspace ρ (ζ ^ e.val)) =
      if Weights.xMultiplicity i (e.val : ZMod 5) = 0 then 0 else 1 := by
  have hd := x_space_dimension ρ hζ i hi e
  by_cases h0 : Weights.xMultiplicity i (e.val : ZMod 5) = 0
  · rw [if_pos h0]
    have := (Module.finrank_zero_iff).mp (hd.trans h0)
    have he : cOnXEigenspace ρ (ζ ^ e.val) = 0 := Subsingleton.elim _ _
    rw [he, map_zero]
  rw [if_neg h0]
  have hle := (by decide +kernel : ∀ (i : Fin 4) (e : Fin 5),
    Weights.xMultiplicity i (e.val : ZMod 5) ≤ 2) i e
  by_cases h1 : Weights.xMultiplicity i (e.val : ZMod 5) = 1
  · rw [c_on_line ρ hζ i hi e h1]
    change LinearMap.trace E _ LinearMap.id = 1
    rw [LinearMap.trace_id, hd, h1, Nat.cast_one]
  exact trace_c_on_x_plane ρ hζ i hi e (by omega)

/-- Literal mixed traces for the first surviving weight orbit. -/
theorem character_c_mul_x_pow_of_pattern_zero
    [FiniteDimensional E U] [IsAlgClosed E] [CharP E 2]
    (ρ : Representation E Carrier U) {ζ : E} (hζ : IsPrimitiveRoot ζ 5)
    (hi : ∀ w, weightMultiplicity ρ ζ w = Weights.pattern 0 w) (j : ℕ) :
    ρ.character (TraceGeometry.c * TraceGeometry.x ^ j) =
      1 + ζ ^ j + ζ ^ (4 * j) := by
  rw [mixed_trace_sum ρ hζ]
  simp_rw [trace_c_on_x ρ hζ 0 hi]
  simp_rw [show ∀ e : Fin 5, Weights.xMultiplicity 0 (e.val : ZMod 5) =
    (![2,2,0,0,2] : Fin 5 → ℕ) e from fun e => congrFun (Weights.xMultiplicity_values 0) e]
  simp [Fin.sum_univ_succ, add_assoc]

/-- Literal mixed traces for the second surviving weight orbit. -/
theorem character_c_mul_x_pow_of_pattern_one
    [FiniteDimensional E U] [IsAlgClosed E] [CharP E 2]
    (ρ : Representation E Carrier U) {ζ : E} (hζ : IsPrimitiveRoot ζ 5)
    (hi : ∀ w, weightMultiplicity ρ ζ w = Weights.pattern 1 w) (j : ℕ) :
    ρ.character (TraceGeometry.c * TraceGeometry.x ^ j) =
      1 + ζ ^ (2 * j) + ζ ^ (3 * j) := by
  rw [mixed_trace_sum ρ hζ]
  simp_rw [trace_c_on_x ρ hζ 1 hi]
  simp_rw [show ∀ e : Fin 5, Weights.xMultiplicity 1 (e.val : ZMod 5) =
    (![2,0,2,2,0] : Fin 5 → ℕ) e from fun e => congrFun (Weights.xMultiplicity_values 1) e]
  simp [Fin.sum_univ_succ, add_assoc]


end Representation.JankoTwo.SixDimensionalCertificate.LocalSpectra.CubicExclusion
