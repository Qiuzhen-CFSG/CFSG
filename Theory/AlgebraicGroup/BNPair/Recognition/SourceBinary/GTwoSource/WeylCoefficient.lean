module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.PositiveCoefficients
public import Theory.SpecificGroups.PSL2.SemilinearCoverage.MatrixBasics

/-!
# The short rank-one cubic determines the highest G₂ coefficient

The positive-root calculation in Fong–Seitz II (9.16)–(9.21), printed
pp.216–217, determines the highest FE coefficient by scalar polarization
only for q ≥ 4. Here the actual short SL₂ pinning supplies another argument:
the conjugation action of F(1)s has cube one. Applying that cube to C(1),
and collecting using the lower exchanges, gives A(1+g(1,1))C(1).
Injectivity of A forces g(1,1)=1. The existing torus calculation then
normalizes every coefficient, including in the field of two elements.

The cubic relation is proved in SL₂ and mapped into the same group; it
is not an assumed value of the missing coefficient. The pinning's three
positive-root actions, the lower exchanges and the torus still have to
be constructed from the source (6E)(a) configuration. In particular this
does not use the q ≥ 4 tensor identification in the binary case and does
not claim to complete the source binary reconstruction or Thomas [33].
-/

@[expose] public noncomputable section
open Atlas.G2.RootPresentationRecognition
open Theory.PSL2.SemilinearCoverage
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
variable {K Y : Type*} [Field K] [CharP K 2] [Group Y]

private theorem unit_weyl_cube : (uni (1 : K) * weyl K)^3 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

/-- An actual short SL₂ map, with its simple root and three Weyl actions.
No highest FE coefficient or polynomial FE relation is an input. -/
structure ShortRankOneData (L : PositiveRoots K Y) where
  hom : SL2 K →* Y
  root : ∀ a, hom (uni a) = L.x 5 a
  fixes_highest : ∀ a, MulAut.conj (hom (weyl K)) (L.x 0 a) = L.x 0 a
  long_orbit : ∀ a, MulAut.conj (hom (weyl K)) (L.x 4 a) = L.x 1 a
  middle_orbit : ∀ a, MulAut.conj (hom (weyl K)) (L.x 3 a) = L.x 2 a

namespace ShortRankOneData
variable {L : PositiveRoots K Y} (p : ShortRankOneData L)
/-- The reflection comes from the same rank-one map as the short root. -/
def reflection : Y := p.hom (weyl K)
theorem reflection_sq : p.reflection * p.reflection = 1 := by
  rw [reflection, ← map_mul, weyl_sq, map_one]
theorem reflection_inv : p.reflection⁻¹ = p.reflection :=
  inv_eq_of_mul_eq_one_right p.reflection_sq

theorem conjugate_twice (y : Y) :
    MulAut.conj p.reflection (MulAut.conj p.reflection y) = y := by
  change p.reflection * (p.reflection*y*p.reflection⁻¹)*p.reflection⁻¹ = y
  rw [p.reflection_inv]
  calc
    _ = (p.reflection*p.reflection)*y*(p.reflection*p.reflection) := by group
    _ = y := by rw [p.reflection_sq]; simp

theorem long_orbit_reverse (a : K) :
    MulAut.conj p.reflection (L.x 1 a) = L.x 4 a := by
  rw [← p.long_orbit]
  exact p.conjugate_twice _
theorem middle_orbit_reverse (a : K) :
    MulAut.conj p.reflection (L.x 2 a) = L.x 3 a := by
  rw [← p.middle_orbit]
  exact p.conjugate_twice _

/-- The rank-one cubic holds without any field-size restriction. -/
theorem cubic : (L.x 5 1 * p.reflection)^3 = 1 := by
  rw [← p.root, reflection, ← map_mul, ← map_pow, unit_weyl_cube, map_one]
end ShortRankOneData

namespace PartialPositiveData
variable [Finite K] {L : PositiveRoots K Y} (d : PartialPositiveData L)
  (p : ShortRankOneData L)
  (g : K → K → K)
  (hg : ∀ z e, L.x 5 z * L.x 4 e =
    L.x 0 (g z e) * L.x 1 (e*z^3) * L.x 2 (e*z^2) * L.x 3 (e*z) * L.x 4 e * L.x 5 z)

private theorem append_exchange {a b c : Y} (h : a*b=c) (z : Y) :
    a*(b*z) = c*z := by rw [← mul_assoc, h]

omit [CharP K 2] [Finite K] in
private theorem collect_root (i : Fin 6) (s t : K) (z : Y) :
    L.x i s * (L.x i t * z) = L.x i (s+t)*z := by
  rw [← mul_assoc, ← L.x_add]

include d p hg in
/-- Collect the cube of the actual rank-one actor on the middle root. -/
theorem coefficient_unit : g 1 1 = 1 := by
  let f := MulAut.conj (L.x 5 1)
  let w := MulAut.conj p.reflection
  let t := MulAut.conj (L.x 5 1 * p.reflection)
  have ht (x : Y) : t x = f (w x) := by
    simp only [t, f, w, MulAut.conj_apply, mul_inv_rev]
    group
  have hfa (a : K) : f (L.x 0 a) = L.x 0 a := by
    change L.x 5 1 * L.x 0 a * (L.x 5 1)⁻¹ = _
    rw [d.commuting.fa, mul_assoc, mul_inv_cancel, mul_one]
  have hfb (a : K) : f (L.x 1 a) = L.x 1 a := by
    change L.x 5 1 * L.x 1 a * (L.x 5 1)⁻¹ = _
    rw [d.commuting.fb, mul_assoc, mul_inv_cancel, mul_one]
  have hfc : f (L.x 2 1) = L.x 1 1 * L.x 2 1 := by
    change L.x 5 1 * L.x 2 1 * (L.x 5 1)⁻¹ = _
    rw [d.fc, mul_one, mul_assoc, mul_inv_cancel, mul_one]
  have hfd : f (L.x 3 1) = L.x 0 1 * L.x 1 1 * L.x 3 1 := by
    change L.x 5 1 * L.x 3 1 * (L.x 5 1)⁻¹ = _
    rw [d.fd]
    simp only [one_pow, mul_assoc, mul_inv_cancel, mul_one]
  have hfe : f (L.x 4 1) = L.x 0 (g 1 1) * L.x 1 1 * L.x 2 1 * L.x 3 1 * L.x 4 1 := by
    change L.x 5 1 * L.x 4 1 * (L.x 5 1)⁻¹ = _
    rw [hg]
    simp only [one_pow, mul_assoc, mul_inv_cancel, mul_one]
  have ha (a : K) : t (L.x 0 a) = L.x 0 a := by
    rw [ht, show w (L.x 0 a) = L.x 0 a from p.fixes_highest a, hfa]
  have hb : t (L.x 1 1) = L.x 0 (g 1 1) * L.x 1 1 * L.x 2 1 * L.x 3 1 * L.x 4 1 := by
    rw [ht, show w (L.x 1 1) = L.x 4 1 from p.long_orbit_reverse 1, hfe]
  have hc : t (L.x 2 1) = L.x 0 1 * L.x 1 1 * L.x 3 1 := by
    rw [ht, show w (L.x 2 1) = L.x 3 1 from p.middle_orbit_reverse 1, hfd]
  have hd : t (L.x 3 1) = L.x 1 1 * L.x 2 1 := by
    rw [ht, show w (L.x 3 1) = L.x 2 1 from p.middle_orbit 1, hfc]
  have he : t (L.x 4 1) = L.x 1 1 := by
    rw [ht, show w (L.x 4 1) = L.x 1 1 from p.long_orbit 1, hfb]
  have hcc : t (t (L.x 2 1)) = L.x 0 (1 + g 1 1) * L.x 3 1 * L.x 4 1 := by
    rw [hc, map_mul, map_mul, ha, hb, hd]
    simp only [mul_assoc, append_exchange (d.eb _ _),
      append_exchange (d.commuting.ba _ _),
      append_exchange (d.commuting.da _ _), append_exchange (d.commuting.cb _ _),
      append_exchange (d.commuting.db _ _), d.commuting.ec,
      append_exchange (d.dc _ _), collect_root,
      one_mul, mul_one, CharTwo.add_self_eq_zero, L.x_zero]
  have hccc : t (t (t (L.x 2 1))) = L.x 0 (1 + g 1 1) * L.x 2 1 := by
    rw [hcc, map_mul, map_mul, ha, hd, he]
    simp only [mul_assoc, ← d.commuting.cb 1 1]
    rw [← L.x_add, CharTwo.add_self_eq_zero, L.x_zero, mul_one]
  have hcycle : t (t (t (L.x 2 1))) = L.x 2 1 := by
    change (L.x 5 1*p.reflection)*((L.x 5 1*p.reflection)*
      ((L.x 5 1*p.reflection)*L.x 2 1*(L.x 5 1*p.reflection)⁻¹)*
        (L.x 5 1*p.reflection)⁻¹)*(L.x 5 1*p.reflection)⁻¹ = _
    calc
      _ = (L.x 5 1*p.reflection)^3 * L.x 2 1 * ((L.x 5 1*p.reflection)^3)⁻¹ := by
        simp only [pow_succ, pow_zero, mul_inv_rev]
        group
      _ = L.x 2 1 := by rw [p.cubic]; simp
  have hzero : L.x 0 (1 + g 1 1) = L.x 0 0 := by
    rw [L.x_zero]
    exact mul_right_cancel (hccc.symm.trans hcycle |>.trans (one_mul _).symm)
  have hscalar : 1 + g 1 1 = 0 :=
    Multiplicative.ofAdd.injective (d.A_injective hzero)
  simpa only [CharTwo.neg_eq] using (eq_neg_of_add_eq_zero_right hscalar)
include d p hg in
/-- The short rank-one action forces the missing coefficient in every finite
characteristic-two field, including the binary field. -/
theorem coefficient_of_short_rankOne (z e : K) : g z e = z^3 * e^2 := by
  have hz (b : K) : g 0 b = 0 := by
    simpa using (d.coefficient_add g hg 0 0 b).symm
  rw [g_homogeneous g hz (d.coefficient_zero_right g hg)
    (d.coefficient_scale g hg), d.coefficient_unit p g hg, mul_one]

include d p in
/-- Complete positive relations without a lower bound on the field cardinality. -/
theorem relations_of_short_rankOne : L.CharTwoRelations := by
  classical
  choose g hg using d.fe_mem
  refine ⟨d.commuting, d.dc, d.eb, d.fc, d.fd, ?_⟩
  intro z e
  simpa only [d.coefficient_of_short_rankOne p g hg z e, mul_comm (z^3) (e^2)] using hg z e
end PartialPositiveData
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
