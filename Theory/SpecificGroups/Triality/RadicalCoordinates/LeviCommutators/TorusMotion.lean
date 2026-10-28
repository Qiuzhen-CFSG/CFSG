module

public import Theory.SpecificGroups.Triality.RadicalCoordinates.LeviCommutators.Motion
public import Theory.SpecificGroups.Triality.RadicalCoordinates.LeviCommutators.TorusMotion.Weights

/-!
# Nontrivial Levi torus motion on the triality radical factors

For q > 2, both supported short roots for the arms torus and the first two
short roots for the central torus admit a nontrivial scalar action. A
nonidentity fixed-field unit supplies all these witnesses and the central
long-root witnesses. A cubic-field unit with nonidentity norm supplies the
arms long-root witnesses, including q = 4 where fixed-field units alone
would have trivial cubic norm.

The four families discharge the exact motion predicates used by the
radical commutator assembly. Each contains an actual torus parameter and
the split Geck conjugation equation for every root parameter.

Sources: GLS3 §§2.4 and 2.6 (`refs/KGroup/GLS3/chapter2.tex`);
Aschbacher–Smith F.1.12(II), printed pp.263–264 (`refs/quasithin.pdf`).
-/

public section
noncomputable section
namespace Triality.Standard.RadicalCoordinates.LeviCommutators
open ConcreteBruhat.TorusCoordinates

/-- The arms torus moves both supported short root groups when q > 2. -/
theorem shortTorusMotion_arms (P : Parameters) (hp : P.prime = 2) (hq : 2 < P.q)
    (i : Fin 3) (hi : i ≠ 0) : ShortTorusMotion P hp .arms i := by
  obtain ⟨t, ht⟩ := exists_fixedUnit_ne_one P hq
  have htval : t.val.val ≠ 1 := fun he => ht (Subtype.ext he)
  have htzero : t.val.val ≠ 0 := (fixedUnit P t).ne_zero
  have hfix : fieldFrobenius P t.val.val = t.val.val := t.val.property
  fin_cases i
  · exact (hi rfl).elim
  · refine ⟨fixedUnit P t, t.val.val⁻¹, inv_ne_one.mpr htval, ?_⟩
    intro u
    simpa [fixedUnit, hfix, -fieldFrobenius_apply, div_mul_eq_div_div, htzero] using
      torus_arms_short_one_conjugate P hp (fixedUnit P t) u
  · refine ⟨fixedUnit P t, t.val.val, htval, ?_⟩
    intro u
    simpa [fixedUnit, hfix, -fieldFrobenius_apply, htzero] using
      torus_arms_short_two_conjugate P hp (fixedUnit P t) u

/-- A unit with nonidentity cubic norm moves the first two long root groups. -/
theorem longTorusMotion_arms (P : Parameters) (hp : P.prime = 2) (hq : 2 < P.q)
    (i : Fin 3) (hi : i ≠ 2) : LongTorusMotion P hp .arms i := by
  obtain ⟨t, ht⟩ := exists_cubicNorm_ne_one P hq
  fin_cases i
  · exact ⟨t, (cubicNorm P t.val)⁻¹, inv_ne_one.mpr ht, torus_arms_long_zero_conjugate P hp t⟩
  · exact ⟨t, cubicNorm P t.val, ht, torus_arms_long_one_conjugate P hp t⟩
  · exact (hi rfl).elim

/-- The central torus moves the first two short root groups. -/
theorem shortTorusMotion_central (P : Parameters) (hp : P.prime = 2) (hq : 2 < P.q)
    (i : Fin 3) (hi : i ≠ 2) : ShortTorusMotion P hp .central i := by
  obtain ⟨t, ht⟩ := exists_fixedUnit_ne_one P hq
  have htval : t.val.val ≠ 1 := fun he => ht (Subtype.ext he)
  fin_cases i
  · exact ⟨t, t.val.val⁻¹, inv_ne_one.mpr htval, torus_central_short_zero_conjugate P hp t⟩
  · exact ⟨t, t.val.val, htval, torus_central_short_one_conjugate P hp t⟩
  · exact (hi rfl).elim

/-- The central torus moves both supported long root groups. -/
theorem longTorusMotion_central (P : Parameters) (hp : P.prime = 2) (hq : 2 < P.q)
    (i : Fin 3) (hi : i ≠ 0) : LongTorusMotion P hp .central i := by
  obtain ⟨t, ht⟩ := exists_fixedUnit_ne_one P hq
  fin_cases i
  · exact (hi rfl).elim
  · exact ⟨t, t.val⁻¹, inv_ne_one.mpr ht, torus_central_long_one_conjugate P hp t⟩
  · exact ⟨t, t.val, ht, torus_central_long_two_conjugate P hp t⟩
end Triality.Standard.RadicalCoordinates.LeviCommutators
