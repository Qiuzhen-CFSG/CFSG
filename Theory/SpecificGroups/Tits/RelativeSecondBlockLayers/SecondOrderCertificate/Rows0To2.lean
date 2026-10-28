module

public import Theory.SpecificGroups.Tits.RelativeSecondBlockLayers.SecondOrderCertificate.Data

/-!
# Second-parabolic coset transitions, rows 0 through 2

These kernel-checked word equalities supply part of the three-coset cover.
The table conventions and Parrott source are documented in `Data`.
Independent rows are separated to bound compilation cost and cache completed checks.
-/

@[expose] public section
namespace Tits.RelativeSecondBlockLayers.SecondOrder
open Atlas1600OrderCertificate

private theorem val_mul (a b : Atlas1600Group) : (a*b).val = a.val*b.val := rfl
private theorem val_pow (a : Atlas1600Group) (n : ℕ) : (a^n).val = a.val^n := rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem step_0 (i : Fin 3) :
    rep i * generator 0 = atlas1600SylowTwoNormalForm (factor 0 i) * rep (dest 0 i) := by
  apply Subtype.ext
  simp only [rep, generator, val_mul, val_pow,
    atlas1600ParrottAssignment_val, atlas1600SylowTwoNormalForm_val]
  apply Equiv.ext
  revert i
  apply allFin₂
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem step_1 (i : Fin 3) :
    rep i * generator 1 = atlas1600SylowTwoNormalForm (factor 1 i) * rep (dest 1 i) := by
  apply Subtype.ext
  simp only [rep, generator, val_mul, val_pow,
    atlas1600ParrottAssignment_val, atlas1600SylowTwoNormalForm_val]
  apply Equiv.ext
  revert i
  apply allFin₂
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem step_2 (i : Fin 3) :
    rep i * generator 2 = atlas1600SylowTwoNormalForm (factor 2 i) * rep (dest 2 i) := by
  apply Subtype.ext
  simp only [rep, generator, val_mul, val_pow,
    atlas1600ParrottAssignment_val, atlas1600SylowTwoNormalForm_val]
  apply Equiv.ext
  revert i
  apply allFin₂
  decide +kernel


end Tits.RelativeSecondBlockLayers.SecondOrder
