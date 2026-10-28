module
public import Theory.Representation.BinaryAlternatingSevenCohomology
public import Theory.Representation.FactorDegreeFiltration.FiniteDual
public import Theory.Representation.FirstCohomologyDuality.Indecomposable

/-!
# Central covers of the four-dimensional binary A₇ modules

The contragredient of an irreducible four-dimensional binary A₇ module is
again irreducible of dimension four. Its first cohomology vanishes, so the
fixed kernel of a commutator-generated central cover has dimension zero.
Thus the original covering map is injective, preserving its actor marking.

Source: Aschbacher–Smith, I.1.5–6, printed p.408, applied in 13.7.6(4),
printed p.939 of the combined manuscript of 1 March 2004.
-/

public section
namespace Representation.BinaryAlternatingSevenControl
open OneCohomology
variable {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) W}
  {τ : Representation (ZMod 2) (alternatingGroup (Fin 7)) V}

/-- Every central covering map onto an irreducible four-dimensional binary A₇ module is injective. -/
theorem four_cover_injective [IsIrreducible τ]
    (hd : Module.finrank (ZMod 2) V = 4)
    (p : σ.IntertwiningMap τ) (hp : IsCover p) : Function.Injective p := by
  let : IsIrreducible τ.dual := isIrreducible_dual
  have hH := binaryAlternatingSeven_finrank_H1_eq_zero_of_irreducible_four τ.dual
    (by rw [Subspace.dual_finrank_eq,hd])
  have hk := finrank_ker_le_H1_of_cover p hp
  rw [hH] at hk
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero hk))

end Representation.BinaryAlternatingSevenControl
