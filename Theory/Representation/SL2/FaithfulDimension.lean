module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Theory.Representation.ScalarDescent
public import Theory.Representation.InvariantsBaseChange
public import Theory.Representation.SL2.LowDegreeIrreducible
public import Theory.Representation.SL2.FaithfulCompositionFactor
public import Theory.Representation.SL2.MinimalSchurDegree
public import Theory.Representation.SL2.SylowFixedDimension

/-!
# Faithful Defining-Characteristic Representations of SL2

For an odd prime p and m positive, every faithful finite-dimensional
GF(p)-representation of SL2(p^m) has dimension at least 2m. If its dimension
is 2m, then the subspace fixed by any Sylow p-subgroup has dimension m.
These are both assertions of Alperin--Brauer--Gorenstein II.4, Lemma 18,
article pp. 45--46, without an extra irreducibility hypothesis.

A faithful irreducible subrepresentation exists by the central-involution
argument. The proved Fong--Wong (1E) bound gives its dimension at least 2m,
hence the same bound for the original space. At equality this subrepresentation
is the whole space. Its actual Schur field has degree m by minimal-orbit
arithmetic. Over that field, extension to an algebraic closure and the actual
highest-weight classification give a one-dimensional Sylow fixed space.
Modular invariant base change and restriction of scalars yield dimension m
over GF(p).

The earlier conditional classification interface and generic invariant
base-change reexports are retained for compatibility. The two unconditional
theorems below use the proved representation and descent results directly.
-/

namespace Representation

namespace SL2

universe u

/-- The low-degree faithful consequence invoked in the proof of ABG II.4,
Lemma 18(i): a faithful `GF(p)`-representation of dimension at most `2m` has
dimension exactly `2m`. -/
@[expose] public def LowDegreeFaithfulClassification (p m : ℕ)
    [Fact p.Prime] : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module (ZMod p) V]
      [FiniteDimensional (ZMod p) V]
      (rho : Representation (ZMod p)
        (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p m)) V),
    Function.Injective rho → Module.finrank (ZMod p) V ≤ 2 * m →
      Module.finrank (ZMod p) V = 2 * m

/-- The low-degree classification consequence gives the dimension inequality
in ABG II.4, Lemma 18(i). -/
public theorem sl2_faithful_finrank_bound_of_lowDegreeClassification
    {p m : ℕ} [Fact p.Prime] (_hpodd : Odd p) (_hm : m ≠ 0)
    (hclassification : LowDegreeFaithfulClassification.{u} p m)
    {V : Type u} [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V]
    (rho : Representation (ZMod p)
      (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p m)) V)
    (hrho : Function.Injective rho) :
    2 * m ≤ Module.finrank (ZMod p) V := by
  by_contra hbound
  have hsmall : Module.finrank (ZMod p) V ≤ 2 * m :=
    Nat.le_of_lt (Nat.lt_of_not_ge hbound)
  have heq := hclassification rho hrho hsmall
  omega


public theorem sl2_faithful_finrank_bound
    {p m : ℕ} [Fact p.Prime] (hp : Odd p) (hm : m ≠ 0)
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (ρ : Representation (ZMod p)
      (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p m)) V)
    (hρ : Function.Injective ρ) : 2*m ≤ Module.finrank (ZMod p) V := by
  obtain ⟨W, hI, hfaithful, hdim⟩ :=
    exists_faithful_irreducible_factor_of_sl2_faithful hp hm ρ hρ
  let : W.toRepresentation.IsIrreducible := hI
  have hW : 2*m ≤ Module.finrank (ZMod p) W.toSubmodule := by
    rcases sl2_faithful_irreducible_finrank_trichotomy hp hm
      W.toRepresentation hfaithful with h | ⟨h, _⟩ | h <;> omega
  exact hW.trans hdim

private theorem isIrreducible_of_minimal
    {p m : ℕ} [Fact p.Prime] (hp : Odd p) (hm : m ≠ 0)
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (ρ : Representation (ZMod p)
      (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p m)) V)
    (hρ : Function.Injective ρ) (hdim : Module.finrank (ZMod p) V = 2*m) :
    ρ.IsIrreducible := by
  obtain ⟨W, hI, hfaithful, hle⟩ :=
    exists_faithful_irreducible_factor_of_sl2_faithful hp hm ρ hρ
  have hbound := sl2_faithful_finrank_bound hp hm W.toRepresentation hfaithful
  have hWtop : W = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    apply Submodule.eq_top_of_finrank_eq
    omega
  have hAtom := (Subrepresentation.irreducible_iff_isAtom W).mp hI
  rw [hWtop] at hAtom
  exact isSimpleOrder_iff_isAtom_top.mpr hAtom

public theorem sl2_faithful_fixed_finrank_of_eq
    {p m : ℕ} [Fact p.Prime] (hp : Odd p) (hm : m ≠ 0)
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (ρ : Representation (ZMod p)
      (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p m)) V)
    (hρ : Function.Injective ρ) (hdim : Module.finrank (ZMod p) V = 2*m)
    (P : Sylow p (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p m))) :
    Module.finrank (ZMod p) (Representation.invariants (ρ.comp P.toSubgroup.subtype)) = m := by
  let hI : ρ.IsIrreducible := isIrreducible_of_minimal hp hm ρ hρ hdim
  have hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) (GaloisField p m)) ∉ ρ.ker := by
    intro h
    have heq := hρ (h.trans (map_one ρ).symm)
    have hh := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField p m) =>
      (g : Matrix (Fin 2) (Fin 2) (GaloisField p m)) 0 0) heq
    have hfield : (-1 : GaloisField p m) = 1 := by simpa using hh
    have htwo : (2 : GaloisField p m) = 0 := by linear_combination -hfield
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p m) p 2).mp htwo
    have hp2 : p = 2 := ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
      (Fact.out : p.Prime).ne_one
    subst p
    exact (by decide : ¬ Odd 2) hp
  rw [finrank_sylow_invariants_eq_endField p ρ P]
  exact endField_finrank_eq_of_minimal p ρ hp hneg m hm (GaloisField.card p m hm) hdim

end SL2
end Representation
