module

public import Theory.Representation.SL2.FrobeniusOrbitDimension
public import Theory.Representation.SL2.OrbitDimensionBounds
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Low-Degree Irreducible Representations of Odd SL2

Let p be an odd prime and m positive. Every nontrivial finite-dimensional
irreducible representation of SL2(p^m) over GF(p) has dimension at least 2m.
For a faithful irreducible representation, the dimension is 2m, or 8m/3 with
3 dividing m, or at least 4m. The exceptional alternative is written as
3*dimension=8*m to avoid natural-number division.

The actual highest-weight classification and Schur-field Frobenius descent
supply m=s*t and dimension=s*b^t, with s,t positive and b at least two.
Faithfulness excludes the central matrix -I from the kernel, forcing t odd
and b even. The proved numerical orbit estimates give the two conclusions.

This is the full statement (1E) of Fong--Wong, Nagoya Math. J. 36 (1969),
p. 149, including its faithful refinement. Alperin--Brauer--Gorenstein II.4,
Lemma 18 uses it after extracting a faithful irreducible factor from an
arbitrary faithful representation; that extraction is proved separately.
-/

open scoped MatrixGroups

namespace Representation.SL2

private theorem sl2_neg_one_ne_one {p m : ℕ} [Fact p.Prime] (hp : Odd p) :
    (-1 : SL(2, GaloisField p m)) ≠ 1 := by
  intro h
  have hh := congrArg (fun g : SL(2, GaloisField p m) =>
    (g : Matrix (Fin 2) (Fin 2) (GaloisField p m)) 0 0) h
  have heq : (-1 : GaloisField p m) = 1 := by simpa using hh
  have htwo : (2 : GaloisField p m) = 0 := by linear_combination -heq
  have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p m) p 2).mp htwo
  have hp2 : p = 2 := ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
    (Fact.out : p.Prime).ne_one
  subst p
  exact (by decide : ¬ Odd 2) hp

public theorem sl2_irreducible_finrank_bound {p m : ℕ} [Fact p.Prime]
    (hp : Odd p) (hm : m ≠ 0) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V]
    (ρ : Representation (ZMod p) SL(2, GaloisField p m) V) [ρ.IsIrreducible]
    (hρ : ∃ g, ρ g ≠ 1) : 2*m ≤ Module.finrank (ZMod p) V := by
  obtain ⟨s,t,b,_,ht,hb,hmt,hd,_⟩ := exists_frobenius_orbit_parameters p ρ hp hρ m hm
    (GaloisField.card p m hm)
  rw [hmt, hd]
  exact orbit_dimension_lower_bound ht hb

public theorem sl2_faithful_irreducible_finrank_trichotomy {p m : ℕ} [Fact p.Prime]
    (hp : Odd p) (hm : m ≠ 0) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V]
    (ρ : Representation (ZMod p) SL(2, GaloisField p m) V) [ρ.IsIrreducible]
    (hρ : Function.Injective ρ) :
    Module.finrank (ZMod p) V = 2*m ∨
      (3 * Module.finrank (ZMod p) V = 8*m ∧ 3 ∣ m) ∨
      4*m ≤ Module.finrank (ZMod p) V := by
  have hneg : (-1 : SL(2, GaloisField p m)) ∉ ρ.ker := by
    intro h
    apply sl2_neg_one_ne_one hp
    apply hρ
    exact h.trans (map_one ρ).symm
  obtain ⟨s,t,b,_,_,hb,hmt,hd,hpar⟩ := exists_frobenius_orbit_parameters p ρ hp
    ⟨-1, hneg⟩ m hm (GaloisField.card p m hm)
  obtain ⟨htodd,hbeven⟩ := hpar hneg
  rw [hmt, hd]
  exact orbit_dimension_trichotomy htodd hb hbeven

end Representation.SL2
