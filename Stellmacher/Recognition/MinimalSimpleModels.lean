module

public import BenderSuzuki.MatrixGroups.PSL2
public import Theory.Comparator.Defs

/-!
# The five models in Thompson's minimal-simple corollary

The catalogue records actual multiplicative equivalences to the five families
in Thompson, *Nonsolvable finite groups all of whose local subgroups are
solvable*, I, Bull. Amer. Math. Soc. 74 (1968), Corollary 1, p. 388.
See `docs/thompson-minimal-simple-source-contract.md` for the source contract.

The prime-field condition is written as the two residues modulo five.
For Suzuki groups the shared model parameter is `n`, so the odd prime field
exponent is `2 * n + 1`. All models live in `Type`, while the group being
recognized may live in any universe. Catalogue membership asserts only the
displayed isomorphism; recognition and minimal simplicity of the models are
separate results. Transport of membership simply composes isomorphisms.
-/

namespace Stellmacher.Recognition

open BenderSuzuki.MatrixGroups

universe u v

/-- The five actual model families of Thompson's minimal-simple corollary. -/
public inductive ThompsonMinimalSimpleModel (G : Type u) [Group G] : Prop
  /-- `PSL₂(2^p)` for a prime exponent. -/
  | psl2Binary (p : ℕ) (hp : p.Prime) (e : G ≃* PSL2Model p)
  /-- `PSL₂(3^p)` for an odd prime exponent. -/
  | psl2ThreePower (p : ℕ) (hp : p.Prime) (hodd : Odd p)
      (e : G ≃* PSL2MatrixGroup (GaloisField 3 p))
  /-- `PSL₂(p)` for primes greater than three with residues two or three modulo five. -/
  | psl2Prime (p : ℕ) (hp : p.Prime) (hgt : 3 < p)
      (hmod : p % 5 = 2 ∨ p % 5 = 3)
      (e : letI : Fact p.Prime := ⟨hp⟩; G ≃* PSL2MatrixGroup (ZMod p))
  /-- `Sz(2^(2*n+1))` with odd prime exponent `2*n+1`. -/
  | suzuki (n : ℕ) (hp : (2 * n + 1).Prime) (e : G ≃* SzModel n)
  /-- The concrete projective special linear group `PSL₃(3)`. -/
  | psl3Three (e : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3))

namespace ThompsonMinimalSimpleModel

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- Membership in the catalogue transports across universes by isomorphism. -/
public theorem of_mulEquiv (hG : ThompsonMinimalSimpleModel G) (e : G ≃* H) :
    ThompsonMinimalSimpleModel H := by
  cases hG with
  | psl2Binary p hp f => exact .psl2Binary p hp (e.symm.trans f)
  | psl2ThreePower p hp hodd f => exact .psl2ThreePower p hp hodd (e.symm.trans f)
  | psl2Prime p hp hgt hmod f => exact .psl2Prime p hp hgt hmod (e.symm.trans f)
  | suzuki n hp f => exact .suzuki n hp (e.symm.trans f)
  | psl3Three f => exact .psl3Three (e.symm.trans f)

/-- Catalogue membership is an isomorphism invariant. -/
public theorem iff_of_mulEquiv (e : G ≃* H) :
    ThompsonMinimalSimpleModel G ↔ ThompsonMinimalSimpleModel H :=
  ⟨fun hG => hG.of_mulEquiv e, fun hH => hH.of_mulEquiv e.symm⟩

end ThompsonMinimalSimpleModel

end Stellmacher.Recognition
