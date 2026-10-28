module

public import Theory.Representation.QuadraticFourGroup.Models
public import Theory.Representation.QuadraticFourGroup.Recognition.ComponentSpectrum
public import Theory.Representation.QuadraticFourGroup.Recognition.OddTranspositions.Definitions
public import Theory.Representation.QuadraticFourGroup.Recognition.OddTranspositions.Linear
public import Theory.Representation.NormalInvariants

/-!
# Odd transpositions: assembly from the diagonal group argument

The actual subgroup `K = E(C_E(a))` and its overgroup `Y = K ⊔ B` are defined
in `Definitions`. The linear part proves the dihedral contradiction, including
nonzero displacement on the central-involution fixed space. Irreducibility
and faithfulness exclude a nonzero globally fixed vector.

The assembly theorem below still requires the group-theoretic commutator
identity `[K,B] = K` and generation by `Y,Yˣ` for involution products. These
are explicit undischarged premises, not fields of a source hypothesis or a
claimed proof of the complete theorem. They must be proved using the diagonal
structure and maximality of `K Z(E)` in the generated-overgroup setup.

`Definitions` also isolates an additional sufficient input for the quotient
involution: odd-order solvability of this particular component quotient.
It does not discharge that input or infer evenness from the spectrum.

Source: GLS, volume 2, Theorem 25.14, Steps 1--3, and Lemmas 3.25, 3.27.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace Representation.QuadraticFourGroup

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L B : Subgroup G} {a : G}

/-- Faithfulness and the distinguished involution exclude fixed vectors in
an irreducible source representation. -/
theorem Hypotheses.fixed_eq_zero [ρ.IsIrreducible] (h : Hypotheses ρ L B a)
    (v : V) (hv : ∀ g : G, ρ g v = v) : v = 0 := by
  by_contra hne
  have hfix : Representation.invariants (ρ.comp (⊤ : Subgroup G).subtype) ≠ ⊥ := by
    intro he
    have hm : v ∈ Representation.invariants (ρ.comp (⊤ : Subgroup G).subtype) := fun g => hv g
    rw [he, Submodule.mem_bot] at hm
    exact hne hm
  have hk := Representation.le_ker_of_normal_invariants_ne_bot ρ ⊤ hfix
  have haρ : ρ a = 1 := MonoidHom.mem_ker.mp (hk (mem_top a))
  have ha : a = 1 := h.faithful (haρ.trans ρ.map_one.symm)
  have hi := h.involution
  simp [ha] at hi

/-- Step 3's displacement conclusion follows from the diagonal commutator
identity; it is not assumed as part of a certificate. -/
theorem Hypotheses.diagonalOvergroup_fixesDisplacements
    (h : Hypotheses ρ L B a)
    (hcomm : ⁅diagonalLayer L B a, B⁆ = diagonalLayer L B a) :
    FixesDisplacements ρ a (diagonalOvergroup L B a) :=
  (h.quadratic.of_commutator_eq (diagonalLayer_le_centralizer L B a) hcomm).sup
    h.quadratic

/-- Conditional assembly of Steps 1--3. The final source theorem must
establish both group-theoretic premises for the actual diagonal layer. -/
theorem Hypotheses.hasOddTranspositions_of_diagonal_generation
    [Finite G] [ρ.IsIrreducible] (h : Hypotheses ρ L B a)
    (hcomm : ⁅diagonalLayer L B a, B⁆ = diagonalLayer L B a)
    (hgen : ∀ x : G, orderOf (a * (x⁻¹ * a * x)) = 2 →
      diagonalOvergroup L B a ⊔
        (diagonalOvergroup L B a).map (MulAut.conj x⁻¹).toMonoidHom = ⊤) :
    HasOddTranspositions a :=
  hasOddTranspositions_of_generates h.faithful h.involution h.fixed_eq_zero
    (h.diagonalOvergroup_fixesDisplacements hcomm) hgen


end Representation.QuadraticFourGroup

end
