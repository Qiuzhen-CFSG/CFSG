module

public import Theory.Representation.BinaryOffender.EndField
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.HigherRecognition.Models

/-!
# Absolute fixed-space bounds needed by the even twisted families

The family-specific mathematical input is a strict fixed-space codimension
bound over any finite coefficient field of characteristic two. It retains
the degree of that field over the binary field and every elementary subgroup
of the ambient group, including subgroups acting by outer automorphisms.

The application below constructs the actual endomorphism-field representation
of the original binary action. It supplies absolute irreducibility of that
ambient action, faithfulness, and irreducibility on the original component.
Absolute irreducibility of the component restriction is not assumed.

This is a conditional reduction for Guralnick–Malle II, Theorem 8.1 and
Lemmas 8.6, 8.8, 8.10, followed by the F-module argument on p.64.
It does not prove any of the three model-specific bounds.
-/

@[expose] public section

open scoped MonoidAlgebra
open Representation Representation.BinaryOffender

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted

universe u v

/-- The precise absolute representation estimate consumed by the binary
exclusion. The group-theoretic and model hypotheses belong to its producers. -/
def AbsoluteGap (H : Type u) [Group H] (N : Subgroup H) : Prop :=
  ∀ (E W : Type v) [Field E] [Finite E] [Algebra (ZMod 2) E] [CharP E 2]
    [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (σ : Representation E H W),
    IsAbsolutelyIrreducible σ → IsIrreducible (σ.comp N.subtype) →
    Function.Injective σ →
    ∀ A : Subgroup H, IsElementaryTwo A →
      rank A < Module.finrank (ZMod 2) E *
        Module.finrank E (W ⧸ invariants (σ.comp A.subtype))

variable {H : Type u} [Group H] {V : Type v} [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (N : Subgroup H) (ρ : Representation (ZMod 2) H V) [ρ.IsIrreducible]
  [IsIrreducible (ρ.comp N.subtype)]

/-- Apply a proved absolute fixed-space bound to the original binary action.
The only extra input is `hgap`, still to be supplied for each concrete family. -/
theorem not_ff_of_absoluteGap (hρ : Function.Injective ρ)
    (hgap : AbsoluteGap.{u, v} H N) : ¬ IsFFModule ρ := by
  let E := Module.End (ZMod 2)[H] ρ.asModule
  let : CharP E 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) E).injective 2
  let : Finite ρ.asModule := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod 2) ρ.asModule)
  let : FiniteDimensional E ρ.asModule := Module.Finite.of_finite
  exact EndField.not_ff_of_fixedSpace_gap ρ
    (hgap E ρ.asModule ρ.endFieldRep (endFieldRep_isAbsolutelyIrreducible ρ)
      (EndField.restriction_irreducible ρ N) (EndField.injective ρ hρ))

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted
