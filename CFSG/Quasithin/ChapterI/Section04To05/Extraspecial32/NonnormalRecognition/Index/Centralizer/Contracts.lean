module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Centralizer.Local
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Centralizer.Embedding
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!+# Intermediate contracts for second-centralizer recognition

The residual facts are the transfer equality and local four-group centralizer
conditions used to recognize J as A₅. The extension contract asks for an actual
isomorphism of K with the A₉ centralizer agreeing with the fixed eight-point
inclusion on K ∩ L. It assumes no ambient fusion conclusion. Odd index and
the two marked classes will propagate that local agreement to all of K.

These are proof obligations, not additional hypotheses of the source theorem.
Their producers are separate from the residual recognition and final assembly.

Source: Aschbacher, “A 2-local characterization of M12”, Proposition 3.3,
printed p.38. In particular J and X mean O², with their original inclusions.
-/

@[expose] public section
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index
open Subgroup
variable {G : Type*} [Group G] {z : G} {L : Subgroup G}

/-- The local facts required by the A₄/A₅ recognition theorem, for the actual
two-residual J and the marked involution `(45)(67)`. -/
structure ResidualFacts (d : InvolutionData z L) : Prop where
  intersection : d.J ⊓ L = d.X
  x_card : Nat.card d.X = 12
  i_mem : (d.i : G) ∈ d.J
  involutions_conjugate : ∀ u : d.J, orderOf u = 2 →
    IsConj u (⟨(d.i : G), i_mem⟩ : d.J)
  centralizer_equiv : Nonempty
    (centralizer ({⟨(d.i : G), i_mem⟩} : Set d.J) ≃* DihedralGroup 2)

/-- A genuine extension of the standard local inclusion. This contract has
no ambient conjugacy-class fields. -/
structure CentralizerExtension (d : InvolutionData z L) where
  equiv : d.K ≃* Centralizer t9
  agrees_on_local : ∀ (a : d.K) (ha : (a : G) ∈ L),
    (equiv a : Nine) = eightToNine (d.equiv ⟨(a : G), ha⟩)

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index
end
