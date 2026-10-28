module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Statements
public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.SymplecticCartan

/-!
# The earlier A.3.15 input for a large-prime subgroup

This is the universal earlier-source case statement used by Proposition
1.3.4, not an assumption of that proposition's embedding conclusion.
The ambient input retains its simple generalized Fitting subgroup, SQTK,
actual Sylow two-subgroup, permuting p-subgroup and nontrivial three-residual.
Each characteristic-two row retains the actual field/Cartan configuration
and model. The cyclic rows combine A.3.15(1),(4),(6),(7); in (6), a p-group
with p > 3 cannot have order 21. The defining-characteristic row retains
its own prime q, which the consumer identifies with the prime of B.

The characteristic-two families are the complete Theorem C possibilities
in A.3.15(5). This file deliberately supplies no proof of the universal
case-existence statement. The source assembly must provide that earlier
lemma; none of the later irreducibility, plane or automizer conclusions
is included in its hypotheses.

Source: Aschbacher–Smith A.3.15, printed pp.50–51; 1.3.4, pp.510–511.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge
universe u
variable {J : Type u} [Group J] [Finite J]

inductive A315PrimeCases (D B : Subgroup J) [D.Normal] (S : Sylow 2 J) (p : ℕ) : Prop
  | cyclic (hc : IsCyclic B)
  | definingThree (q : ℕ) (hq : q.Prime) (ho : Odd q)
      (model : ClassicalGroup.IsPSL D 3 q) (plane : Nonempty (B ≃* Plane q))
  | oddCartan (K : Subgroup J) (q : ℕ) [hq : Fact q.Prime] (δ ε : OddCartan.Sign)
      (c : OddCartan.CaseThree D B (S : Subgroup J) K q δ ε)
  | rankOne (n : ℕ) (hn : 1 < n) (model : EvenActions.RankOne.IsBinaryRankOne D n)
  | linear (F : Type) [Field F] [Finite F] (n : ℕ)
      (c : EvenActions.Linear.SourceAlignment.SourceConfiguration F n
        ((S : Subgroup J).subgroupOf D) (B.subgroupOf D))
  | symplectic (F : Type) [Field F] [Finite F] (n : ℕ)
      (c : SymplecticAction.RawCartan (F := F) n
        ((S : Subgroup J).subgroupOf D) (B.subgroupOf D))
  | g2 (F : Type) [Field F] (e : D ≃* Atlas.G2.Model F)
      (n f : ℕ) (F₀ H₀ I : Subgroup (MulAut D))
      (c : EvenActions.G2.Source.RawCartan.Input D KnownSimple.IsKnownSimple e S B p n f F₀ H₀ I)
  | triality (a : Triality.Standard.Parameters) (n : ℕ)
      (e : D ≃* Triality.Standard.Carrier a)
      (c : EvenActions.Triality.SourceAlignment.RawConfiguration a n
        (((S : Subgroup J).subgroupOf D).map e.toMonoidHom)
        ((B.subgroupOf D).map e.toMonoidHom))
  | ree (m : ℕ) (d : ReeF4.LocalBlockInput m) (e : D ≃* ReeF4.Model m)
      (n f : ℕ) (F₀ H₀ I : Subgroup (MulAut D))
      (c : EvenActions.Ree.Source.RawCartan D d e S B n f F₀ H₀ I)

/-- The universal earlier A.3.15 implication in the prime-subgroup case.
Its raw configurations still require all their original geometric clauses. -/
@[expose] def A315PrimeSubgroupTheorem : Prop :=
  ∀ (J : Type u) [Group J] [Finite J] (D B : Subgroup J) (S : Sylow 2 J) (p : ℕ)
    (h : OddCartan.AmbientInput KnownSimple.IsKnownSimple D B S p),
      letI : D.Normal := h.normal
      A315PrimeCases D B S p

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge
