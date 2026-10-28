module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Frame

/-!
# The original SL₃ three-conjugate configuration and collapse

The Cartan frame construction chooses x,y in the original L ∩ N_G(X) and
supplies the genuine G.2.5 hypothesis. Its natural and dual quotient models
give all three layer-generation identities. Cartan normalization and odd
order discharge the opposite-pair action inputs, so the original core
argument gives S ≤ O₂(G₁). The centrality from 11.5.5 then collapses S to
the literal triple intersection S₂.

The remaining inputs are preceding Chapter 11 conclusions: the field point,
Sylow invariance and local irreducibility; 11.4.3(2)'s G₁ = KYM₁;
11.5.5's core, Frattini and centrality bounds; and 11.5.6(4–5)'s Cartan
commutator bounds. Their final discharge belongs to
`qt-d-1222-natural-closure` and `qt-d-1222-natural-closure-cartan`.
The subsequent block and outside-subgroup arguments remain with
`qt-d-1222-natural-closure-sl3`.

All quotients and right conjugates are the original ones. In particular,
E.L₁ is the solvable residual of N_L(V₁), not G.2's two-residual.
Source: Aschbacher–Smith, 11.5.7, printed pp.781–782; G.2.5, pp.335–336.
-/

open Subgroup Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource

public section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)
    (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))

/-- Construct the marked G.2.5 configuration, prove its three generation
identities, and apply the original core and collapse arguments. Only the
specified preceding Chapter 11 geometry and Cartan/core conclusions remain. -/
theorem exists_source_three_conjugates
    (P : Submodule E.input.field.Carrier (Fin 3 → E.input.field.Carrier))
    (hdim : Module.finrank E.input.field.Carrier P = 1)
    (hpoint : E.point = (LocalGeometry.Coordinates.sl3 m).binarySubspace P)
    (hT : (T : Subgroup G) ≤ E.G₁)
    (hX : LocalGeometry.IsCartan T L E.X) (hXG : E.X ≤ E.G₁)
    (hirr : ∀ A : Subgroup G, E.V₁ ≤ A → A ≤ V →
      E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) → A = E.V₁ ∨ A = V)
    (hUT : E.W ≤ (T : Subgroup G)) (hn : ¬ IsMulCommutative E.W)
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hUQ : E.W ≤ E.G₁.pCoreIn 2)
    (hgen : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁)
    (hcartan : ∀ A : Subgroup G, A ≤ (T : Subgroup G) → A = ⁅A,E.X⁆ →
      (frattini A).map A.subtype ≤ E.G₁.pCoreIn 2 → ⁅A,E.Y⁆ ≤ E.Y.pCoreIn 2)
    (hcoreX : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,E.X⁆ ≤
      (E.K ⊔ (T : Subgroup G)).pCoreIn 2)
    (hcentral : ⁅E.W,E.G₁.pCoreIn 2⁆ ≤ E.V₁) :
    ∃ x y : G, x ∈ L ⊓ normalizer (E.X : Set G) ∧
      y ∈ L ⊓ normalizer (E.X : Set G) ∧
      Nonempty (ChapterG.Section02.LinearThree.Hypothesis
        (setup E) E.input.field.Carrier E.input.field.degree x y) ∧
      (threeCore E x y = ⁅threeCore E x y,E.L₁⁆ ⊔ oppositePair E x y) ∧
      (threeCore E x y ≤ ⁅threeCore E x y,E.X⁆ ⊔ (threeCore E x y ⊓ E.W)) ∧
      (oppositePair E x y ≤ ⁅oppositePair E x y,E.X⁆ ⊔ triple E x y) ∧
      (E.X ≤ normalizer (oppositePair E x y : Set G)) ∧
      Nat.Coprime (Nat.card E.X) (Nat.card (oppositePair E x y)) ∧
      threeCore E x y ≤ E.G₁.pCoreIn 2 ∧ threeCore E x y = triple E x y := by
  obtain ⟨x, y, hx, hy, ⟨d⟩, hres, hmove, hpair⟩ :=
    Generation.Frame.source_frame_layer_generation E m P hdim hpoint hT hX hXG
      hirr hUT hn hf
  have hnorm := Cartan_normalizes_oppositePair E hXG hx.2 hy.2
  have hcop := Cartan_coprime_oppositePair E x y hUT hX
  have hcore := threeCore_le_point_core_of_cartan E d hUT hf hT hXG hUQ hgen
    hres hmove hpair hnorm hcop hcartan hcoreX
  exact ⟨x, y, hx, hy, ⟨d⟩, hres, hmove, hpair, hnorm, hcop, hcore,
    threeCore_eq_triple E d hUT hf hcore hcentral⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear
