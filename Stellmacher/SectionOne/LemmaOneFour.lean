module

public import Stellmacher.SectionsOneToFourDefs
open Theory.GroupAction
open Theory.ElementaryAbelian


open scoped BigOperators Pointwise

namespace Stellmacher.SectionOne

universe u

/-! **Stellmacher (1.4).**  The set `Ω(W)` is finite because `G` is finite;
we use a `Finset` representative so that the internal direct products in the
source are explicit. -/

public structure LemmaOneFourConclusion
    {G V : Type u} [Group G] [Group V] [Finite V]
    [MulDistribMulAction G V]
    (W0 : Subgroup G) (F : Finset (Subgroup G)) : Prop where
  part_a : IsInternalDirectProduct W0 F
  part_b :
    IsInternalDirectProductFamily (⊤ : Subgroup V)
      (fun i : Option {D : Subgroup G // D ∈ F} =>
        match i with
        | none => FixedPoints.subgroup W0 V
        | some D => commutatorAction (D : Subgroup G) V)

/-- **Stellmacher (1.4).**

Let `Ω(W) = {F₁, …, Fᵣ}` and `W₀ = ⟨F₁, …, Fᵣ⟩ ≤ O₃(G)`.  Then `W₀` and
`V` split as the internal direct products stated in the paper. -/
public theorem lemma_one_four
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (F : Finset (Subgroup G))
    (hF : ∀ D : Subgroup G, D ∈ F ↔ oneOmega (G := G) (V := V) D)
    (W0 : Subgroup G)
    (hW0 : W0 = ⨆ D : {D : Subgroup G // D ∈ F}, (D : Subgroup G))
    (hW0_le : W0 ≤ pCore 3 G) :
    LemmaOneFourConclusion (G := G) (V := V) W0 F := by
  sorry

end Stellmacher.SectionOne
