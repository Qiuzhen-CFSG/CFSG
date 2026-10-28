module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.Reduction
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedMovedEmbedding.SmallModels

/-!
# Small rows in the marked 14.3.20 component

The original factor A embeds as an elementary subgroup of order sixteen in
B.subgroupOf C_G(d). The existing intrinsic rank bounds therefore exclude
both alternating rows, including their triple covers, and the odd rows of
1.1.5. The surviving alternatives retain B, its relative componenthood, its
commutator identity, and the literal conjugation action of the original z.

This is a reduction of the model list, not the remaining source exclusion.
Source: Aschbacher--Smith, 14.3.20, p.998 and 1.1.5(3), pp.501--503.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}
variable {F : InvariantFlag T V 2} {L A : Subgroup G}

/-- The even rows of 1.1.5, including the original inner automorphism. -/
def EvenModelAction (X : Type*) [Group X] (α : MulAut X) : Prop :=
  (IsSimpleGroup X ∧ LieTypeTwoModel X ∧ α ∈ (MulAut.conj (G := X)).range) ∨
  (center X ≠ ⊥ ∧ center X = pCore 2 X ∧
    (ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 3 4 ∨
      ClassificationModels.IsG2At (X ⧸ pCore 2 X) 4) ∧
    α ∈ (MulAut.conj (G := X)).range)

/-- The sporadic rows of 1.1.5, retaining the quotient and two-central action. -/
def SporadicModelAction (X : Type*) [Group X] (α : MulAut X) : Prop :=
  ∃ name : ClassificationModels.SporadicName, name ≠ .j3 ∧
    Nonempty ((X ⧸ pCore 2 X) ≃* name.Carrier) ∧ TwoCentralInner α

namespace MarkedPoint
variable (P : MarkedPoint F L A)

/-- A subfamily of the actual containing components, with the same action of z. -/
def ComponentWithAction (z : G)
    (model : ∀ B : Subgroup G, MulAut (B.subgroupOf P.globalCentralizer) → Prop) : Prop :=
  ∃ B : Subgroup G, B ≤ P.globalCentralizer ∧ P.blockCentralizer ≤ B ∧
    IsComponent P.globalCentralizer (B.subgroupOf P.globalCentralizer) ∧
    B = ⁅B, zpowers z⁆ ∧
    ∃ α : MulAut (B.subgroupOf P.globalCentralizer),
      (∀ x : B.subgroupOf P.globalCentralizer,
        ((α x : P.globalCentralizer) : G) = z * (x : G) * z⁻¹) ∧ model B α

abbrev EvenComponent (z : G) : Prop :=
  P.ComponentWithAction z (fun B α => EvenModelAction (B.subgroupOf P.globalCentralizer) α)

abbrev SporadicComponent (z : G) : Prop :=
  P.ComponentWithAction z (fun B α => SporadicModelAction (B.subgroupOf P.globalCentralizer) α)

/-- The original elementary sixteen excludes the alternating and odd rows in
the literal component of C_G(d), without changing its action or quotient. -/
theorem classifiedComponent_cases (hA : ElementaryFactor F L A) (z : G)
    (h : P.ClassifiedComponent z) : P.EvenComponent z ∨ P.SporadicComponent z := by
  obtain ⟨B, hB, hKB, hcomp, hcomm, α, hα, hm⟩ := h
  let C := P.globalCentralizer
  let K := B.subgroupOf C
  let E := (A.subgroupOf C).subgroupOf K
  have hAC : A ≤ C := P.factor_le_blockCentralizer.trans inf_le_right
  have hAB : A ≤ B := P.factor_le_blockCentralizer.trans hKB
  have hAK : A.subgroupOf C ≤ K := fun _ hx => hAB hx
  let := hA.elementary
  let : IsElementaryAbelian 2 (A.subgroupOf C) := IsElementaryAbelian.subgroupOf hAC
  have hE : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hAK
  have hc : Nat.card E = 16 :=
    (Nat.card_congr ((subgroupOfEquivOfLe hAK).trans (subgroupOfEquivOfLe hAC)).toEquiv).trans hA.card
  rcases Section06.SourcePairedMovedEmbedding.modelAction115_large_elementary_cases
      E hE hc.ge hm with hl | ht | hs
  · exact Or.inl ⟨B, hB, hKB, hcomp, hcomm, α, hα, Or.inl hl⟩
  · exact Or.inl ⟨B, hB, hKB, hcomp, hcomm, α, hα, Or.inr ht⟩
  · exact Or.inr ⟨B, hB, hKB, hcomp, hcomm, α, hα, hs⟩

end MarkedPoint
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
