module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.PointPlacement

/-!
# A placed endpoint for the terminal component-pair endgame

Select a critical endpoint using the actual paired supports. The uniform
point-placement theorem puts its point in one component support. Relative
component centralization kills the opposite action; joint faithfulness
then bounds the original star actor by rank two. Choosing the component
orientation constructs every field of PlacedEndpoint, including the
literal opposite-core denominator and its rank comparison.

The component embeddings identify the original star images and retain
conjugation covariance. Their construction and the simultaneous module
markings remain with qt-e-suitable-component-marking under the genuine
14.6.20--23 support inputs. The component-alignment and Sylow contradiction
are subsequent obligations; final suitable-choice assembly remains with
qt-e-suitable-existence.
Source: Aschbacher--Smith 14.6.24(3), printed pp.1039--1041.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
open Chapter13.Section08 Chapter13.Section08.SourceCompletion
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open BinaryLinearThree.NaturalDual
variable {G E : Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

/-- Construct the endpoint required by the two-component endgame, choosing
which original component contains its point. Every endpoint and rank field
is proved from the marked support inputs. -/
theorem source_placedEndpoint_of_paired_supports
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    {ρ : Representation (ZMod 2) (Source.Hstar Mc) E}
    (c : BinaryConjugationSection Mc (conjugateSpanBy (localModule T M) Mc)
      (centralInvolutions T) (ρ.comp (QuotientGroup.mk' (pCore 2 Mc))))
    (N : Subgroup (Source.Hstar Mc)) (m : Paired.Marking (ρ.comp N.subtype))
    (hN : N = subspaceStabilizer ρ m.leftEmbedding.range ⊓
      subspaceStabilizer ρ m.rightEmbedding.range)
    (hspan : m.leftEmbedding.range ⊔ m.rightEmbedding.range ⊔ fixedSpace ρ ⊤ = ⊤)
    (hperm : ∀ a : Source.Hstar Mc,
      (m.leftEmbedding.range.map (ρ a) = m.leftEmbedding.range ∧
        m.rightEmbedding.range.map (ρ a) = m.rightEmbedding.range) ∨
      (m.leftEmbedding.range.map (ρ a) = m.rightEmbedding.range ∧
        m.rightEmbedding.range.map (ρ a) = m.leftEmbedding.range))
    (K Kplus : Subgroup G) (hKM : K ≤ Mc) (hKplusM : Kplus ≤ Mc)
    (hcomp : (K.subgroupOf Mc).IsCComponent) (hcompPlus : (Kplus.subgroupOf Mc).IsCComponent)
    (hK : (normalizer (K : Set G)).subgroupOf Mc =
      (subspaceStabilizer ρ m.leftEmbedding.range).comap (QuotientGroup.mk' (pCore 2 Mc)))
    (hKplus : (normalizer (Kplus : Set G)).subgroupOf Mc =
      (subspaceStabilizer ρ m.rightEmbedding.range).comap (QuotientGroup.mk' (pCore 2 Mc)))
    (hZ₁ : centralInvolutions T ≤ ⁅conjugateSpanBy (localModule T M) Mc,K⁆)
    (hZ₂ : centralInvolutions T ≤ ⁅conjugateSpanBy (localModule T M) Mc,Kplus⁆)
    (hS₁ : c.imageSpace ⁅conjugateSpanBy (localModule T M) Mc,K⁆ = m.leftEmbedding.range)
    (hS₂ : c.imageSpace ⁅conjugateSpanBy (localModule T M) Mc,Kplus⁆ = m.rightEmbedding.range)
    (hcross₁ : ⁅⁅conjugateSpanBy (localModule T M) Mc,K⁆,Kplus⁆ = ⊥)
    (hcross₂ : ⁅⁅conjugateSpanBy (localModule T M) Mc,Kplus⁆,K⁆ = ⊥)
    (κ₁ κ₂ : BinaryLinearThree.Group →* Source.Hstar Mc)
    (hκ₁ : Function.Injective κ₁) (hκ₂ : Function.Injective κ₂)
    (hκrange₁ : κ₁.range = Source.starImage Mc K)
    (hκrange₂ : κ₂.range = Source.starImage Mc Kplus)
    (hκact₁ : ∀ (n : N) (k : BinaryLinearThree.Group),
      κ₁ (m.left n k) = (n : Source.Hstar Mc) * κ₁ k * (n : Source.Hstar Mc)⁻¹)
    (hκact₂ : ∀ (n : N) (k : BinaryLinearThree.Group),
      κ₂ (m.right n k) = (n : Source.Hstar Mc) * κ₂ k * (n : Source.Hstar Mc)⁻¹) :
    let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    Nonempty (PlacedEndpoint h K Kplus) ∨ Nonempty (PlacedEndpoint h Kplus K) := by
  obtain ⟨_,p,hpK,hpKplus⟩ := source_quadraticEndpoint_of_paired_supports
    hG T hempty hM hunique hmany hcard e hab c N m hN hspan hperm K Kplus hK hKplus
  obtain ⟨hb,_,_⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hunique hmany hcard e hab
    Mc (ComponentSupports.terminal_outside hG T hempty hM hunique hmany hcard e)
  have hAN := p.le_pair_stabilizer hb c N m hN hspan hperm
  have hp := source_pairPointPlacement_of_paired_supports
    hG T hempty hM hunique hmany hcard e hab c N m hN hspan hperm
    K Kplus hZ₁ hZ₂ hS₁ hS₂
  rcases hp p.endpoint p.positive p.comparison with hpoint | hpoint
  · have hr := source_actor_rank_and_inner_of_point_support
      hG T hempty hM hunique hmany hcard e hab c p N m hAN K Kplus
      hpKplus hpoint hKplusM hcompPlus hcross₁ κ₂ hκ₂ hκrange₂ hκact₂
    exact Or.inl ⟨⟨p.endpoint,hpK,hpKplus,hpoint,p.positive,p.comparison,hr.2.1⟩⟩
  · let m' : Paired.Marking (ρ.comp N.subtype) := {
      left := m.right
      right := m.left
      leftEmbedding := m.rightEmbedding
      rightEmbedding := m.leftEmbedding
      left_injective := m.right_injective
      right_injective := m.left_injective
      disjoint := m.disjoint.symm
      span := by rw [sup_comm m.rightEmbedding.range m.leftEmbedding.range]; exact m.span
      left_intertwines := m.right_intertwines
      right_intertwines := m.left_intertwines }
    have hr := source_actor_rank_and_inner_of_point_support
      hG T hempty hM hunique hmany hcard e hab c p N m' hAN Kplus K
      hpK hpoint hKM hcomp hcross₂ κ₁ hκ₁ hκrange₁ hκact₁
    exact Or.inr ⟨⟨p.endpoint,hpKplus,hpK,hpoint,p.positive,p.comparison,hr.2.1⟩⟩
end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
