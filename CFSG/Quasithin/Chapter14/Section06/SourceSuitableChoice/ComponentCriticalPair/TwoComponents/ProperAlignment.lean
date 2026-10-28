module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.Properness
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.OrbitMatching.CommutatorImages

/-!
# Proper component alignment in the original terminal setup

The checked paired-module alignment puts the opposite component in one
literal conjugate component. The equality exclusion now makes this
containment proper. Conjugate subgroups have equal orders, so it cannot
lie properly in its own conjugate. The components therefore have different
orders and, as the complete pair of C-components of Mc, are both normal in Mc.
In particular T cannot interchange them: case (2) of 14.6.21 is excluded.

All actions use U/Z for the original U and central point, and the endpoint
retains its left conjugator. The actual support embeddings and diagram
action are earlier 14.6.20--23 data. Their construction and the remaining
normal-pair Sylow contradiction belong to qt-e-suitable-component-marking;
final suitable-choice assembly belongs to qt-e-suitable-existence.
Source: Aschbacher--Smith 14.6.24(3), printed p.1040.
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

/-- The original marked component pair has proper alignment and unequal
orders; its exchanged alternative is excluded and both components are
normal in Mc. The point, quotient and conjugator are unchanged. -/
theorem source_placedEndpoint_proper_alignment
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (K Kplus : Subgroup G)
    (p : PlacedEndpoint
      (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab) K Kplus)
    (hKM : K ≤ Mc) (hKplusM : Kplus ≤ Mc)
    (hcomp : (K.subgroupOf Mc).IsCComponent)
    (hcompPlus : (Kplus.subgroupOf Mc).IsCComponent)
    (hcross : ⁅⁅conjugateSpanBy (localModule T M) Mc,K⁆,Kplus⁆ = ⊥)
    {ρ : Representation (ZMod 2) (Source.Hstar Mc) E}
    (c : BinaryConjugationSection Mc (conjugateSpanBy (localModule T M) Mc)
      (centralInvolutions T) (ρ.comp (QuotientGroup.mk' (pCore 2 Mc))))
    (N : Subgroup (Source.Hstar Mc)) (m : Paired.Marking (ρ.comp N.subtype))
    (hN : N = subspaceStabilizer ρ m.leftEmbedding.range ⊓
      subspaceStabilizer ρ m.rightEmbedding.range)
    (hperm : ∀ a : Source.Hstar Mc,
      (m.leftEmbedding.range.map (ρ a) = m.leftEmbedding.range ∧
        m.rightEmbedding.range.map (ρ a) = m.rightEmbedding.range) ∨
      (m.leftEmbedding.range.map (ρ a) = m.rightEmbedding.range ∧
        m.rightEmbedding.range.map (ρ a) = m.leftEmbedding.range))
    (κ₁ κ₂ : BinaryLinearThree.Group →* N)
    (hκrange₁ : (N.subtype.comp κ₁).range = Source.starImage Mc K)
    (hκrange₂ : (N.subtype.comp κ₂).range = Source.starImage Mc Kplus)
    (hl₁ : ∀ k, m.left (κ₁ k) = MulAut.conj k)
    (hr₁ : ∀ k, m.right (κ₁ k) = 1)
    (hl₂ : ∀ k, m.left (κ₂ k) = 1)
    (hr₂ : ∀ k, m.right (κ₂ k) = MulAut.conj k)
    (hpair : ∀ J : Subgroup Mc, J.IsCComponent →
      J = K.subgroupOf Mc ∨ J = Kplus.subgroupOf Mc)
    (hZ₁ : centralInvolutions T ≤ ⁅conjugateSpanBy (localModule T M) Mc,K⁆)
    (hZ₂ : centralInvolutions T ≤ ⁅conjugateSpanBy (localModule T M) Mc,Kplus⁆)
    (hS₁ : c.imageSpace ⁅conjugateSpanBy (localModule T M) Mc,K⁆ = m.leftEmbedding.range)
    (hS₂ : c.imageSpace ⁅conjugateSpanBy (localModule T M) Mc,Kplus⁆ = m.rightEmbedding.range)
    (hK : (normalizer (K : Set G)).subgroupOf Mc =
      (subspaceStabilizer ρ m.leftEmbedding.range).comap (QuotientGroup.mk' (pCore 2 Mc)))
    (hKplus : (normalizer (Kplus : Set G)).subgroupOf Mc =
      (subspaceStabilizer ρ m.rightEmbedding.range).comap (QuotientGroup.mk' (pCore 2 Mc)))
    (a : N) (ha : m.left a ∉ MulAut.innerSubgroup BinaryLinearThree.Group) :
    Kplus < p.endpoint.conjugate K ∧ Nat.card Kplus < Nat.card K ∧
      (K.subgroupOf Mc).Normal ∧ (Kplus.subgroupOf Mc).Normal ∧
      ¬ ∃ t ∈ (T : Subgroup G), Kplus = K.map (MulAut.conj t⁻¹).toMonoidHom := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,Mc⟩
  let h : D.Hypothesis := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let : IsElementaryAbelian 2 D.UH :=
    h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  obtain ⟨hb,_,_⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hunique hmany hcard e hab
    Mc (ComponentSupports.terminal_outside hG T hempty hM hunique hmany hcard e)
  have hAN : Source.starImage Mc (p.endpoint.conjugate D.UH) ≤ N := by
    rw [hN]
    rintro _ ⟨u,hu,rfl⟩
    have hl : u ∈ (normalizer (K : Set G)).subgroupOf Mc := p.normalizes_left hu
    have hr : u ∈ (normalizer (Kplus : Set G)).subgroupOf Mc := p.normalizes_right hu
    rw [hK] at hl
    rw [hKplus] at hr
    exact ⟨hl,hr⟩
  have hNplus : ∀ x : Mc, QuotientGroup.mk' (pCore 2 Mc) x ∈ N →
      (x : G) ∈ normalizer (Kplus : Set G) := by
    intro x hx
    rw [hN] at hx
    have hh : x ∈ (normalizer (Kplus : Set G)).subgroupOf Mc := by
      rw [hKplus]
      exact hx.2
    exact hh
  have hpoint : ¬ p.endpoint.conjugate D.V₁ ≤ D.V₁ := by
    intro hp
    have hh := OrbitMatching.source_critical_points_disjoint
      hG T hempty hM hunique hmany hcard e hab p.endpoint
    change D.V₁ ⊓ p.endpoint.conjugate D.V₁ = ⊥ at hh
    rw [inf_eq_right.mpr hp] at hh
    have hc : Nat.card (p.endpoint.conjugate D.V₁) = 2 :=
      (card_map_of_injective (MulAut.conj p.endpoint.representative).injective).trans h.point_card
    rw [hh] at hc
    simp at hc
  have hne := placedEndpoint_component_ne h K Kplus p hb hKM hKplusM hcomp hcompPlus
    hZ₁ hZ₂ hpoint c N m hAN hNplus hS₁ hS₂ κ₁ hl₁ a ha
  have halign := source_placedEndpoint_component_alignment
    hG T hempty hM hunique hmany hcard e hab K Kplus p hKM hKplusM hcomp hcompPlus
    hcross c N m hN hperm κ₁ κ₂ hκrange₁ hκrange₂ hl₁ hr₁ hl₂ hr₂
  obtain ⟨J,hJ,hinc,hneq⟩ : ∃ J : Subgroup G,
      (J = p.endpoint.conjugate K ∨ J = p.endpoint.conjugate Kplus) ∧
      Kplus ≤ J ∧ Kplus ≠ J := by
    rcases halign with hl | hr
    · exact ⟨_,Or.inl rfl,hl,hne.1⟩
    · exact ⟨_,Or.inr rfl,hr,hne.2⟩
  obtain ⟨_,hstrict,hcardlt⟩ := strict_conjugate_pair K Kplus J
    p.endpoint.representative hJ hinc hneq
  obtain ⟨hn,hnplus⟩ := relative_cComponent_pair_normal_of_card_ne
    Mc K Kplus hKM hKplusM hcomp hcompPlus hpair hcardlt.ne.symm
  refine ⟨hstrict,hcardlt,hn,hnplus,?_⟩
  rintro ⟨t,_,ht⟩
  rw [ht,card_map_of_injective (MulAut.conj t⁻¹).injective] at hcardlt
  exact Nat.lt_irrefl _ hcardlt

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
