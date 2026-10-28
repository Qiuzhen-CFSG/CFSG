module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.SylowBound
public import Theory.Representation.BinaryConjugationSection.LinearThreeCentralizerIndex

/-!
# The terminal Sylow contradiction for a marked natural point

The same common point centralizer has two incompatible bounds. Proper
component alignment bounds every two-subgroup S there by 8|S|≤|T|.
If its opposite central point lies in a natural support, the literal
surjective SL₃(2) action and index-two support stabilizer construct such
an S with |T|≤4|S|. The original points are disjoint, so their chosen
nonidentity generator is a nonzero vector modulo the original point.

This proves the centralizer-count step for the original marked endpoint.
The actual natural and dual sections, their support stabilizers, and
placement in one of them must still be constructed from the paired marking
by qt-e-suitable-component-marking. In particular this conditional result
does not assert the completed two-component exclusion. Earlier source
support inputs remain with qt-e-suitable-component-supports, and final
suitable-choice assembly belongs to qt-e-suitable-existence.
Source: Aschbacher--Smith 14.6.24(3), printed p.1041.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped commutatorElement MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
open Chapter13.Section08 Chapter13.Section08.SourceCompletion
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open BinaryLinearThree.NaturalDual
variable {G E : Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

/-- The opposite point cannot lie in an actual natural three-space whose
support stabilizer has index at most two. The lower and upper Sylow bounds
refer to the same literal common point centralizer. -/
theorem source_placedEndpoint_point_not_le_natural_support
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
    (a : N) (ha : m.left a ∉ MulAut.innerSubgroup BinaryLinearThree.Group)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (eKplus : (Kplus ⧸ pCore 2 Kplus) ≃* BinaryLinearThree.Group)
    (A W : Subgroup G) (hAM : A ≤ Mc) (hindex : A.relIndex Mc ∣ 2)
    (f : A →* SL(3,ZMod 2)) (hf : Function.Surjective f)
    (d : BinaryConjugationSection A W (centralInvolutions T) ((specialLinearNatural 3).comp f)) :
    ¬ p.endpoint.conjugate (centralInvolutions T) ≤ W := by
  intro hpoint
  let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let Zg := p.endpoint.conjugate (centralInvolutions T)
  have hZg : Nat.card Zg = 2 :=
    (card_map_of_injective (MulAut.conj p.endpoint.representative).injective).trans h.point_card
  have hne : Zg ≠ ⊥ := by
    intro he
    rw [he] at hZg
    simp at hZg
  obtain ⟨z,hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hz1 : (z : G) ≠ 1 := fun he => hz (Subtype.ext he)
  have hzZ : (z : G) ∉ centralInvolutions T := by
    intro hh
    have hd := OrbitMatching.source_critical_points_disjoint
      hG T hempty hM hunique hmany hcard e hab p.endpoint
    exact hz1 (show (z : G) ∈ (⊥ : Subgroup G) from hd ▸ ⟨hh,z.property⟩)
  have hMc : Mc = centralizer (centralInvolutions T : Set G) :=
    (source_lemma_14_1_18 hG T hempty hM hunique hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨S,hSC,hS,hu⟩ := d.linearThree_point_large_two_subgroup
    T Mc A W (centralInvolutions T) h.T_le_H hAM hindex f hf
    (hAM.trans_eq hMc) h.point_card ⟨z,hpoint z.property⟩ hzZ
  have hzpow : (z : G) ^ 2 = 1 := by
    have hh := congrArg Subtype.val (pow_card_eq_one' (x := z))
    rwa [hZg] at hh
  have hgen : Zg = zpowers (z : G) :=
    (eq_of_le_of_card_ge (zpowers_le.mpr z.property) (by
      rw [hZg,Nat.card_zpowers,orderOf_eq_prime hzpow hz1])).symm
  have hSC' : S ≤ centralizer
      (((centralInvolutions T) ⊔ Zg : Subgroup G) : Set G) := by
    apply le_centralizer_iff.mp
    refine sup_le (le_centralizer_iff.mp ((hSC.trans inf_le_left).trans_eq hMc)) ?_
    apply le_centralizer_iff.mp
    rw [hgen,zpowers_eq_closure,centralizer_closure]
    exact hSC.trans inf_le_right
  have hl := source_placedEndpoint_common_two_subgroup_bound
    hG T hempty hM hunique hmany hcard e hab K Kplus p hKM hKplusM hcomp hcompPlus
    hcross c N m hN hperm κ₁ κ₂ hκrange₁ hκrange₂ hl₁ hr₁ hl₂ hr₂
    hpair hZ₁ hZ₂ hS₁ hS₂ hK hKplus a ha eK eKplus S hS hSC'
  have hspos : 0 < Nat.card S := Nat.card_pos
  omega
end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
