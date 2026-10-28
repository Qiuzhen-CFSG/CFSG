module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.OppositeMovement
public import Theory.Representation.PSL3Two.PairedNaturalDual.PerfectNormalizer
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.Containment

/-!
# Aligning the opposite component at the placed endpoint

Pull the original U and opposite component Kplus through the literal
quotient Mc^g/O₂(Mc^g) and the canonical inverse conjugation isomorphism.
The denominator comparison makes the image of U nontrivial of order at
most four. The opposite-movement bound puts it in the common component
stabilizer; perfectness puts Kplus there too. Since Kplus normalizes U,
the paired perfect-normalizer theorem places its image in one factor.
Perfect quotient lifting then gives Kplus ≤ K^g or Kplus ≤ Kplus^g.

The source application derives Kplus ≤ Mc^g from the placed point and
cross-centralization, retaining H=Mc and the original left conjugator.
The component embeddings and simultaneous action markings remain genuine
14.6.20--23 support inputs. Their construction, exclusion of equality,
and the subsequent Sylow contradiction remain with
qt-e-suitable-component-marking; final suitable-choice assembly remains
with qt-e-suitable-existence. This module does not assert the completed
14.6.24(3) exclusion.
Source: Aschbacher--Smith 14.6.24(3), printed p.1040.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
open Chapter13.Section08 Chapter13.Section08.CriticalGeometry
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences
open BinaryLinearThree.NaturalDual
variable {G E : Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

omit [Finite G] in
private theorem starImage_normalizes {H A B : Subgroup G}
    (hn : B ≤ normalizer (A : Set G)) :
    Source.starImage H B ≤ normalizer (Source.starImage H A : Set (Source.Hstar H)) := by
  have hh : B.subgroupOf H ≤ normalizer (A.subgroupOf H : Set H) :=
    (comap_mono hn).trans (A.le_normalizer_comap H.subtype)
  exact (map_mono hh).trans ((A.subgroupOf H).le_normalizer_map (QuotientGroup.mk' (pCore 2 H)))

private theorem perfect_subgroupOf {X : Type*} [Group X]
    (A N : Subgroup X) [Group.IsPerfect A] (hAN : A ≤ N) : Group.IsPerfect (A.subgroupOf N) :=
  Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hAN).symm.toMonoidHom)
    (subgroupOfEquivOfLe hAN).symm.surjective

/-- The perfect opposite component lies in one of the two literal conjugate
components. The diagonal possibility is discharged by the actual small actor. -/
theorem placedEndpoint_component_alignment
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    (K Kplus : Subgroup G) (p : PlacedEndpoint h K Kplus)
    (hb : 3 ≤ h.b) [IsElementaryAbelian 2 D.UH]
    (hKM : K ≤ D.H) (hKplusM : Kplus ≤ D.H)
    (hcomp : (K.subgroupOf D.H).IsCComponent)
    (hcompPlus : (Kplus.subgroupOf D.H).IsCComponent)
    (hHg : Kplus ≤ p.endpoint.conjugate D.H)
    {ρ : Representation (ZMod 2) (Source.Hstar D.H) E}
    (c : BinaryConjugationSection D.H D.UH D.V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 D.H))))
    (N : Subgroup (Source.Hstar D.H)) (m : Paired.Marking (ρ.comp N.subtype))
    (hN : N = subspaceStabilizer ρ m.leftEmbedding.range ⊓
      subspaceStabilizer ρ m.rightEmbedding.range)
    (hperm : ∀ a : Source.Hstar D.H,
      (m.leftEmbedding.range.map (ρ a) = m.leftEmbedding.range ∧
        m.rightEmbedding.range.map (ρ a) = m.rightEmbedding.range) ∨
      (m.leftEmbedding.range.map (ρ a) = m.rightEmbedding.range ∧
        m.rightEmbedding.range.map (ρ a) = m.leftEmbedding.range))
    (κ₁ κ₂ : BinaryLinearThree.Group →* N)
    (hκrange₁ : (N.subtype.comp κ₁).range = Source.starImage D.H K)
    (hκrange₂ : (N.subtype.comp κ₂).range = Source.starImage D.H Kplus)
    (hl₁ : ∀ k, m.left (κ₁ k) = MulAut.conj k)
    (hr₁ : ∀ k, m.right (κ₁ k) = 1)
    (hl₂ : ∀ k, m.left (κ₂ k) = 1)
    (hr₂ : ∀ k, m.right (κ₂ k) = MulAut.conj k) :
    Kplus ≤ p.endpoint.conjugate K ∨ Kplus ≤ p.endpoint.conjugate Kplus := by
  let i := p.endpoint
  let Hg := i.conjugate D.H
  let e := starEquiv (MulAut.conj i.representative) D.H
  let Abar := Source.starImage Hg D.UH
  let Bbar := Source.starImage Hg Kplus
  let A := Abar.map e.symm.toMonoidHom
  let B := Bbar.map e.symm.toMonoidHom
  have hUH : D.UH ≤ Hg := (conjugateSpanBy_mono h.plus_le le_rfl).trans (i.reverse_le hb)
  have hcard : Nat.card A = (D.UH ⊓ i.conjugate D.QH).relIndex D.UH := by
    change Nat.card (Abar.map e.symm.toMonoidHom) = _
    rw [card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective]
    rw [starImage_card Hg D.UH hUH]
    have hQ : Source.QH Hg = i.conjugate D.QH := by
      exact AmalgamLocalCores.pCoreIn_map_of_injective 2
        (MulAut.conj i.representative).toMonoidHom (MulAut.conj i.representative).injective D.H
    rw [hQ,inf_relIndex_left]
  let : IsElementaryAbelian 2 Abar := starImage_isElementaryAbelian Hg D.UH hUH
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hsmall : Nat.card A ≤ 4 := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
    have hr : n ≤ 2 := by
      have hc := p.comparison.trans p.rank_le_two
      rw [←hcard,hn,Nat.log_pow (by decide : 1 < 2)] at hc
      exact hc
    rw [hn]
    exact (Nat.pow_le_pow_right (by decide) hr)
  have hnon : A ≠ ⊥ := by
    intro he
    have hc := p.positive
    rw [←hcard,he] at hc
    simp at hc
  let : Group.IsPerfect (Kplus.subgroupOf D.H) := hcompPlus.perfect
  let : Group.IsPerfect Kplus := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKplusM).toMonoidHom) (subgroupOfEquivOfLe hKplusM).surjective
  let : Group.IsPerfect (Kplus.subgroupOf Hg) := perfect_subgroupOf Kplus Hg hHg
  let : Group.IsPerfect Bbar := Group.IsPerfect.map (QuotientGroup.mk' (pCore 2 Hg))
  let : Group.IsPerfect B := Group.IsPerfect.map e.symm.toMonoidHom
  have hBN : B ≤ N := by
    rw [hN]
    exact Paired.perfect_le_pair_stabilizer ρ _ _ hperm B
  have hAN : A ≤ N := by
    rw [hN]
    have hdim : 3 < Module.finrank (ZMod 2) m.leftEmbedding.range := by
      rw [←(LinearEquiv.ofInjective m.leftEmbedding m.left_injective).finrank_eq]
      change 3 < Module.finrank (ZMod 2) (BinaryLinearThree.Vector ×
        Module.Dual (ZMod 2) BinaryLinearThree.Vector)
      rw [Module.finrank_prod,Subspace.dual_finrank_eq]
      norm_num [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
    have hs := endpoint_opposite_preserves_pair h i hb c p.rank_le_two
      _ _ m.disjoint hdim hperm
    rintro _ ⟨a,ha,rfl⟩
    have hh := hs a ha
    exact ⟨(subspace_map_eq_iff ρ _ _).mp hh.1,(subspace_map_eq_iff ρ _ _).mp hh.2⟩
  have hnorm : B ≤ normalizer (A : Set (Source.Hstar D.H)) := by
    have hn : Kplus ≤ normalizer (D.UH : Set G) :=
      hKplusM.trans (le_normalizer_conjugateSpanBy _ _)
    have hs : Bbar ≤ normalizer (Abar : Set (Source.Hstar Hg)) := starImage_normalizes hn
    exact (map_mono hs).trans (Abar.le_normalizer_map e.symm.toMonoidHom)
  let : Group.IsPerfect (B.subgroupOf N) := perfect_subgroupOf B N hBN
  have hnormN : B.subgroupOf N ≤ normalizer (A.subgroupOf N : Set N) :=
    (comap_mono hnorm).trans (A.le_normalizer_comap N.subtype)
  have hnonN : A.subgroupOf N ≠ ⊥ := by
    intro hz
    have := map_subgroupOf_eq_of_le hAN
    rw [hz,Subgroup.map_bot] at this
    exact hnon this.symm
  have hcN : Nat.card (A.subgroupOf N) ≤ 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAN).toEquiv]
    exact hsmall
  have hf := Chapter13.Section08.SourceCompletion.f9_section_faithful D h (criticalSection h c)
  have halign := m.perfect_normalizer_le_factor (hf.comp N.subtype_injective)
    (A.subgroupOf N) (B.subgroupOf N) hnonN hcN hnormN κ₁ κ₂ hl₁ hr₁ hl₂ hr₂
  have lift (J : Subgroup G) (hJM : J ≤ D.H)
      (hJ : (J.subgroupOf D.H).IsCComponent)
      (κ : BinaryLinearThree.Group →* N)
      (hκ : (N.subtype.comp κ).range = Source.starImage D.H J)
      (hle : B.subgroupOf N ≤ κ.range) : Kplus ≤ i.conjugate J := by
    have him : B ≤ Source.starImage D.H J := by
      have hh := map_mono (f := N.subtype) hle
      rw [map_subgroupOf_eq_of_le hBN,MonoidHom.map_range,hκ] at hh
      exact hh
    have him' : Bbar ≤ Source.starImage Hg (i.conjugate J) := by
      have hh := map_mono (f := e.toMonoidHom) him
      have he : B.map e.toMonoidHom = Bbar := by
        change (Bbar.map e.symm.toMonoidHom).map e.toMonoidHom = Bbar
        rw [map_map]
        have hm : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := by
          apply MonoidHom.ext
          intro x
          exact e.apply_symm_apply x
        rw [hm,Subgroup.map_id]
      rw [he,starImage_map] at hh
      exact hh
    exact perfect_le_relative_cComponent_of_twoCore_image_le Hg Kplus (i.conjugate J)
      hHg (map_mono hJM) (hJ.map_relative_equiv D.H J hJM (MulAut.conj i.representative)) him'
  exact halign.imp (lift K hKM hcomp κ₁ hκrange₁)
    (lift Kplus hKplusM hcompPlus κ₂ hκrange₂)

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- In the original terminal setup the placed point puts the opposite
component in Mc^g; the proved small-actor argument then aligns it with an
actual conjugate component. No quotient-alignment premise remains. -/
theorem source_placedEndpoint_component_alignment
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
    (hr₂ : ∀ k, m.right (κ₂ k) = MulAut.conj k) :
    Kplus ≤ p.endpoint.conjugate K ∨ Kplus ≤ p.endpoint.conjugate Kplus := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,Mc⟩
  let h : D.Hypothesis := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let : IsElementaryAbelian 2 D.UH :=
    h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  obtain ⟨hb,_,_⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hunique hmany hcard e hab
    Mc (ComponentSupports.terminal_outside hG T hempty hM hunique hmany hcard e)
  have hMc : Mc = centralizer (centralInvolutions T : Set G) :=
    (source_lemma_14_1_18 hG T hempty hM hunique hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hHg : Kplus ≤ p.endpoint.conjugate Mc := le_conjugate_of_point_support
    Mc (centralInvolutions T) _ Kplus hMc p.endpoint.representative p.point_support
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcross))
  exact placedEndpoint_component_alignment h K Kplus p hb hKM hKplusM hcomp hcompPlus
    hHg c N m hN hperm κ₁ κ₂ hκrange₁ hκrange₂ hl₁ hr₁ hl₂ hr₂

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
