module
public import Theory.Representation.PSL3Two.PairedNaturalDual.CommonLine
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.PairedActions
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.Reversal
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.PlacedEndpoint

/-!
# Placement of the original critical point in a component support

The literal opposite-core denominator has index bounded by the selected
actor rank. Its common displacement line is the image of the original
critical point. Restricting both marked component actions to this same
actor permits the common-line kernel bound to place that line in one
support. The no-FF bound first puts the point in U; the original quotient
kernel then lifts the linear placement to actual subgroup containment.

The uniform result applies to every rank-compared endpoint, so the same
argument is available after the genuine F.9 reversal. No alternate point,
denominator, quotient action, or component support is chosen.

These are the point-placement claims of Aschbacher--Smith 14.6.24(3),
printed pp.1039--1040. The simultaneous support markings remain explicit
inputs to be constructed by qt-e-suitable-component-marking from the
14.6.20--23 inputs of qt-e-suitable-component-supports. This module does
not assert the subsequent component-pair exclusion. Final suitable-choice
assembly remains with qt-e-suitable-existence.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
open Chapter13.Section08 Chapter13.Section08.SourceCompletion
open BinaryLinearThree.NaturalDual
variable {G E : Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

/-- The literal critical point is in one of the two marked component supports. -/
theorem QuadraticEndpoint.point_le_one_of_paired_supports
    {D : ChapterF.Section09.Setup G} {h : D.Hypothesis}
    {ρ : Representation (ZMod 2) (Source.Hstar D.H) E}
    (p : QuadraticEndpoint h ρ) (hb : 3 ≤ h.b)
    (c : BinaryConjugationSection D.H D.UH D.V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 D.H))))
    (N : Subgroup (Source.Hstar D.H)) (m : Paired.Marking (ρ.comp N.subtype))
    (hAN : Source.starImage D.H (p.endpoint.conjugate D.UH) ≤ N)
    (S₁ S₂ : Subgroup G) (hZ₁ : D.V₁ ≤ S₁) (hZ₂ : D.V₁ ≤ S₂)
    (hS₁ : c.imageSpace S₁ = m.leftEmbedding.range)
    (hS₂ : c.imageSpace S₂ = m.rightEmbedding.range) :
    p.endpoint.conjugate D.V₁ ≤ S₁ ∨ p.endpoint.conjugate D.V₁ ≤ S₂ := by
  let s := criticalSection h c
  let Ug := p.endpoint.conjugate D.UH
  let Zg := p.endpoint.conjugate D.V₁
  let Dh := commutatorPreimage D.UH Ug Zg
  let A := Source.starImage D.H Ug
  let : IsElementaryAbelian 2 A := p.member.1.2
  let : IsElementaryAbelian 2 (⊤ : Subgroup A) :=
    IsElementaryAbelian.of_injective (⊤ : Subgroup A).subtype (⊤ : Subgroup A).subtype_injective
  let τ := ρ.comp A.subtype
  let mA : Paired.Marking τ := m.comp (inclusion hAN)
  have hf : Function.Injective τ := (f9_section_faithful _ h s).comp A.subtype_injective
  have huv : D.UH ≤ D.VH := conjugateSpanBy_mono h.plus_le le_rfl
  have hUgH : Ug ≤ D.H := (map_mono huv).trans (p.endpoint.large_le hb)
  have hUZg : D.UH ≤ normalizer (Zg : Set G) := by
    have hn := map_mono (f := (MulAut.conj p.endpoint.representative).toMonoidHom)
      (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    rw [map_equiv_normalizer_eq] at hn
    exact huv.trans ((p.endpoint.reverse_le hb).trans hn)
  have hUgZg : Ug ≤ centralizer (Zg : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    change ⁅D.UH.map _,D.V₁.map _⁆ = ⊥
    rw [←map_commutator,commutator_eq_bot_iff_le_centralizer.mpr
      (h.UH_le_H.trans h.H_centralizes),Subgroup.map_bot]
  have hn : Ug ≤ normalizer (Dh : Set G) :=
    commutatorPreimage_normalized _ _ _ _ hUZg (hUgH.trans s.normalizes)
      Ug.le_normalizer (hUgZg.trans (Subgroup.centralizer_le_normalizer _))
  let W : Subrepresentation τ := {
    toSubmodule := s.image Dh
    apply_mem_toSubmodule := by
      rintro ⟨b,hb⟩ v hv
      obtain ⟨a,ha,rfl⟩ := hb
      obtain ⟨u,hu,rfl⟩ := (s.mem_image Dh v).mp hv
      change ρ (QuotientGroup.mk' (pCore 2 D.H) a) (s.quotient u).toAdd ∈ s.image Dh
      rw [s.conjugates]
      exact ⟨_,(mem_normalizer_iff.mp (hn ha) u).mp hu,rfl⟩ }
  have hzcard : Nat.card Zg = 2 :=
    (card_map_of_injective (MulAut.conj p.endpoint.representative).injective).trans h.point_card
  obtain ⟨hdim,hdisp⟩ := s.critical_line_displacement Ug Zg hUZg hzcard
  have hfixed : ∀ a : A, ∀ z ∈ s.image Zg, τ a z = z := by
    rintro ⟨b,hb⟩ z hz
    obtain ⟨a,ha,rfl⟩ := hb
    obtain ⟨u,hu,rfl⟩ := (s.mem_image Zg z).mp hz
    apply sub_eq_zero.mp
    change ρ (QuotientGroup.mk' (pCore 2 D.H) a) (s.quotient u).toAdd -
      (s.quotient u).toAdd = 0
    rw [s.displacement]
    apply (s.quotient_eq_zero_iff _).mpr
    have hc : ⁅(a : G),(u : G)⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr ((hUgZg ha) u hu).symm
    change ⁅(a : G),(u : G)⁆ ∈ D.V₁
    rw [hc]
    exact D.V₁.one_mem
  have hdenom : Module.finrank (ZMod 2) (E ⧸ W.toSubmodule) =
      Nat.log 2 ((D.UH ⊓ p.endpoint.conjugate D.QH).relIndex D.UH) := by
    change Module.finrank (ZMod 2) (E ⧸ s.image Dh) = _
    rw [s.quotient_finrank Dh (s.line_le_DH Ug Zg hUgH)]
    exact congrArg (fun B : Subgroup G => Nat.log 2 (B.relIndex D.UH))
      (p.endpoint.denominators h hb).1
  have hcmp : Module.finrank (ZMod 2) (E ⧸ W.toSubmodule) ≤ Nat.log 2 (Nat.card A) := by
    rw [hdenom]
    exact p.comparison
  have hpos : 0 < Nat.log 2 (Nat.card A) := p.positive.trans_le p.comparison
  have htoprank : rank (⊤ : Subgroup A) = Nat.log 2 (Nat.card A) :=
    congrArg (Nat.log 2) (Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A).toEquiv)
  have hstrict : Nat.log 2 (Nat.card A) < fixedCodim τ ⊤ := by
    apply Nat.lt_of_not_ge
    intro hh
    apply mA.not_ff hf
    refine ⟨⊤,⟨?_,inferInstance⟩,?_⟩
    · intro he
      rw [he,Representation.BinaryOffender.rank_bot] at htoprank
      omega
    · rwa [htoprank]
  have hpointU : Zg ≤ D.UH := by
    by_contra hn
    have he := s.image_eq_bot_of_not_le Zg hzcard hn
    have hw : W.toSubmodule ≤ fixedSpace τ ⊤ := by
      intro v hv a
      have hd := hdisp a a.val.property v hv
      rw [he,Submodule.mem_bot] at hd
      exact sub_eq_zero.mp hd
    have hh := Submodule.finrank_mono hw
    have hc := fixedCodim_add_finrank τ ⊤
    have hw' := W.toSubmodule.finrank_quotient_add_finrank
    omega
  have hplace := mA.line_le_one_of_supports hf hpos W (s.image Zg) hdim
    (fun a v hv => hdisp a a.property v hv) hfixed hcmp
  have hlift (S : Subgroup G) (hZS : D.V₁ ≤ S)
      (himage : s.image Zg ≤ s.image S) : Zg ≤ S := by
    intro z hz
    exact (s.quotient_mem_image_iff S hZS ⟨z,hpointU hz⟩).mp
      (himage ((s.mem_image Zg _).mpr ⟨⟨z,hpointU hz⟩,hz,rfl⟩))
  rcases hplace with hl | hr
  · exact Or.inl (hlift S₁ hZ₁ (by change s.image Zg ≤ c.imageSpace S₁; rw [hS₁]; exact hl))
  · exact Or.inr (hlift S₂ hZ₂ (by change s.image Zg ≤ c.imageSpace S₂; rw [hS₂]; exact hr))
end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents

namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
open Chapter13.Section08 Chapter13.Section08.SourceCompletion
open BinaryLinearThree.NaturalDual
variable {G E : Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

/-- Uniform placement includes the reversed endpoint in the equal-rank branch. -/
theorem pairPointPlacement_of_paired_supports
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    (hplus : D.Vplus = D.V) (hb : 3 ≤ h.b) [IsElementaryAbelian 2 D.UH]
    {ρ : Representation (ZMod 2) (Source.Hstar D.H) E}
    (c : BinaryConjugationSection D.H D.UH D.V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 D.H))))
    (N : Subgroup (Source.Hstar D.H)) (m : Paired.Marking (ρ.comp N.subtype))
    (hN : N = subspaceStabilizer ρ m.leftEmbedding.range ⊓
      subspaceStabilizer ρ m.rightEmbedding.range)
    (hspan : m.leftEmbedding.range ⊔ m.rightEmbedding.range ⊔ fixedSpace ρ ⊤ = ⊤)
    (hperm : ∀ a : Source.Hstar D.H,
      (m.leftEmbedding.range.map (ρ a) = m.leftEmbedding.range ∧
        m.rightEmbedding.range.map (ρ a) = m.rightEmbedding.range) ∨
      (m.leftEmbedding.range.map (ρ a) = m.rightEmbedding.range ∧
        m.rightEmbedding.range.map (ρ a) = m.leftEmbedding.range))
    (K Kplus : Subgroup G) (hZ₁ : D.V₁ ≤ ⁅D.UH,K⁆) (hZ₂ : D.V₁ ≤ ⁅D.UH,Kplus⁆)
    (hS₁ : c.imageSpace ⁅D.UH,K⁆ = m.leftEmbedding.range)
    (hS₂ : c.imageSpace ⁅D.UH,Kplus⁆ = m.rightEmbedding.range) :
    PairPointPlacement h K Kplus := by
  intro i _ hcmp
  let p := quadraticEndpointOfComparison h i hb hplus c hcmp
  exact p.point_le_one_of_paired_supports hb c N m
    (p.le_pair_stabilizer hb c N m hN hspan hperm)
    _ _ hZ₁ hZ₂ hS₁ hS₂

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- Original 14.6.24's mixed-support branch, retaining H=Mc and the literal
component commutators. The statement applies uniformly after reversal. -/
theorem source_pairPointPlacement_of_paired_supports
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
    (K Kplus : Subgroup G)
    (hZ₁ : centralInvolutions T ≤ ⁅conjugateSpanBy (localModule T M) Mc,K⁆)
    (hZ₂ : centralInvolutions T ≤ ⁅conjugateSpanBy (localModule T M) Mc,Kplus⁆)
    (hS₁ : c.imageSpace ⁅conjugateSpanBy (localModule T M) Mc,K⁆ = m.leftEmbedding.range)
    (hS₂ : c.imageSpace ⁅conjugateSpanBy (localModule T M) Mc,Kplus⁆ = m.rightEmbedding.range) :
    PairPointPlacement
      (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab) K Kplus := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,Mc⟩
  let h : D.Hypothesis := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let : IsElementaryAbelian 2 D.UH :=
    h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  obtain ⟨hb,_,_⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hunique hmany hcard e hab
    Mc (ComponentSupports.terminal_outside hG T hempty hM hunique hmany hcard e)
  exact pairPointPlacement_of_paired_supports h rfl hb c N m hN hspan hperm
    K Kplus hZ₁ hZ₂ hS₁ hS₂
end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents

