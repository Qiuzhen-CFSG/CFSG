module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourOrdinary

/-!
# The original span embeds in the ordinary-component quotient

The original normal point residual L₁ contains U and lies in every ordinary
component B of the escaping involution centralizer. If an element of U dies
in B/O₂(B), it is central in B and hence centralizes O₂(L₁). The original
core pairing places it in V₁. The nonidentity generator of V₁ cannot be
central in B: its ambient centralizer lies in H, whereas B escapes H.
Thus the literal map U → B → B/O₂(B) is injective. Since U is elementary
abelian of order 128, this gives two-rank at least seven in that same quotient.

Source: Aschbacher–Smith 14.7.16, 14.7.21 and 14.7.26, printed
pp.1048–1053, refs/quasithin.pdf. This uses the original ambient flag;
it is not an assertion about arbitrary intrinsic Heisenberg actions.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open ClassificationModels Chapter1.Section02.LocalModels
open Chapter15.Section03.Candidates.ComponentStructure

open Representation Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08
open scoped IsMulCommutative Pointwise commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original order-128 span embeds through the literal ordinary-component
quotient: its intersection with the central two-core is trivial. -/
theorem extraspecial_four_ordinary_span_embedding
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (B : Subgroup (centralizer ({x} : Set G)))
    (hB : IsComponent (centralizer ({x} : Set G)) B) :
    ∃ i : F.U →* B, (∀ u, ((i u : centralizer ({x} : Set G)) : G) = u) ∧
      Function.Injective ((QuotientGroup.mk' (pCore 2 B)).comp i) := by
  classical
  let C := centralizer ({x} : Set G)
  have hst := extraspecial_four_ordinary_structure
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  have hLB := hst.2.1
  have hzB := hst.2.2.2.1
  obtain ⟨hn,_,_⟩ := extraspecial_source_reduction h hab structural previous he
  have hUB := (U_le_pointResidual_of_normal h hn).trans hLB
  have hUC : F.U ≤ C := hUB.trans (map_subtype_le B)
  let i : F.U →* B := (inclusion hUC).codRestrict B (by
    intro u
    obtain ⟨b,hb,heq⟩ := hUB u.property
    exact (show b = inclusion hUC u from Subtype.ext heq) ▸ hb)
  have hival (u : F.U) : ((i u : C) : G) = u := rfl
  obtain ⟨_,_,z,hzo,hzp,P,_,h115⟩ := extraspecial_four_centralizer_source_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
  obtain ⟨_,houtB,_⟩ := Chapter1.lemma_1_1_5_three_knownSimple d.qtke C P F.H z h115 B hB
  obtain ⟨e⟩ := he
  have hfix := extraspecial_point_core_centralizer h hab structural previous
    ((HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm)
    ((Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3)))
    ((Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2)))
  refine ⟨i,hival,?_⟩
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro u hu
  have huZ : i u ∈ center B := by
    rw [hzB]
    exact (QuotientGroup.eq_one_iff _).mp hu
  have huC : (u : G) ∈ centralizer ((F.Li L 1).pCoreIn 2 : Set G) := by
    intro y hy
    obtain ⟨b,hb,rfl⟩ := hLB (pCoreIn_le 2 (F.Li L 1) hy)
    exact congrArg (fun b : B => ((b : C) : G)) (mem_center_iff.mp huZ ⟨b,hb⟩)
  have huV : (u : G) ∈ F.Vi 1 := hfix ▸ (show (u : G) ∈
    F.U ⊓ centralizer ((F.Li L 1).pCoreIn 2 : Set G) from ⟨u.property,huC⟩)
  rw [←hzp,mem_zpowers_iff_mem_range_orderOf,hzo] at huV
  obtain ⟨n,hn,heq⟩ := Finset.mem_image.mp huV
  have hn2 : n < 2 := Finset.mem_range.mp hn
  interval_cases n
  · exact mem_bot.mpr (Subtype.ext (by simpa using heq.symm))
  · have huz : (u : G) = z := by simpa using heq.symm
    apply (houtB ?_).elim
    rintro _ ⟨b,hb,rfl⟩
    apply h115.centralizer_le
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg (fun b : B => ((b : C) : G)) (mem_center_iff.mp huZ ⟨b,hb⟩)
    change (b : G) * (u : G) = (u : G) * (b : G) at hh
    change (b : G) * z = z * (b : G)
    simpa only [huz] using hh

/-- The actual ordinary-component quotient has two-rank at least seven. -/
theorem extraspecial_four_ordinary_twoRank
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (B : Subgroup (centralizer ({x} : Set G)))
    (hB : IsComponent (centralizer ({x} : Set G)) B) :
    7 ≤ primeRank 2 (B ⧸ pCore 2 B) := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨i,_,hi⟩ := extraspecial_four_ordinary_span_embedding
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  let j := (QuotientGroup.mk' (pCore 2 B)).comp i
  let : IsElementaryAbelian 2 j.range := IsElementaryAbelian.of_surjective
    j.rangeRestrict j.rangeRestrict_surjective
  have hc : Nat.card j.range = 2^7 :=
    (Nat.card_congr (MonoidHom.ofInjective hi).toEquiv).symm.trans
      (extraspecial_source_reduction h hab structural previous he).2.1
  exact IsElementaryAbelian.primeRank_ge_of_card j.range hc

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
