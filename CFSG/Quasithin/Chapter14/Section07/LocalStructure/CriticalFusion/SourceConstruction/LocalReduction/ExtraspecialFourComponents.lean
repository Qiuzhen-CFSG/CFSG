module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourThreeCore
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwoSource

/-!
# The component divisible by three in the original overgroup

Every C-component of G₀ whose order is divisible by three contains the
original L₁: the two-perfect Y and L₁ normalize it by the proved source
orbit theorem, so the common cubic and its normal generation apply.
In a strict outside-centralizer overgroup, there is at most one such
component. Distinct components commute modulo the literal two-core;
their common cubic would then lie in O₃(G₀/O₂(G₀)), already proved trivial.
Conjugation preserves the prime divisor, so this component is normal.

These are the component containment, uniqueness and normality reductions
in Aschbacher–Smith 14.7.26, printed p.1053, refs/quasithin.pdf. Existence,
the characteristic-two-overgroup exclusions, the automorphism restrictions
and the final outside-centralizer containment still require proof.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Subgroup Representation Theory.GroupTheory
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08
open scoped IsMulCommutative Pointwise commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Every actual C-component of the overgroup whose order is divisible by three contains the original point residual. -/
theorem extraspecial_four_component_contains_point
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
    (hND : normalizer (D : Set G) = F.H)
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) ≤ G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (B : Subgroup G₀) (hB : B.IsCComponent) (hd : 3 ∣ Nat.card B) :
    F.Li L 1 ≤ B.map G₀.subtype := by
  obtain ⟨Y,hYK,_,_,⟨e⟩,_,_,hcontains⟩ := extraspecial_four_point_containment
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
  have hKC : K F ≤ centralizer ({x} : Set G) := by
    rw [map_center_subtype_eq_inf_centralizer] at hDK
    intro k hk
    exact mem_centralizer_singleton_iff.mpr ((hDK hx).2 k hk)
  have hKG : K F ≤ G₀ := (le_inf (K_le_H F) hKC).trans hJG
  have hYG := hYK.trans hKG
  have hLG : F.Li L 1 ≤ G₀ := (pointResidual_le F).trans hKG
  have hC := (extraspecial_four_centralizer_source_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ).1
  have hG : IsSQTK KnownSimple.IsKnownSimple G₀ :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hGC)).mp
      (hC.subgroup (G₀.subgroupOf (centralizer ({x} : Set G))))
  have hQ : IsSQTK KnownSimple.IsKnownSimple (G₀ ⧸ pCore 2 G₀) := by
    refine ⟨?_,hG.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hG.stronglyQuasithin p hp ho)
  have hYperfect : IsPPerfect 2 Y := by
    apply (pResidual_eq_top_iff 2 Y).mp
    apply top_unique
    intro a _
    apply mem_pResidual_of_orderOf_coprime
    apply Nat.Coprime.of_dvd_right (orderOf_dvd_natCard a)
    rw [Nat.card_congr e.toEquiv,HeisenbergPrime.card]
    decide
  have normalizes (A : Subgroup G) (hAG : A ≤ G₀) (hA : IsPPerfect 2 A) :
      A ≤ normalizer (B.map G₀.subtype : Set G) := by
    have hp := hA.of_surjective (subgroupOfEquivOfLe hAG).symm.toMonoidHom
      (subgroupOfEquivOfLe hAG).symm.surjective
    have hn := Chapter1.Section02.twoPerfect_normalizes_cComponent_source hQ hB hp
    have hm := (map_mono (f := G₀.subtype) hn).trans (B.le_normalizer_map G₀.subtype)
    simpa only [map_subgroupOf_eq_of_le hAG] using hm
  exact hcontains _ ((map_subtype_le _).trans hGC)
    (normalizes Y hYG hYperfect)
    (normalizes (F.Li L 1) hLG (isPPerfect_embedded_pResidual 2 (L ⊓ F.H)))
    (by rw [card_map_of_injective G₀.subtype_injective]; exact hd)

/-- The actual overgroup has at most one C-component divisible by three. -/
theorem extraspecial_four_component_unique
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
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (B C : Subgroup G₀) (hB : B.IsCComponent) (hC : C.IsCComponent)
    (hdB : 3 ∣ Nat.card B) (hdC : 3 ∣ Nat.card C) : B = C := by
  by_contra hne
  let q := QuotientGroup.mk' (pCore 2 G₀)
  let B₀ := B.map q
  let C₀ := C.map q
  have h3 := extraspecial_four_threeCore_eq_bot
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC
  have hCen := (extraspecial_four_centralizer_source_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ).1
  have hG : IsSQTK KnownSimple.IsKnownSimple G₀ :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hGC)).mp
      (hCen.subgroup (G₀.subgroupOf (centralizer ({x} : Set G))))
  have hQ : IsSQTK KnownSimple.IsKnownSimple (G₀ ⧸ pCore 2 G₀) := by
    refine ⟨?_,hG.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hG.stronglyQuasithin p hp ho)
  let := (pCore_isPGroup (p := 2) (G := G₀)).isNilpotent
  have hBC := ChapterA.Section03.CComponentCommutation.commutator_eq_bot hQ
    (pCore_quotient_pCore_eq_bot 2) (hB.map_quotient (pCore 2 G₀))
    (hC.map_quotient (pCore 2 G₀))
    (fun hh => hne (hB.eq_of_map_quotient_eq hC (pCore 2 G₀) hh))
  have hLB := extraspecial_four_component_contains_point
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
    G₀ hJG.le hGC B hB hdB
  have hLC := extraspecial_four_component_contains_point
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
    G₀ hJG.le hGC C hC hdC
  obtain ⟨Y,_,_,_,_,hc,_⟩ := extraspecial_four_three_sylow_center
    d h hab structural previous faithful earlier he
  let X := Y ⊓ F.Li L 1
  have hXG : X ≤ G₀ := (inf_le_right.trans hLB).trans (map_subtype_le _)
  let X₀ := X.subgroupOf G₀
  have hXcard : Nat.card X₀ = 3 := (Nat.card_congr (subgroupOfEquivOfLe hXG).toEquiv).trans hc
  have hXp : IsPGroup 3 X₀ := IsPGroup.of_card (n := 1) (by rw [hXcard]; decide)
  have hXB : X₀ ≤ B := by
    have hh := comap_mono (f := G₀.subtype) (inf_le_right.trans hLB : X ≤ B.map G₀.subtype)
    rw [comap_map_eq_self_of_injective G₀.subtype_injective] at hh
    exact hh
  have hXC : X₀ ≤ C := by
    have hh := comap_mono (f := G₀.subtype) (inf_le_right.trans hLC : X ≤ C.map G₀.subtype)
    rw [comap_map_eq_self_of_injective G₀.subtype_injective] at hh
    exact hh
  have hZN : B₀ ≤ normalizer (X₀.map q : Set (G₀ ⧸ pCore 2 G₀)) :=
    ((commutator_eq_bot_iff_le_centralizer.mp hBC).trans
      (centralizer_le (map_mono (f := q) hXC))).trans (Subgroup.centralizer_le_normalizer _)
  have hZ3 : X₀.map q ≤ pCore 3 (G₀ ⧸ pCore 2 G₀) :=
    (le_pCoreIn_of_normalizes (hXp.map q) (map_mono (f := q) hXB) hZN).trans
      (pCoreIn_le_of_subnormal 3 (hB.subnormal.map (QuotientGroup.mk'_surjective _)))
  have hZbot : X₀.map q = ⊥ := le_bot_iff.mp (hZ3.trans h3.le)
  have hXtwo : X₀ ≤ pCore 2 G₀ := by
    simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff X₀).mp hZbot
  have hp2 : IsPGroup 2 X₀ := (pCore_isPGroup (p := 2) (G := G₀)).to_le hXtwo
  rcases hp2.card_eq_or_dvd with h1 | hd
  · rw [hXcard] at h1
    omega
  · rw [hXcard] at hd
    norm_num at hd

/-- The C-component divisible by three is normal in the original overgroup. -/
theorem extraspecial_four_component_normal
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
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (B : Subgroup G₀) (hB : B.IsCComponent) (hdB : 3 ∣ Nat.card B) : B.Normal := by
  apply normal_iff_map_conj_eq.mpr
  intro g
  exact extraspecial_four_component_unique
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC (B.map (MulAut.conj g).toMonoidHom) B (hB.map_equiv (MulAut.conj g)) hB
    (by rw [card_map_of_injective (MulAut.conj g).injective]; exact hdB) hdB

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
