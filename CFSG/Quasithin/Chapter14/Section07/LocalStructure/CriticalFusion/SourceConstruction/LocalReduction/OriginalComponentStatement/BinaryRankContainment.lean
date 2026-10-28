module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Source.SolvableConclusion
public import Theory.SpecificGroups.BinaryComponentResidual
public import Theory.SpecificGroups.Alternating.SevenComponent
public import Theory.GroupTheory.CComponent.CenterlessRankNormal
public import Theory.GroupTheory.TwoPerfectCubicKernel

/-!
# Original point containment in the binary rank-two component rows

The actual component quotient has trivial center, cubic rank at least two,
and a two-group of outer automorphisms. The ambient cubic rank bound first
forces component normality, then makes its index prime to three. Every
two-perfect cubic section is therefore contained in it, in particular the
original point residual. This works at the same original G,T and does not
use the component statement 14.7.47 as an input.

Source: Aschbacher–Smith 14.7.47(1), printed p.1064, and A.3.18,
printed pp.51–53, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Theory.SpecificGroups.BinaryComponentResidual
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem twoPerfect_cubic_le_of_coprime_index
    {D : Type*} [Group D] [Finite D] (A C : Subgroup D) [C.Normal]
    (hp : IsPPerfect 2 A) (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (hi : Nat.Coprime 3 C.index) : A ≤ C := by
  by_contra hout
  let f := (QuotientGroup.mk' C).comp A.subtype
  have hf : f ≠ 1 := by
    intro he
    apply hout
    intro a ha
    exact (QuotientGroup.eq_one_iff a).mp (DFunLike.congr_fun he (⟨a,ha⟩ : A))
  have hk := f.kernel_isTwoGroup_of_twoPerfect_cubic hp hc hf
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' 3
    (hc ▸ card_quotient_dvd_card (pCore 2 A))
  have hfx : f x = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes hi
    · exact (orderOf_dvd_of_pow_eq_one (by rw [←map_pow,←hx,pow_orderOf_eq_one,map_one]))
    · exact _root_.orderOf_dvd_natCard (f x)
  have ho := hk.orderOf_coprime (by decide : Nat.Coprime 2 3) (⟨x,hfx⟩ : f.ker)
  have he : orderOf (⟨x,hfx⟩ : f.ker) = 3 :=
    (f.ker.orderOf_coe ⟨x,hfx⟩).symm.trans hx
  rw [he] at ho
  norm_num at ho

/-- The rank and outer-action facts force containment for an actual original
component. Normality is proved rather than supplied. -/
theorem local_rank_two_component_contains_point_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (hfacts : Facts (C ⧸ pCore 2 C)) : F.Li L 1 ≤ C.map I.subtype := by
  let := WholeResidualAssembly.GuardedSource.local_component_twoCore_isQuasisimple
    h hab structural previous faithful I hI C hC
  have hrI : primeRank 3 I ≤ 2 := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 I) pCore_isPGroup]
    exact (local_star_sqtk h I hI).stronglyQuasithin 3 (by decide) (by decide)
  let : C.Normal := hC.normal_of_centerless_core_threeRank hfacts.1 hfacts.2.1 hrI
  have ho : Nat.Coprime 3 (Nat.card (MulAut.Outer (C ⧸ pCore 2 C))) := by
    obtain ⟨n,hn⟩ := hfacts.2.2.exists_card_dvd_pow
    exact ((by decide : Nat.Coprime 3 2).pow_right n).coprime_dvd_right hn
  have hi := cComponent_index_coprime_three_of_quotient C hC hfacts.1 hfacts.2.1 hrI ho
  let A := (F.Li L 1).subgroupOf I
  have hAI := F.Li_one_le_of_mem_Hz hI
  let ea := subgroupOfEquivOfLe hAI
  have hp : IsPPerfect 2 A := (isPPerfect_embedded_pResidual 2 _).of_surjective
    ea.symm.toMonoidHom ea.symm.surjective
  have hc : Nat.card (A ⧸ pCore 2 A) = 3 := by
    rw [Nat.card_congr (QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)).toEquiv]
    exact pointResidual_core_quotient_card_at h structural
  have hh := map_mono (f := I.subtype) (twoPerfect_cubic_le_of_coprime_index A C hp hc hi)
  rwa [map_subgroupOf_eq_of_le hAI] at hh

/-- The original point lies in every binary linear-four or linear-five component. -/
theorem local_binary_linear_component_contains_point_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : (C ⧸ pCore 2 C) ≃* SL(n,ZMod 2)) : F.Li L 1 ≤ C.map I.subtype :=
  local_rank_two_component_contains_point_at h hab structural previous faithful I hI C hC
    (Facts.of_equiv e (linear hn))

/-- The original point lies in every alternating-six or alternating-seven component. -/
theorem local_binary_alternating_component_contains_point_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) {n : ℕ} (hn : n = 6 ∨ n = 7)
    (e : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin n)) : F.Li L 1 ≤ C.map I.subtype := by
  apply local_rank_two_component_contains_point_at h hab structural previous faithful I hI C hC
  apply Facts.of_equiv e
  rcases hn with rfl | rfl
  · exact alternatingSix
  · exact ⟨alternatingGroup.center_eq_bot (by simp),
      alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide),
      alternatingGroup.SevenComponent.outer_two⟩

/-- The original point lies in every actual G₂(2)′ component. -/
theorem local_binary_gTwo_component_contains_point_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    F.Li L 1 ≤ C.map I.subtype :=
  local_rank_two_component_contains_point_at h hab structural previous faithful I hI C hC
    (Facts.of_equiv e g2)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
