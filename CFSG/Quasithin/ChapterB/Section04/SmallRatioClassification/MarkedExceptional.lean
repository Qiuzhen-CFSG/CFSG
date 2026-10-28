module
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Domain
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.HigherRecognition.EvenTwisted.Triality.Inner.Complete
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.HigherRecognition.EvenTwisted.Triality.Outer.Source
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.Source
public import Theory.SpecificGroups.ReeF4.AlmostSimpleTwoElements
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.AbelianFrobeniusDisplacement
public import Theory.Representation.BinaryOffender.CubicRatio.Equivariant
public import Theory.Representation.RepEquiv
/-!
# Exceptional source exclusions from the original small involution

Every involution on an original triality chief action moves more than 5n
binary dimensions. The inner bound applies through the actual central cover;
outer actors are handled by their action on the component commutant and the
proved paired-tensor estimate. In a Ree action, the original two-element lies
in the component and moves at least 10(2m+1) dimensions. Both contradict the
retained chief-image involution with displacement rank at most two.

Finite binary coordinates align the coefficient and vector-space universes
required by the existing source bounds. The transported action retains
faithfulness, component irreducibility, cubic ratio and exact displacement;
the public endpoints apply to the original module in any universe.

Source: Aschbacher–Smith B.4.5 and K.3, printed pp.87,453–457;
Guralnick–Malle II, Lemmas 8.6 and 8.8. These are specialized exclusions for
the actual marked chief action, with no FF or absolute-irreducibility premise.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SmallRatioClassification
universe u
variable {G : Type u} {V : Type} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

set_option backward.isDefEq.respectTransparency false in
private theorem triality_excluded_coordinates
    (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (n : ℕ) (hn : 0 < n)
    (hm : _root_.Triality.Standard.IsTrialityGroupAt (2^n) (L ⧸ center L))
    (t : G) (ht : orderOf t = 2)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) ≤ 2) : False := by
  let := h.quasisimple
  let := h.layer_normal
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  have ht1 : t ≠ 1 := by intro he; simp [he] at ht
  have ht2 : t^2=1 := by rw [←ht];exact pow_orderOf_eq_one t
  change Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) ≤ 2 at hr
  have hb : 5*n < Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) := by
    by_cases htL : t ∈ L
    · have hi := ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.Triality.componentInvolutionBound_source
        n hn hm (ZMod 2) V (ρ.comp L.subtype) h.irreducible
        (h.faithful.comp L.subtype_injective) ⟨t,htL⟩
        (fun hh => ht1 (congrArg Subtype.val hh)) (Subtype.ext ht2)
      simpa only [Module.finrank_self,mul_one,one_mul,MonoidHom.comp_apply,Subgroup.subtype_apply] using hi
    · by_cases hc : Representation.CentralizesCommutant ρ L t
      · have hh := ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.Triality.source_ratio_of_centralizesCommutant
          L n hn hm ρ h.faithful t htL ht2 hc
        have hd := ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.Triality.displacement_gt_of_ratio
          L ρ h.faithful n hn hm t hh
        simpa only [Module.finrank_self,one_mul] using hd
      · have hd := ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.Triality.displacement_gt_of_not_centralizesCommutant
          L ρ h.faithful n hn hm t hc
        simpa only [Module.finrank_self,one_mul] using hd
  omega

private theorem reeF4_excluded_coordinates
    (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {m : ℕ} (hm : 1 ≤ m) (e : L ⧸ center L ≃* _root_.ReeF4.Model m)
    (t : G) (ht : orderOf t = 2)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) ≤ 2) : False := by
  let := h.quasisimple
  let := h.layer_normal
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  have ht1 : t ≠ 1 := by intro he; simp [he] at ht
  have ht2 : t^2=1 := by rw [←ht];exact pow_orderOf_eq_one t
  have htL := _root_.ReeF4.twoPower_mem_of_generalizedFitting L hm h.fitting e t 1
    (by simpa only [pow_one] using ht2)
  let tL : L := ⟨t,htL⟩
  have hb := _root_.ReeF4.FixedSpaceEstimate.coverInvolutionBound_source hm
    L ⟨e⟩ (ZMod 2) V (ρ.comp L.subtype) h.irreducible
    (h.faithful.comp L.subtype_injective) tL
    (fun hh => ht1 (congrArg Subtype.val hh)) (Subtype.ext ht2)
  simp only [Module.finrank_self,one_mul] at hb
  have hc : Module.finrank (ZMod 2)
      (V ⧸ invariants ((ρ.comp L.subtype).comp (zpowers tL).subtype)) =
      Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) := by
    rw [←ker_sub_one_eq_cyclic_invariants]
    exact (LinearMap.quotKerEquivRange (ρ t - 1)).finrank_eq
  rw [hc] at hb
  omega
end CFSG.Quasithin.ChapterB.SmallRatioClassification
namespace CFSG.Quasithin.ChapterB.SmallRatioClassification
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

private theorem exists_binary_coordinates (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (t : G) (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) ≤ 2) :
    ∃ d : ℕ,∃ σ : Representation (ZMod 2) G (Fin d → ZMod 2),
      ChapterK.RankOne.SourceHypotheses σ L ∧
      Module.finrank (ZMod 2) (LinearMap.range (σ t - 1)) ≤ 2 := by
  let e := (Module.finBasis (ZMod 2) V).equivFun
  let σ : Representation (ZMod 2) G (Fin (Module.finrank (ZMod 2) V) → ZMod 2) :=
    e.conjRingEquiv.toMonoidHom.comp ρ
  have he : ∀ g v,e (ρ g v) = σ g (e v) := by
    intro g v
    change e (ρ g v) = e (ρ g (e.symm (e v)))
    rw [e.symm_apply_apply]
  let eL : RepEquiv (ρ.comp L.subtype) (σ.comp L.subtype) := {
    toLinearEquiv := e
    isIntertwining' := by intro g;apply LinearMap.ext;intro v;exact he g v }
  have hi := (RepEquiv.irreducible_euqiv eL).mp h.irreducible
  have hc := cubicRatio_le_nat_of_equivariant ρ σ (MonoidHom.id G)
    Function.injective_id e he 2 h.smallCubic
  refine ⟨_,σ,⟨h.sqtk,h.fitting,h.quasisimple,e.conjRingEquiv.injective.comp h.faithful,hi,hc⟩,?_⟩
  have hd := fixedCodim_map_equivariant ρ σ (MonoidHom.id G) e he (zpowers t)
  rw [Subgroup.map_id,fixedCodim_zpowers_eq_displacement_rank,
    fixedCodim_zpowers_eq_displacement_rank] at hd
  change Module.finrank (ZMod 2) (LinearMap.range (σ t - LinearMap.id)) ≤ 2
  change Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) ≤ 2 at hr
  omega

theorem triality_excluded_of_small_involution
    (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (n : ℕ) (hn : 0 < n)
    (hm : _root_.Triality.Standard.IsTrialityGroupAt (2^n) (L ⧸ center L))
    (t : G) (ht : orderOf t = 2)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) ≤ 2) : False := by
  obtain ⟨d,σ,hσ,hrσ⟩ := exists_binary_coordinates h t hr
  exact triality_excluded_coordinates hσ n hn hm t ht hrσ

theorem reeF4_excluded_of_small_involution
    (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {m : ℕ} (hm : 1 ≤ m) (e : L ⧸ center L ≃* _root_.ReeF4.Model m)
    (t : G) (ht : orderOf t = 2)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) ≤ 2) : False := by
  obtain ⟨d,σ,hσ,hrσ⟩ := exists_binary_coordinates h t hr
  exact reeF4_excluded_coordinates hσ hm e t ht hrσ
end CFSG.Quasithin.ChapterB.SmallRatioClassification
