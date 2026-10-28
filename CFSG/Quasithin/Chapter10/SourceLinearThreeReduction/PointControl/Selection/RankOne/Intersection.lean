module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.RankOne.PointNormalizers

/-!
# Point control through the intersection of the original moved factors

The maximal local subgroup permutes the two moved factors. Their intersection
is therefore normal in that local subgroup, and original 1.2.7 uniqueness
controls its full ambient normalizer whenever the intersection is nontrivial.
A point fixer that interchanges the components places its point in this
intersection. If the intersection has order at most two, its nonidentity
point has centralizer inside the same maximal local subgroup.

Together with the rank-one Baumann calculation this gives point-Sylow control
for every escaping opposite point, including points fixed by L₀. The two
individual fixed kernels can be larger, and no half-Sylow input is needed for
this implication. This does not assert stabilization of the entire fixed layer
or a bound on the intersection from the general source hypotheses.
The selected-module application is in ModuleChoice.Source.

Source: Aschbacher--Smith, 10.1.1 and the point-Sylow argument in10.2.9,
printed pp.741 and750, with uniqueness from1.2.7, pp.505--507.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.Selection
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

private theorem moved_pair_conjugation
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    {m : G} (hm : m ∈ D.maximalLocal) :
    let W := ⁅D.fullModule,L⁆
    let U := W.map (MulAut.conj t).toMonoidHom
    (W.map (MulAut.conj m).toMonoidHom = W ∧ U.map (MulAut.conj m).toMonoidHom = U) ∨
    (W.map (MulAut.conj m).toMonoidHom = U ∧ U.map (MulAut.conj m).toMonoidHom = W) := by
  dsimp only
  let W := ⁅D.fullModule,L⁆
  let U := W.map (MulAut.conj t).toMonoidHom
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hne : U ≠ W := by
    intro he
    have hc : W ≤ centralizer (L : Set G) := he ▸ hcross
    exact source_full_moved_ne_bot D ((source_full_moved_eq_commutator D).symm.trans
      (commutator_eq_bot_iff_le_centralizer.mpr hc))
  have hmap (s : G) (hs : s ∈ D.maximalLocal) :
      W.map (MulAut.conj s).toMonoidHom = W ∨ W.map (MulAut.conj s).toMonoidHom = U := by
    have hV : D.fullModule.map (MulAut.conj s).toMonoidHom = D.fullModule :=
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule hs)
    have htV : D.fullModule.map (MulAut.conj t).toMonoidHom = D.fullModule :=
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule
        (le_normalizer_componentOrbit L T ht))
    dsimp only [W,U]
    rw [map_commutator,hV,map_commutator,htV]
    exact (source_nonnormal_maximal_pair D hn ht htn s hs).imp
      (congrArg (fun A => ⁅D.fullModule,A⁆)) (congrArg (fun A => ⁅D.fullModule,A⁆))
  have hU : U.map (MulAut.conj m).toMonoidHom = W ∨ U.map (MulAut.conj m).toMonoidHom = U := by
    have he : U.map (MulAut.conj m).toMonoidHom = W.map (MulAut.conj (m*t)).toMonoidHom := by
      dsimp only [U]
      rw [map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply,mul_assoc]
    rw [he]
    exact hmap (m*t) (D.maximalLocal.mul_mem hm (le_normalizer_componentOrbit L T ht))
  have hdistinct : U.map (MulAut.conj m).toMonoidHom ≠ W.map (MulAut.conj m).toMonoidHom :=
    fun he => hne (map_injective (MulAut.conj m).injective he)
  rcases hmap m hm with hW | hW
  · exact Or.inl ⟨hW,hU.resolve_left (fun he => hdistinct (he.trans hW.symm))⟩
  · exact Or.inr ⟨hW,hU.resolve_right (fun he => hdistinct (he.trans hW.symm))⟩

/-- The original maximal local subgroup preserves the intersection of its two moved factors. -/
theorem moved_intersection_normalized
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    D.maximalLocal ≤ normalizer
      (↑(⁅D.fullModule,L⁆ ⊓ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) : Set G) := by
  intro m hm
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (⁅D.fullModule,L⁆ ⊓ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom).map
    (MulAut.conj m).toMonoidHom = _
  rw [map_inf _ _ _ (MulAut.conj m).injective]
  rcases moved_pair_conjugation D ht htn hcross hm with ⟨hW,hU⟩ | ⟨hW,hU⟩
  · rw [hW,hU]
  · rw [hW,hU,inf_comm]

/-- A nonzero intersection has its entire ambient normalizer inside the original M. -/
theorem moved_intersection_normalizer_le
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hne : ⁅D.fullModule,L⁆ ⊓ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≠ ⊥) :
    normalizer (↑(⁅D.fullModule,L⁆ ⊓
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) : Set G) ≤ D.maximalLocal := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  exact normalizer_le_of_unique_maximalTwoLocal (D.lemma_3_2_3_uniqueness hu).2.2
    ((source_original_full_moved_elementary D).isPGroup.to_le inf_le_left) hne
    ((sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)).trans
      (moved_intersection_normalized D ht htn hcross))

/-- If an original point fixer interchanges the components, the point belongs to both moved factors. -/
theorem partner_point_mem_moved_of_exchanging_fixer
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    {v m : G} (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hm : m ∈ D.maximalLocal) (hmn : m ∉ normalizer (L : Set G))
    (hmv : m ∈ centralizer ({v} : Set G)) : v ∈ ⁅D.fullModule,L⁆ := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hL := (source_nonnormal_maximal_pair D hn ht htn m hm).resolve_left
    (fun he => hmn (mem_normalizer_iff_map_conj_eq.mpr he))
  have hW : (⁅D.fullModule,L⁆).map (MulAut.conj m).toMonoidHom =
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom := by
    have hVm : D.fullModule.map (MulAut.conj m).toMonoidHom = D.fullModule :=
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule hm)
    have hVt : D.fullModule.map (MulAut.conj t).toMonoidHom = D.fullModule :=
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule
        (le_normalizer_componentOrbit L T ht))
    rw [map_commutator,hVm,hL,map_commutator,hVt]
  have hne : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≠ ⁅D.fullModule,L⁆ := by
    intro he
    have hc : ⁅D.fullModule,L⁆ ≤ centralizer (L : Set G) := he ▸ hcross
    exact source_full_moved_ne_bot D ((source_full_moved_eq_commutator D).symm.trans
      (commutator_eq_bot_iff_le_centralizer.mpr hc))
  have hU := (moved_pair_conjugation D ht htn hcross hm).resolve_left
    (fun h => hne (hW.symm.trans h.1)) |>.2
  have hv' := mem_map_of_mem (MulAut.conj m).toMonoidHom hv
  rw [hU] at hv'
  have he : (MulAut.conj m) v = v := by
    change m*v*m⁻¹=v
    rw [mem_centralizer_singleton_iff.mp hmv,mul_inv_cancel_right]
  simpa only [MulEquiv.coe_toMonoidHom,he] using hv'

/-- Outside the common intersection, the full local point centralizer fixes the original component. -/
theorem partner_point_stabilizes_of_not_mem_intersection
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    {v : G} (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hout : v ∉ ⁅D.fullModule,L⁆ ⊓ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) :
    D.maximalLocal ⊓ centralizer ({v} : Set G) ≤ normalizer (L : Set G) := by
  intro m hm
  by_contra hmn
  exact hout ⟨partner_point_mem_moved_of_exchanging_fixer D ht htn hcross hv hm.1 hmn hm.2,hv⟩

/-- An order-two common intersection controls its nonidentity point using original uniqueness. -/
theorem intersection_point_centralizer_le_of_small_intersection
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hcard : Nat.card (⁅D.fullModule,L⁆ ⊓
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom : Subgroup G) ≤ 2)
    {v : G} (hv : v ∈ ⁅D.fullModule,L⁆ ⊓ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hvne : v ≠ 1) : centralizer ({v} : Set G) ≤ D.maximalLocal := by
  let I := ⁅D.fullModule,L⁆ ⊓ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom
  have hne : I ≠ ⊥ := fun he => hvne (mem_bot.mp (he ▸ hv))
  have hi : Nat.card I = 2 := by
    change Nat.card I ≤ 2 at hcard
    have := (one_lt_card_iff_ne_bot I).mpr hne
    omega
  have hz : zpowers v = I := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr hv)
    have hn : zpowers v ≠ ⊥ := fun he => hvne (mem_bot.mp (he ▸ mem_zpowers v))
    have := (one_lt_card_iff_ne_bot (zpowers v)).mpr hn
    omega
  rw [show centralizer ({v} : Set G) = centralizer (I : Set G) by
    rw [←hz,zpowers_eq_closure,centralizer_closure]]
  exact (Subgroup.centralizer_le_normalizer _).trans
    (moved_intersection_normalizer_le D ht htn hcross hne)

/-- Every escaping opposite point distinguishes the two components when their common intersection is small. -/
theorem partner_point_stabilizes_of_small_intersection
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hcard : Nat.card (⁅D.fullModule,L⁆ ⊓
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom : Subgroup G) ≤ 2)
    {v : G} (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hvne : v ≠ 1) (hout : ¬ centralizer ({v} : Set G) ≤ D.maximalLocal) :
    D.maximalLocal ⊓ centralizer ({v} : Set G) ≤ normalizer (L : Set G) :=
  partner_point_stabilizes_of_not_mem_intersection D ht htn hcross hv
    (fun hi => hout (intersection_point_centralizer_le_of_small_intersection D ht htn hcross hcard hi hvne))

namespace RankOne
/-- Literal rank-one point control when the common intersection is small; neither moved kernel is bounded. -/
theorem pointSylowControl_of_small_intersection
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hmodel : RankOneNatural D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hcard : Nat.card (⁅D.fullModule,L⁆ ⊓
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom : Subgroup G) ≤ 2) : PointSylowControl D t := by
  intro v hv hvne hout hs
  exact ⟨(point_sylow_normalizer_and_sylow D hna hmodel ht htn hv hs).1,
    (inf_le_inf (le_normalizer_componentOrbit L T) le_rfl).trans
      (partner_point_stabilizes_of_small_intersection D ht htn hcross hcard hv hvne hout)⟩

/-- In particular, disjoint moved factors give point control in every field degree, even with large fixed kernels. -/
theorem pointSylowControl_of_disjoint_moved
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hmodel : RankOneNatural D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hdis : Disjoint ⁅D.fullModule,L⁆ ((⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)) :
    PointSylowControl D t :=
  pointSylowControl_of_small_intersection D hna hmodel ht htn hcross (by
    rw [hdis.eq_bot,Subgroup.card_bot]; decide)
end RankOne
end CFSG.Quasithin.Chapter10.PointControl.Selection
