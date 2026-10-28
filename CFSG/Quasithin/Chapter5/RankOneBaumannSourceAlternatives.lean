module
public import CFSG.Quasithin.Chapter5.RankOneBaumannSourceSylow
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.CompleteSource
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.RankOneComparison
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Stellmacher.BaumannMap

/-!
# The actual five-point section forced by a rank-one Baumann escape

The original reduced W supplies the minimal-parabolic FF action on LT.
The complete earlier classifier gives natural single or paired factors.
The actual rank-one quotient bounds the three-rank by one, excluding paired
factors. The natural branch gives a Baumann Sylow subgroup and is eliminated
by the Sylow-invariant normalizer theorem. Hence an escaping normalizer
produces the genuine S5 action on the original commutator module, retaining
its equivariant quotient and its precise fixed-space kernel.

This constructs the remaining action input, not the A5 crossing-core
contradiction. Source: Aschbacher--Smith 5.1.2 and 5.1.7(1), pp.630,633.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}
attribute [local instance] ChapterB.RankOneBaumann.semilinear_moved_elementary

/-- The residual in the source join is the original L. -/
theorem Input.local_residual_eq (h : Input KnownSimple.IsKnownSimple T L W n) :
    (pResidual 2 (L ⊔ (T : Subgroup G) : Subgroup G)).map (L ⊔ (T : Subgroup G)).subtype = L :=
  embedded_pResidual_join_pGroup L (T : Subgroup G)
    h.local_mem.2.2.1 T.isPGroup' h.sylow_normalizes

/-- The moved module in the intrinsic FF theorem maps to the original [W,L]. -/
theorem Input.local_moved_map (h : Input KnownSimple.IsKnownSimple T L W n) :
    (⁅W.subgroupOf (L ⊔ (T : Subgroup G)),pResidual 2 (L ⊔ (T : Subgroup G) : Subgroup G)⁆).map
      (L ⊔ (T : Subgroup G)).subtype = ⁅W,L⁆ := by
  rw [map_commutator, map_subgroupOf_eq_of_le h.reduced.1, h.local_residual_eq]

private theorem local_three_rank (h : Input KnownSimple.IsKnownSimple T L W n) :
    primeRank 3 (L ⊔ (T : Subgroup G) : Subgroup G) ≤ 1 := by
  let H := L ⊔ (T : Subgroup G)
  rw [← ResidualCentralizerRank.primeRank_residual (by decide : Nat.Coprime 2 3)]
  let e : (pResidual 2 H) ≃* L :=
    (equivMapOfInjective (pResidual 2 H) H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr h.local_residual_eq)
  rw [primeRank_congr 3 e]
  exact Chapter4.Section03.RankOneUniqueness.odd_primeRank_le_one h.linear (by decide)

/-- All natural and paired alternatives are discharged on the original input.
The remaining marker is the literal original commutator's natural S5 section. -/
theorem Input.five_section_of_baumann_escape
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G)) :
    let H := L ⊔ (T : Subgroup G)
    let U := W.subgroupOf H
    letI := h.reduced_internal.normal
    letI := h.reduced_internal.elementary
    let V := ⁅U,pResidual 2 H⁆
    ∃ p : H →* Equiv.Perm (Fin 5), ∃ hp : Function.Surjective p,
      ∃ hk : p.ker = centralizer (V : Set H),
      ∃ f : Additive V →ₗ[ZMod 2] BinaryPermutation.core (Fin 5),
      Function.Surjective f ∧
      (∀ g v, f (NormalElementaryQuotient.representation V p hp hk g v) =
        BinaryPermutation.coreRepresentation (Fin 5) g (f v)) ∧
      f.ker = fixedSpace (NormalElementaryQuotient.representation V p hp hk)
        ((pResidual 2 H).map p) := by
  classical
  let H := L ⊔ (T : Subgroup G)
  let U := W.subgroupOf H
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let := h.reduced_internal.normal
  let := h.reduced_internal.elementary
  have hSQ : IsSQTK KnownSimple.IsKnownSimple H := by
    have hHM : H ≤ normalizer (L : Set G) := sup_le L.le_normalizer h.sylow_normalizes
    exact (IsSQTK.equiv (subgroupOfEquivOfLe hHM)).mp
      ((h.qtke.twoLocal_sqtk h.maximal.1).subgroup (H.subgroupOf (normalizer (L : Set G))))
  have hns : ¬ Group.IsSolvable H := by
    intro hs
    let := hs
    exact Chapter1.mem_L_not_isSolvable h.maximal_local.1
      (Group.isSolvable_of_isSolvable_injective
        (inclusion_injective (show L ≤ H from le_sup_left)))
  have hj : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G) := by
    intro hj
    let := h.quotient_quasisimple
    exact hout (Chapter5.RankOneBaumannSource.baumann_normalizer_of_thompson_centralizes
      h.qtke h.maximal_local h.sylow_normalizes h.reduced.1 h.reduced_internal
      h.quotient_center_eq_bot h.noncentral hj)
  have hSm : (S : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hjm : (elementaryAbelianMaxJ (S : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective, hSm]
  have hjS : ¬ elementaryAbelianMaxJ (S : Subgroup H) ≤ centralizer (U : Set H) := by
    intro hc
    apply hj
    rw [← hjm]
    rintro _ ⟨x,hx,rfl⟩ v hv
    exact congrArg H.subtype (hc hx ⟨v,h.reduced.1 hv⟩ hv)
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  rcases ChapterE.ThompsonAction.source_nonsolvable_natural_factors
      hSQ S h.local_minimal_parabolic U h.reduced_internal hns hjS with
    ⟨hqs,c,hlin|hfive⟩ | ⟨d,_,_⟩
  · obtain ⟨F,hF⟩ := hlin
    have hs := (ChapterE.ThompsonAction.quasisimple_linear_baumann_of_section
      S h.local_minimal_parabolic U h.reduced_internal hjS q hq hk hqs c.sectionData F hF).1
    have hb : (ChapterB.baumann (S : Subgroup H)).map H.subtype =
        ChapterB.baumann (T : Subgroup G) := by
      simpa only [ChapterB.baumann, ChapterB.thompsonAlpha, hSm] using
        baumann_map_injective H.subtype H.subtype_injective (S : Subgroup H)
    have hs' := (Chapter1.IsSylowIn.map_iff H.subtype H.subtype_injective).mpr hs
    rw [Subgroup.map_sup, hb, h.local_residual_eq] at hs'
    exact (hout (h.baumann_normalizer_of_baumann_sylow hs')).elim
  · obtain ⟨e⟩ := hfive
    exact ChapterE.ThompsonAction.quasisimple_five_source_marker
      S h.local_minimal_parabolic U h.reduced_internal hjS q hq hk hqs c.sectionData e
  · let P : Sylow 3 H := Classical.choice inferInstance
    have hr : primeRank 3 (H ⧸ C) ≤ 1 :=
      P.primeRank_quotient_le_one (P.isCyclic_of_odd_of_primeRank_le_one
        (by decide) (local_three_rank h)) C
    have hy := (primeRank_subgroup_le 3 (offenderSubgroup α)).trans hr
    have hd := d.two_le_three_rank
    change 2 ≤ primeRank 3 (offenderSubgroup α) at hd
    omega

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
