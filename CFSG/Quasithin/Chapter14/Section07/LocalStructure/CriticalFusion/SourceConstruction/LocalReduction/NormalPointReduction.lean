module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NormalPoint
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.LinearThreeCore
public import CFSG.Quasithin.Chapter14.Section03.Prelim.ThompsonSource.Marking
public import Theory.GroupTheory.Commutator.SmallNormalizedImage

/-!
# The normal-point source reduction before residual classification

For the original point normalizer, normality of L₁ gives a cubic star image.
If O₂(H) centralized the flag plane, the earlier natural-action reduction
13.3.14(c) would put a nontrivial two-core in that cubic image. Thus the
plane is moved, and its commutator with O₂(H) is exactly the original point.
The full three-space marking then identifies QQ_H with R₁ and preserves
that identity under the literal star map.

The neighborhood-kernel argument in CriticalSelection constructs a reverse
critical path from any nontrivial original star actor. The normal-point
cubic supplies this nontriviality; choosing an orientation and applying the
exact original section kernel gives a quadratic two-offender, its actual
reciprocal index bound, and even displacement for every actor.

The applications discharge these local geometric inputs both under the
source's star-normality antecedent and when the actual K/O₂(K) is abelian.
The full earlier 12.2.13 escape and Structural1222 remain explicit. The
noncyclic solvable exclusions, larger-field reductions and component sieve
through 14.7.52 remain separate work in the same source assembly.

Source: Aschbacher–Smith, 13.3.14(c), pp.891–892; 14.7.4(1),(4),
14.7.5 and Notation 14.7.1, printed pp.1043–1044; F.9.16–17, pp.323–324.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

omit [Finite G] in
private theorem core_le_sylow (H : Subgroup G) (hT : (T : Subgroup G) ≤ H) :
    H.pCoreIn 2 ≤ (T : Subgroup G) :=
  (pCoreIn_le_sylow H (T.subtype hT)).trans_eq (map_subgroupOf_eq_of_le hT)

omit [Finite G] in
/-- The LT two-core lies in the point-parabolic two-core. -/
private theorem core_product_Q_le_Ri (F : InvariantFlag T V 3) : Q T L ≤ F.Ri L 1 := by
  have hQ := core_le_sylow (L ⊔ (T : Subgroup G)) le_sup_right
  have hle : Rechoice.group F L ≤ L ⊔ (T : Subgroup G) := Rechoice.group_le_LT
  exact (le_inf (hQ.trans le_sup_right) le_rfl).trans (inf_pCoreIn_le_of_le 2 hle)

omit [Finite G] in
/-- The H two-core lies in the same point-parabolic two-core. -/
private theorem core_product_QH_le_Ri (F : InvariantFlag T V 3) : F.H.pCoreIn 2 ≤ F.Ri L 1 := by
  have hQ := core_le_sylow F.H (F.invariant 1)
  exact (le_inf (hQ.trans le_sup_right) le_rfl).trans
    (inf_pCoreIn_le_of_le 2 Rechoice.group_le_H)

/-- The original two-cores generate the point-parabolic two-core. -/
theorem core_product_of_plane_movement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ ≤ F.Vi 1)
    (hmove : ¬ F.H.pCoreIn 2 ≤ centralizer (F.Vi 2 : Set G)) :
    Q T L ⊔ F.H.pCoreIn 2 = F.Ri L 1 := by
  let J := L ⊔ (T : Subgroup G)
  let R := (F.Ri L 1).subgroupOf J
  let N := (F.H.pCoreIn 2).subgroupOf J
  let D := (F.Li L 1).subgroupOf J
  have hRJ : F.Ri L 1 ≤ J := (pCoreIn_le 2 _).trans Rechoice.group_le_LT
  have hNJ : F.H.pCoreIn 2 ≤ J := (core_le_sylow F.H (F.invariant 1)).trans le_sup_right
  have hDJ : F.Li L 1 ≤ J := (F.Li_le L 1).trans (inf_le_left.trans le_sup_left)
  obtain ⟨e,q,hq,hq2,ha,hker,hT,hR⟩ :=
    Chapter14.Section03.ThompsonSource.exists_marking h F structural
  have hkerMap : q.ker.map J.subtype = Q T L := by
    rw [hker, subgroupOf_map_subtype, inf_comm]
    exact h.centralizer_LT structural
  have hNle : N.map q ≤ Matrix.PSL3Two.MarkedAutomorphisms.pointV := by
    rw [←hR]
    exact map_mono (subgroupOf_mono J (core_product_QH_le_Ri F))
  have hn : D ≤ normalizer (N : Set J) := by
    intro a ha
    apply mem_normalizer_iff.mpr
    intro x
    change (x : G) ∈ F.H.pCoreIn 2 ↔
      (a : G) * (x : G) * (a : G)⁻¹ ∈ F.H.pCoreIn 2
    exact mem_normalizer_iff.mp
      ((F.H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H)))
          ((F.Li_le L 1 ha).2)) _
  have hlarge : 2 < Nat.card (N.map q) := by
    by_contra hc
    have hDN := commutator_le_ker_of_normalized_image_card_le_two q D N hn (by omega)
    have hDNQ : ⁅F.Li L 1,F.H.pCoreIn 2⁆ ≤ Q T L := by
      have hh := map_mono (f := J.subtype) hDN
      rw [map_commutator, map_subgroupOf_eq_of_le hDJ,
        map_subgroupOf_eq_of_le hNJ, hkerMap] at hh
      exact hh
    have hQV : Q T L ≤ centralizer (V : Set G) := by
      change (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ _
      rw [← h.centralizer_LT structural]
      exact inf_le_right
    have hpoint : F.H ≤ centralizer (F.Vi 1 : Set G) :=
      normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))
    have h1 : ⁅⁅F.Li L 1,F.H.pCoreIn 2⁆,V⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (hDNQ.trans hQV)
    have h2 : ⁅⁅F.H.pCoreIn 2,V⁆,F.Li L 1⁆ = ⊥ := by
      apply commutator_eq_bot_iff_le_centralizer.mpr
      have hp : ⁅F.H.pCoreIn 2,V⁆ ≤ F.Vi 1 := by
        rw [commutator_comm]
        exact (commutator_mono (le_conjugateSpanBy V F.H) le_rfl).trans hcomm
      exact hp.trans (le_centralizer_iff.mp ((F.Li_le L 1).trans (inf_le_right.trans hpoint)))
    have hz := commutator_commutator_eq_bot_of_rotate h1 h2
    rw [← seed_commutator h F] at hz
    exact hmove ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)).trans
      (centralizer_le (F.le_seed 2)))
  have hc : Nat.card (N.map q) = 4 := by
    have hd := card_dvd_of_le hNle
    rw [Matrix.PSL3Two.MarkedAutomorphisms.card_pointV] at hd
    have hb := Nat.le_of_dvd (by decide : 0 < 4) hd
    interval_cases h : Nat.card (N.map q) <;> norm_num [h] at *
  have he : N.map q = R.map q := by
    rw [hR]
    exact eq_of_le_of_card_ge hNle (by rw [hc, Matrix.PSL3Two.MarkedAutomorphisms.card_pointV])
  have hRN : R ≤ N ⊔ q.ker := by
    rw [←comap_map_eq]
    exact (map_le_iff_le_comap).mp he.ge
  have hh := map_mono (f := J.subtype) hRN
  rw [map_subgroupOf_eq_of_le hRJ, Subgroup.map_sup, map_subgroupOf_eq_of_le hNJ, hkerMap] at hh
  exact le_antisymm (sup_le (core_product_Q_le_Ri F) (core_product_QH_le_Ri F)) (by simpa [sup_comm] using hh)


/-- The literal star quotient kills Q_H and preserves the product identity. -/
theorem core_product_star_of_plane_movement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ ≤ F.Vi 1)
    (hmove : ¬ F.H.pCoreIn 2 ≤ centralizer (F.Vi 2 : Set G)) :
    star F (Q T L) = star F (F.Ri L 1) := by
  have he := congrArg (fun A : Subgroup G => star F A)
    (core_product_of_plane_movement h structural hcomm hmove)
  change ((Q T L ⊔ F.H.pCoreIn 2).subgroupOf F.H).map (starMap F) = _ at he
  rw [subgroupOf_sup (Q_le_H F) (pCoreIn_le 2 F.H), Subgroup.map_sup] at he
  have hz : ((F.H.pCoreIn 2).subgroupOf F.H).map (starMap F) = ⊥ := by
    change (((pCore 2 F.H).map F.H.subtype).comap F.H.subtype).map (starMap F) = ⊥
    rw [comap_map_eq_self_of_injective F.H.subtype_injective,
      Subgroup.map_eq_bot_iff, starMap, QuotientGroup.ker_mk']
  simpa only [CriticalFusion.Source.star,hz,sup_bot_eq] using he


/-- The normal cubic image has trivial two-core, contradicting reduction
13.3.14(c) if the original H-core centralized the original plane. -/
theorem plane_moved_of_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    ¬ F.H.pCoreIn 2 ≤ centralizer (F.Vi 2 : Set G) := by
  intro hc
  have hne := Chapter13.Section03.Noncentrality.linearThree_star_core_ne_bot_of_plane_centralized
    h F (by rw [commutator_comm]; exact commutator_eq_bot_iff_le_centralizer.mpr hc)
  have he : Chapter13.Section03.Noncentrality.star F.H (F.Li L 1)
      ((F.Li_le L 1).trans inf_le_right) = star F (F.Li L 1) := by
    ext x
    constructor
    · rintro ⟨a,rfl⟩
      exact mem_map_of_mem (starMap F) a.property
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨a,ha⟩,rfl⟩
  rw [he] at hne
  have hp : IsPGroup 3 (star F (F.Li L 1)) :=
    IsPGroup.of_card (n := 1) (by simpa using pointResidual_star_card_of_normal h structural hn)
  apply hne
  exact le_bot_iff.mp ((le_inf le_rfl le_top).trans
    (pCore_isPGroup.disjoint_of_coprime (hp.to_subgroup ⊤)
      (by decide : Nat.Coprime 2 3)).le_bot)

/-- Source 14.7.5(2), with the literal two-cores and no recognition datum. -/
theorem core_product_of_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    Q T L ⊔ F.H.pCoreIn 2 = F.Ri L 1 ∧ star F (Q T L) = star F (F.Ri L 1) := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  have hc : ⁅F.U,F.H.pCoreIn 2⁆ ≤ F.Vi 1 := by
    rw [commutator_comm]
    exact section_core_commutator_le_point h s
  have hm := plane_moved_of_point_normal h structural hn
  exact ⟨core_product_of_plane_movement h structural hc hm,
    core_product_star_of_plane_movement h structural hc hm⟩

/-- The normal-point branch supplies the selected critical pair of
Notation 14.7.1, preserving the original actor and reciprocal core. -/
theorem exists_selected_critical_geometry_of_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
      star F c.Uα ≠ ⊥ ∧
      star F c.Uα ≤ centralizer (star F (F.Li L 1) : Set (HStar F.H)) := by
  obtain ⟨c,_,hc,_⟩ := exists_critical_geometry_of_point_normal h hab structural previous hn
  obtain ⟨a,ha⟩ := select_critical_orientation_of_nontrivial_star h structural c hc
  exact ⟨a,ha,critical_le_Ri h structural a,
    critical_star_nontrivial_of_point_normal h hab structural (h.flag_escape F previous) hn a,
    critical_actor_star_centralizes_of_point_normal h structural hn a⟩
open Representation.BinaryOffender
variable {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) F.H W}

/-- The normal-point branch constructs an actual quadratic two-offender,
using the original quotient, the literal index and exact centralizer kernel. -/
theorem exists_selected_critical_action_of_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) :
    ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
      star F c.Uα ≠ ⊥ ∧
      star F c.Uα ≤ centralizer (star F (F.Li L 1) : Set (HStar F.H)) ∧
      IsQuadratic ρ (c.Uα.subgroupOf F.H) ∧
      fixedCodim ρ (c.Uα.subgroupOf F.H) ≤ 2 * Nat.log 2 (Nat.card (star F c.Uα)) ∧
      ∀ a : F.H, (a : G) ∈ c.Uα →
        Even (Module.finrank (ZMod 2) (ρ a - LinearMap.id).range) ∧
        Module.finrank (ZMod 2) (ρ a - LinearMap.id).range ≤
          Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U) + 1 := by
  obtain ⟨c,hs,hplace,hne,hcent⟩ :=
    exists_selected_critical_geometry_of_point_normal h hab structural previous hn
  have hb := critical_fixedCodim_bounds_of_kernel h hab structural
    (section_action_kernel_eq_core_of_escape h structural (h.flag_escape F previous) s) s c
  refine ⟨c,hs,hplace,hne,hcent,critical_quadratic h hab s c,?_,?_⟩
  · have hh := hb.1
    have hr := hs.comparison
    omega
  · intro a ha
    exact ⟨point_core_displacement_even_of_normal h structural hn s a (hplace ha),hb.2 a ha⟩

/-- Source 14.7.4(1) in the normal-point branch, on the actual plane. -/
theorem plane_core_commutator_of_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    ⁅F.Vi 2,F.H.pCoreIn 2⁆ = F.Vi 1 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  have hc : ⁅F.U,F.H.pCoreIn 2⁆ ≤ F.Vi 1 := by
    rw [commutator_comm]
    exact section_core_commutator_le_point h s
  have hle : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≤ F.Vi 1 :=
    (commutator_mono ((F.le_seed 2).trans (le_conjugateSpanBy V F.H)) le_rfl).trans hc
  have hne : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥ := by
    intro he
    exact plane_moved_of_point_normal h structural hn
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he))
  apply eq_of_le_of_card_ge hle
  rw [show Nat.card (F.Vi 1) = 2 by simpa using F.card 1 (by decide)]
  exact (one_lt_card_iff_ne_bot _).mpr hne

/-- Apply all the normal-point reductions to source 14.7.5's literal
star-normality antecedent. These are the source clauses at the original G₁. -/
theorem normal_point_source_structure
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hstar : (star F (F.Li L 1)).Normal) :
    ⁅F.Vi 2,F.H.pCoreIn 2⁆ = F.Vi 1 ∧
      Q T L ⊔ F.H.pCoreIn 2 = F.Ri L 1 ∧
      Nat.card (star F (F.Li L 1)) = 3 ∧
      star F (Q T L) = star F (F.Ri L 1) ∧
      star F (F.Ri L 1) = star F (T : Subgroup G) ⊓
        centralizer (star F (F.Li L 1) : Set (HStar F.H)) ∧
      (star F (F.Ri L 1)).relIndex (star F (T : Subgroup G)) = 2 ∧
      ⁅F.U,F.Li L 1⁆ = F.U ∧
      ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
        star F c.Uα ≠ ⊥ ∧
        star F c.Uα ≤ centralizer (star F (F.Li L 1) : Set (HStar F.H)) := by
  have hn := pointResidual_normal_of_star_normal h structural hstar
  have hp := core_product_of_point_normal h hab structural hn
  exact ⟨plane_core_commutator_of_point_normal h hab structural hn, hp.1,
    pointResidual_star_card_of_normal h structural hn, hp.2,
    point_core_star_eq_centralizer_of_normal h structural hn,
    point_core_star_index_two_of_normal h structural hn,
    commutator_U_point_of_normal h hn,
    exists_selected_critical_geometry_of_point_normal h hab structural previous hn⟩

/-- In the abelian-residual branch the actual section receives the normal
point cubic, the radical product, and the selected quadratic two-offender.
No cyclicity or final residual model is assumed. -/
theorem abelian_residual_source_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (ha : IsMulCommutative ((K F) ⧸ pCore 2 (K F)))
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) :
    ⁅F.Vi 2,F.H.pCoreIn 2⁆ = F.Vi 1 ∧
      Q T L ⊔ F.H.pCoreIn 2 = F.Ri L 1 ∧
      star F (Q T L) = star F (F.Ri L 1) ∧
      ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
        star F c.Uα ≠ ⊥ ∧
        star F c.Uα ≤ centralizer (star F (F.Li L 1) : Set (HStar F.H)) ∧
        IsQuadratic ρ (c.Uα.subgroupOf F.H) ∧
        fixedCodim ρ (c.Uα.subgroupOf F.H) ≤ 2 * Nat.log 2 (Nat.card (star F c.Uα)) ∧
        ∀ a : F.H, (a : G) ∈ c.Uα →
          Even (Module.finrank (ZMod 2) (ρ a - LinearMap.id).range) ∧
          Module.finrank (ZMod 2) (ρ a - LinearMap.id).range ≤
            Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U) + 1 := by
  have hn := pointResidual_normal_of_abelian_residual h structural ha
  have hp := core_product_of_point_normal h hab structural hn
  exact ⟨plane_core_commutator_of_point_normal h hab structural hn, hp.1, hp.2,
    exists_selected_critical_action_of_point_normal h hab structural previous hn s⟩
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
