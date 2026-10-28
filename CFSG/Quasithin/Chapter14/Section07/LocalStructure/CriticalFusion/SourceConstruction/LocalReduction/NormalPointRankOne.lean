module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NormalPointReduction
public import Theory.ElementaryAbelian.PrimeRankCard
public import Theory.GroupTheory.Commutator.BoundedImageKernel

/-!
# Rank-one critical pairs in the normal-point branch

Assume the original L₁ is normal in H and the image R₁* has two-rank at
most one. The elementary selected critical actor then has order two, and
the reciprocal core index is two. The normal cubic makes every nonzero
actor displacement even; the critical bound therefore makes it exactly
two. Applying this on both orientations identifies both point commutators.
It also gives an order-eight full commutator and disjoint original and
reciprocal points. A bounded-image commutator argument then gives the exact
indices of the literal centralizer C_U(Uα).

The final application constructs its section and selected path from the
original flag. It retains normality and the rank bound as explicit local
antecedents: the residual classification deriving these from the
extraspecial branch is not supplied here. In particular, these results do
not assert all of 14.7.16, identify the full commutator with V, or complete
the solvable exclusion or the classification through 14.7.52.

Source: Aschbacher–Smith, 14.7.15(1),(2), 14.7.16(6), Remark 14.7.17 and
the commutator and centralizer arguments in 14.7.16–18, printed pp.1047–1048.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) F.H W}

/-- An order-two critical image forces the selected reciprocal index to be two. -/
theorem selected_critical_indices_of_card_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) :
    (F.U ⊓ c.Qα).relIndex F.U = 2 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 F.U).to_quotient
    ((F.U ⊓ c.Qα).subgroupOf F.U) |>.exists_card_eq
  change (F.U ⊓ c.Qα).relIndex F.U = 2 ^ n at hn
  have hp := hs.positive
  have hb := hs.comparison
  rw [hn,Nat.log_pow Nat.one_lt_two] at hp hb
  rw [ha] at hb
  norm_num at hb
  have : n = 1 := by omega
  simpa only [this,pow_one] using hn

/-- The selected actor has order two when the point-parabolic star core has two-rank at most one. -/
theorem critical_card_two_of_point_core_rank_one
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (hr : primeRank 2 (star F (F.Ri L 1)) ≤ 1) :
    Nat.card (star F c.Uα) = 2 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  let : IsElementaryAbelian 2 c.Uα :=
    IsElementaryAbelian.map (MulAut.conj c.conjugator⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 (c.Uα.subgroupOf F.H) :=
    IsElementaryAbelian.subgroupOf ((critical_le_Q h structural c).trans (Q_le_H F))
  let : IsElementaryAbelian 2 (star F c.Uα) := IsElementaryAbelian.map (starMap F)
  have hle : star F c.Uα ≤ star F (F.Ri L 1) :=
    map_mono (comap_mono (critical_le_Ri h structural c))
  have hb : primeRank 2 (star F c.Uα) ≤ 1 := (primeRank_mono 2 hle).trans hr
  have hpos := (one_lt_card_iff_ne_bot _).mpr (c.star_ne_bot hs)
  rw [IsElementaryAbelian.card_eq_pow_primeRank (p := 2) (star F c.Uα)] at hpos ⊢
  have : primeRank 2 (star F c.Uα) = 1 := by
    have hn : primeRank 2 (star F c.Uα) ≠ 0 := by
      intro hz
      simp only [hz,pow_zero,lt_self_iff_false] at hpos
    omega
  rw [this,pow_one]

/-- Every nontrivial selected actor has displacement exactly two on the literal section. -/
theorem critical_displacement_two_of_normal_card_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2)
    (a : F.H) (haA : (a : G) ∈ c.Uα) (haQ : a ∉ pCore 2 F.H) :
    Module.finrank (ZMod 2) (ρ a - LinearMap.id).range = 2 := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have hk := section_action_kernel_eq_core_of_escape h structural hescape s
  have hb := (critical_fixedCodim_bounds_of_kernel h hab structural hk s c).2 a haA
  rw [selected_critical_indices_of_card_two h hab c hs ha] at hb
  norm_num at hb
  have he := point_core_displacement_even_of_normal h structural hn s a
    (critical_le_Ri h structural c haA)
  have hne : Module.finrank (ZMod 2) (ρ a - LinearMap.id).range ≠ 0 := by
    intro hz
    have he : ρ a = 1 := sub_eq_zero.mp
      (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz))
    exact haQ (hk ▸ (show a ∈ ρ.ker from he))
  obtain ⟨k,hk⟩ := he
  omega

/-- The reciprocal core intersection has commutator exactly the reciprocal point. -/
theorem critical_intersection_commutator_of_normal_card_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) :
    ⁅F.U ⊓ c.Qα,c.Uα⁆ = c.Zα := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have hk := section_action_kernel_eq_core_of_escape h structural hescape s
  have hle : ⁅F.U ⊓ c.Qα,c.Uα⁆ ≤ c.Zα :=
    (commutator_mono inf_le_right le_rfl).trans (reciprocal_core_commutator_le_point h s c)
  have hcard : Nat.card c.Zα = 2 := by
    rw [CriticalPath.Zα,conjugate,card_map_of_injective (MulAut.conj c.conjugator⁻¹).injective]
    simpa using F.card 1 (by decide)
  apply eq_of_le_of_card_ge hle
  rw [hcard]
  apply (one_lt_card_iff_ne_bot _).mpr
  intro hz
  let A := star F c.Uα
  let : Nontrivial A := (nontrivial_iff_ne_bot _).mpr (c.star_ne_bot hs)
  obtain ⟨x,hx⟩ := exists_ne (1 : A)
  obtain ⟨a,haA,he⟩ := x.property
  have haQ : a ∉ pCore 2 F.H := by
    intro hq
    apply hx
    apply Subtype.ext
    rw [←he]
    exact (QuotientGroup.eq_one_iff _).mpr hq
  have hdim := critical_displacement_two_of_normal_card_two h hab structural hescape hn s c hs ha a haA haQ
  have hfix : s.imageSpace (F.U ⊓ c.Qα) ≤ LinearMap.ker (ρ a - LinearMap.id) := by
    intro v hv
    apply sub_eq_zero.mpr
    exact s.fixed_on_imageSpace_of_commutator_le c.Uα (F.U ⊓ c.Qα)
      (by rw [commutator_comm,hz]; exact bot_le) a haA v hv
  have hpoint : F.Vi 1 ≤ F.U ⊓ c.Qα :=
    le_inf ((F.le_seed 1).trans (le_conjugateSpanBy V F.H))
      (point_le_reciprocal_core_of_kernel h structural hk s c)
  have hc := s.imageSpace_codimension_of_index (F.U ⊓ c.Qα) inf_le_left hpoint 1
    (by simpa using selected_critical_indices_of_card_two h hab c hs ha)
  have hb := Submodule.finrank_mono hfix
  have hr := LinearMap.finrank_range_add_finrank_ker (ρ a - LinearMap.id)
  omega


/-- Reversing the selected pair recovers the original point as a commutator. -/
theorem critical_reverse_intersection_commutator_of_normal_card_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) :
    ⁅c.Uα ⊓ F.H.pCoreIn 2,F.U⁆ = F.Vi 1 := by
  have hAH := (critical_le_Q h structural c).trans (Q_le_H F)
  obtain ⟨r⟩ := exists_reversal_of_star_ne_bot h structural c hAH (c.star_ne_bot hs)
  have hrCard : Nat.card (star F r.path.Uα) = 2 := by
    rw [r.reverse_star_of_placement ((critical_le_Q h structural r.path).trans (Q_le_H F))]
    exact selected_critical_indices_of_card_two h hab c hs ha
  have hrSel : r.path.RankSelection :=
    ⟨critical_index_positive r.path,by
      rw [r.reverse_index_of_placement hAH,ha,hrCard]⟩
  have he := congrArg (fun B : Subgroup G => conjugate B r.conjugator)
    (critical_intersection_commutator_of_normal_card_two h hab structural hescape hn s r.path hrSel hrCard)
  have hm (A B : Subgroup G) : conjugate ⁅A,B⁆ r.conjugator =
      ⁅conjugate A r.conjugator,conjugate B r.conjugator⁆ := map_commutator _ _ _
  rw [hm,conjugate_inf,r.base_U,r.tip_core,r.tip_U,r.tip_point] at he
  exact he

/-- The full critical commutator has image of dimension two in the original section. -/
theorem critical_commutator_image_rank_of_normal_card_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) :
    Module.finrank (ZMod 2) (s.imageSpace ⁅F.U,c.Uα⁆) = 2 := by
  have hAH := (critical_le_Q h structural c).trans (Q_le_H F)
  obtain ⟨σ,hσ⟩ := exists_star_representation h s
  let A := star F c.Uα
  let : Nontrivial A := (nontrivial_iff_ne_bot _).mpr (c.star_ne_bot hs)
  obtain ⟨x,hx⟩ := exists_ne (1 : A)
  obtain ⟨a,haA,he⟩ := x.property
  have haQ : a ∉ pCore 2 F.H := by
    intro hq
    apply hx
    apply Subtype.ext
    rw [←he]
    exact (QuotientGroup.eq_one_iff _).mpr hq
  have hz : zpowers (x : HStar F.H) = A := by
    have hh := congrArg (Subgroup.map A.subtype) (zpowers_eq_top_of_prime_card ha hx)
    rw [MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have ht : s.imageSpace F.U = ⊤ := by
    apply top_unique
    intro v _
    obtain ⟨y,hy⟩ := s.onto (Multiplicative.ofAdd v)
    exact (s.mem_imageSpace_iff _ _).mpr ⟨y,y.property,congrArg Multiplicative.toAdd hy⟩
  rw [commutator_comm,s.imageSpace_commutator c.Uα F.U hAH le_rfl,ht,←hσ,
    subspaceCommutator_comp_map]
  change Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ A) = 2
  rw [←hz,CyclicFixedRank.commutator_eq_range,←he]
  change Module.finrank (ZMod 2) (σ.comp (starMap F) a - LinearMap.id).range = 2
  rw [hσ]
  exact critical_displacement_two_of_normal_card_two h hab structural hescape hn s c hs ha a haA haQ

/-- The full critical commutator has order eight, including the original point. -/
theorem critical_commutator_card_of_normal_card_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) :
    Nat.card (⁅F.U,c.Uα⁆ : Subgroup G) = 8 := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have hpoint : F.Vi 1 ≤ ⁅F.U,c.Uα⁆ := by
    rw [←critical_reverse_intersection_commutator_of_normal_card_two h hab structural hescape hn s c hs ha,
      commutator_comm]
    exact commutator_mono le_rfl inf_le_left
  have hCU : ⁅F.U,c.Uα⁆ ≤ F.U := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_right.mp
      (((critical_le_Q h structural c).trans (Q_le_H F)).trans s.normalized)
  have he := s.imageSpace_card_eq_relIndex ⁅F.U,c.Uα⁆ hCU
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
    critical_commutator_image_rank_of_normal_card_two h hab structural hescape hn s c hs ha] at he
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) (F.Vi 1) ⁅F.U,c.Uα⁆ bot_le hpoint
  rw [relIndex_bot_left,relIndex_bot_left,←he] at hc
  have hp : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  norm_num [hp] at hc
  exact hc.symm


/-- The ambient centralizer bound follows from the exact original kernel. -/
theorem centralizer_U_le_core_of_escape
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) :
    centralizer (F.U : Set G) ≤ F.H.pCoreIn 2 := by
  intro x hx
  have hxH : x ∈ F.H :=
    (Subgroup.centralizer_le_normalizer _) (centralizer_le s.kernel_le hx)
  let a : F.H := ⟨x,hxH⟩
  have hk : a ∈ ρ.ker := by
    apply (s.action_mem_ker_iff a).mpr
    intro v hv
    have he : ⁅x,v⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hx v hv).symm
    exact he ▸ (F.Vi 1).one_mem
  rw [section_action_kernel_eq_core_of_escape h structural hescape s] at hk
  exact mem_map_of_mem F.H.subtype hk

/-- The original and reciprocal points are distinct and have trivial intersection. -/
theorem critical_points_disjoint_of_normal_card_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) : Disjoint (F.Vi 1) c.Zα := by
  have hnle : ¬ c.Zα ≤ F.Vi 1 := by
    intro hle
    let A := star F c.Uα
    let : Nontrivial A := (nontrivial_iff_ne_bot _).mpr (c.star_ne_bot hs)
    obtain ⟨x,hx⟩ := exists_ne (1 : A)
    obtain ⟨a,haA,he⟩ := x.property
    have haQ : a ∉ pCore 2 F.H := by
      intro hq
      apply hx
      apply Subtype.ext
      rw [←he]
      exact (QuotientGroup.eq_one_iff _).mpr hq
    have hd := critical_displacement_two_of_normal_card_two h hab structural hescape hn s c hs ha a haA haQ
    let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
      (Multiplicative.toAdd.surjective.comp s.onto)
    have hfix : s.imageSpace (F.U ⊓ c.Qα) ≤ LinearMap.ker (ρ a - LinearMap.id) := by
      intro v hv
      apply sub_eq_zero.mpr
      exact s.fixed_on_imageSpace_of_commutator_le c.Uα (F.U ⊓ c.Qα)
        (by rw [commutator_comm,critical_intersection_commutator_of_normal_card_two h hab structural hescape hn s c hs ha]; exact hle)
        a haA v hv
    have hpoint : F.Vi 1 ≤ F.U ⊓ c.Qα := le_inf s.kernel_le
      (point_le_reciprocal_core_of_kernel h structural
        (section_action_kernel_eq_core_of_escape h structural hescape s) s c)
    have hc := s.imageSpace_codimension_of_index (F.U ⊓ c.Qα) inf_le_left hpoint 1
      (by simpa using selected_critical_indices_of_card_two h hab c hs ha)
    have hb := Submodule.finrank_mono hfix
    have hr := LinearMap.finrank_range_add_finrank_ker (ρ a - LinearMap.id)
    omega
  have hzCard : Nat.card c.Zα = 2 := by
    rw [CriticalPath.Zα,conjugate,card_map_of_injective (MulAut.conj c.conjugator⁻¹).injective]
    simpa using F.card 1 (by decide)
  apply disjoint_iff.mpr
  by_contra hb
  have hlo := (one_lt_card_iff_ne_bot _).mpr hb
  have he : F.Vi 1 ⊓ c.Zα = c.Zα := eq_of_le_of_card_ge inf_le_right (by omega)
  exact hnle (he ▸ (inf_le_left : F.Vi 1 ⊓ c.Zα ≤ F.Vi 1))

/-- The two reciprocal core intersections commute. -/
theorem critical_intersection_centralizes_of_normal_card_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) :
    ⁅F.U ⊓ c.Qα,c.Uα ⊓ F.H.pCoreIn 2⁆ = ⊥ := by
  have h₁ : ⁅F.U ⊓ c.Qα,c.Uα ⊓ F.H.pCoreIn 2⁆ ≤ F.Vi 1 := by
    rw [commutator_comm]
    exact (commutator_mono inf_le_right inf_le_left).trans (section_core_commutator_le_point h s)
  have h₂ : ⁅F.U ⊓ c.Qα,c.Uα ⊓ F.H.pCoreIn 2⁆ ≤ c.Zα :=
    (commutator_mono inf_le_right inf_le_left).trans (reciprocal_core_commutator_le_point h s c)
  exact le_bot_iff.mp ((le_inf h₁ h₂).trans
    (critical_points_disjoint_of_normal_card_two h hab structural hescape hn s c hs ha).le_bot)

/-- The actual centralizer has index two in the reciprocal intersection and index four in U. -/
theorem critical_centralizer_indices_of_normal_card_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) :
    (F.U ⊓ centralizer (c.Uα : Set G)).relIndex (F.U ⊓ c.Qα) = 2 ∧
      (F.U ⊓ centralizer (c.Uα : Set G)).relIndex F.U = 4 := by
  let := hab
  let D := F.U ⊓ c.Qα
  let A := c.Uα ⊓ F.H.pCoreIn 2
  let C := F.U ⊓ centralizer (c.Uα : Set G)
  have hcc : centralizer (c.Uα : Set G) ≤ c.Qα := by
    have he : conjugate (centralizer (F.U : Set G)) c.conjugator = centralizer (c.Uα : Set G) := by
      apply le_antisymm
      · exact map_centralizer_le_centralizer_image _ _
      · intro x hx
        refine ⟨(MulAut.conj c.conjugator) x, ?_, by simp [MulAut.conj_apply,mul_assoc]⟩
        intro a ha
        apply (MulAut.conj c.conjugator⁻¹).injective
        simpa [map_mul,MulAut.conj_apply,mul_assoc] using
          hx ((MulAut.conj c.conjugator⁻¹) a) (mem_map_of_mem _ ha)
    rw [←he]
    exact (map_mono (centralizer_U_le_core_of_escape h structural hescape s)).trans_eq
      (map_pCoreIn_of_injective 2 F.H _ (MulAut.conj c.conjugator⁻¹).injective)
  have hCD : C ≤ D := inf_le_inf_left _ hcc
  have hz : ⁅D,c.Uα⁆ = c.Zα :=
    critical_intersection_commutator_of_normal_card_two h hab structural hescape hn s c hs ha
  have hZA : c.Zα ≤ D := by
    let := h.chosen.elementary
    let := elementary_U F
    have hUQ : F.U ≤ F.H.pCoreIn 2 := le_pCoreIn_of_normalizes
      (IsElementaryAbelian.isPGroup 2 F.U) s.section_le s.normalized
    refine le_inf ?_ ?_
    · rw [←hz]
      exact (commutator_mono inf_le_left le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp
          (((critical_le_Q h structural c).trans (Q_le_H F)).trans s.normalized))
    · exact (map_mono (s.kernel_le.trans hUQ)).trans_eq
        (map_pCoreIn_of_injective 2 F.H _ (MulAut.conj c.conjugator⁻¹).injective)
  have hzCard : Nat.card c.Zα = 2 := by
    rw [CriticalPath.Zα,conjugate,card_map_of_injective (MulAut.conj c.conjugator⁻¹).injective]
    simpa using F.card 1 (by decide)
  have hi : A.relIndex c.Uα = 2 := by
    rw [show A = F.H.pCoreIn 2 ⊓ c.Uα from inf_comm _ _]
    rw [CriticalIntersections.core_intersection_index_eq_star_card c.Uα
      ((critical_le_Q h structural c).trans (Q_le_H F)),ha]
  have hcent : A ≤ centralizer (D : Set G) := le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp
      (critical_intersection_centralizes_of_normal_card_two h hab structural hescape hn s c hs ha))
  let : IsMulCommutative D := le_centralizer_iff_isMulCommutative.mp
    (inf_le_left.trans (F.U.le_centralizer.trans (centralizer_le inf_le_left)))
  obtain ⟨B,hBD,hcard,hBfix⟩ := exists_large_subgroup_commutator_le_of_index_two
    D D c.Uα A ⊥ c.Zα le_rfl inferInstance hZA hz.le inf_le_left hcent hi
  have hBC : B ≤ C := le_inf (hBD.trans inf_le_left)
    (commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp hBfix))
  rw [relIndex_bot_left,hzCard] at hcard
  have hb : Nat.card D ≤ 2 * Nat.card C := hcard.trans (Nat.mul_le_mul_left 2 (card_le_of_le hBC))
  have hci : C.relIndex D = 2 := by
    have hc := relIndex_mul_card_of_le hCD
    have hp : 0 < Nat.card C := Nat.card_pos
    have hpos : C.relIndex D ≠ 0 := (C.subgroupOf D).index_ne_zero_of_finite
    have hne : C.relIndex D ≠ 1 := by
      intro he
      have hfix : ⁅D,c.Uα⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
        ((relIndex_eq_one.mp he).trans inf_le_right)
      rw [hz] at hfix
      rw [hfix,card_bot] at hzCard
      omega
    have hge : 2 ≤ C.relIndex D := by omega
    have hle : C.relIndex D ≤ 2 := by nlinarith
    omega
  refine ⟨hci,?_⟩
  have ht := relIndex_mul_relIndex C D F.U hCD inf_le_left
  rw [hci,selected_critical_indices_of_card_two h hab c hs ha] at ht
  exact ht.symm

/-- Apply the rank-one geometry to the original normal point normalizer.
The local antecedents are exactly normality from 14.7.15(1) and the
rank-one consequence of 14.7.15(2); the literal section, selected path
and displayed critical-pair conclusions are constructed here. -/
theorem normal_point_rank_one_source_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (hr : primeRank 2 (star F (F.Ri L 1)) ≤ 1) :
    ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
      Nat.card (star F c.Uα) = 2 ∧ (F.U ⊓ c.Qα).relIndex F.U = 2 ∧
      ⁅F.U ⊓ c.Qα,c.Uα⁆ = c.Zα ∧
      ⁅c.Uα ⊓ F.H.pCoreIn 2,F.U⁆ = F.Vi 1 ∧
      Disjoint (F.Vi 1) c.Zα ∧
      ⁅F.U ⊓ c.Qα,c.Uα ⊓ F.H.pCoreIn 2⁆ = ⊥ ∧
      Nat.card (⁅F.U,c.Uα⁆ : Subgroup G) = 8 ∧
      (F.U ⊓ centralizer (c.Uα : Set G)).relIndex (F.U ⊓ c.Qα) = 2 ∧
      (F.U ⊓ centralizer (c.Uα : Set G)).relIndex F.U = 4 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  obtain ⟨c,hs,hplace,_,_⟩ :=
    exists_selected_critical_geometry_of_point_normal h hab structural previous hn
  have ha := critical_card_two_of_point_core_rank_one h hab structural c hs hr
  have hescape := h.flag_escape F previous
  exact ⟨c,hs,hplace,ha,selected_critical_indices_of_card_two h hab c hs ha,
    critical_intersection_commutator_of_normal_card_two h hab structural hescape hn s c hs ha,
    critical_reverse_intersection_commutator_of_normal_card_two h hab structural hescape hn s c hs ha,
    critical_points_disjoint_of_normal_card_two h hab structural hescape hn s c hs ha,
    critical_intersection_centralizes_of_normal_card_two h hab structural hescape hn s c hs ha,
    critical_commutator_card_of_normal_card_two h hab structural hescape hn s c hs ha,
    critical_centralizer_indices_of_normal_card_two h hab structural hescape hn s c hs ha⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
