module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialBranch
public import Theory.GroupAction.Extraspecial27CubicFixer
public import Theory.Representation.ExtraspecialCubicSmallActor

/-!
# Point normality in the original extraspecial residual branch

The point cubic has order three and is centralized by R₁* before any point
normality is assumed. Faithful action on the extraspecial residual therefore
bounds the two-rank of R₁* by one. Cubic displacement excludes transvections
on the literal U/V₁ section, so critical reciprocity supplies a nontrivial
selected involution. It moves at most two dimensions, hence fixes the residual
center. Its fixed subgroup in the residual is exactly that center; since it
also fixes the point cubic, the two cubics coincide. Relative normality in H
then follows through the original star map.

The application starts with the actual Heisenberg isomorphism and discharges
the point-normality premise of ExtraspecialBranch. It yields the faithful
irreducible six-dimensional section, |U| = 128, and reciprocal critical
geometry from the original flag and the named earlier-source inputs.
The subsequent extraspecial exclusion 14.7.14 and residual classification
through 14.7.52 remain separate mathematical obligations in this task.

Source: Aschbacher–Smith, 14.7.15(1) and 14.7.16, printed pp.1047–1048.
The argument uses the faithful section as an alternative to the source's
initial central-cubic placement argument.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
local notation "B" => (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)

omit [Finite G] in
private theorem point_star_le_residual' : star F (F.Li L 1) ≤ pResidual 2 (HStar F.H) := by
  have hh : (F.Li L 1).subgroupOf F.H ≤ pResidual 2 F.H := by
    rw [←residual_subgroupOf F]
    exact subgroupOf_mono F.H (pointResidual_le F)
  exact (map_mono hh).trans (map_pResidual_le 2 (starMap F))

/-- An odd three-residual gives the actual point image order three, without normality. -/
theorem point_star_card_of_three_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hp : IsPGroup 3 (pResidual 2 (HStar F.H))) :
    Nat.card (star F (F.Li L 1)) = 3 := by
  let A := (F.Li L 1).subgroupOf F.H
  let f := (starMap F).subgroupMap A
  have hk : IsPGroup 2 f.ker := by
    rw [ker_subgroupMap,starMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  have hA3 : IsPGroup 3 (star F (F.Li L 1)) := hp.to_le point_star_le_residual'
  have hc : pCore 2 (star F (F.Li L 1)) = ⊥ := by
    exact le_bot_iff.mp ((le_inf le_rfl le_top).trans
      (pCore_isPGroup.disjoint_of_coprime (hA3.to_subgroup ⊤)
        (by decide : Nat.Coprime 2 3)).le_bot)
  have hcard : Nat.card (A ⧸ pCore 2 A) = 3 := by
    let e : A ≃* F.Li L 1 := subgroupOfEquivOfLe
      (show F.Li L 1 ≤ F.H from (F.Li_le L 1).trans inf_le_right)
    rw [Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv]
    exact pointResidual_core_quotient_card h structural
  have he := Nat.card_congr (f.pCoreQuotientEquiv
    ((starMap F).subgroupMap_surjective A) hk).toEquiv
  change Nat.card (A ⧸ pCore 2 A) = Nat.card
    ((star F (F.Li L 1)) ⧸ pCore 2 (star F (F.Li L 1))) at he
  rw [hc,Nat.card_congr QuotientGroup.quotientBot.toEquiv,hcard] at he
  exact he.symm

/-- The point core centralizes the cubic image inside an odd three-residual. -/
theorem point_core_centralizes_of_three_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hp : IsPGroup 3 (pResidual 2 (HStar F.H))) :
    star F (F.Ri L 1) ≤ centralizer (star F (F.Li L 1) : Set (HStar F.H)) := by
  let R := star F (F.Ri L 1)
  let A := star F (F.Li L 1)
  have hn : B ≤ normalizer (F.Li L 1 : Set G) :=
    sup_le (F.Li L 1).le_normalizer (T_normalizes_L₁ h structural)
  have hcomm : ⁅F.Ri L 1,F.Li L 1⁆ ≤ F.Li L 1 :=
    le_normalizer_iff_commutator_le_right.mp ((pCoreIn_le 2 B).trans hn)
  have hcommR : ⁅F.Ri L 1,F.Li L 1⁆ ≤ F.Ri L 1 := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_right.mp
      ((show F.Li L 1 ≤ B from le_sup_left).trans
        ((show B ≤ normalizer (B : Set G) from Subgroup.le_normalizer).trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))))
  have hrel : ⁅(F.Ri L 1).subgroupOf F.H,(F.Li L 1).subgroupOf F.H⁆ ≤
      (F.Ri L 1).subgroupOf F.H ⊓ (F.Li L 1).subgroupOf F.H := by
    intro x hx
    have hm := mem_map_of_mem F.H.subtype hx
    rw [map_commutator,subgroupOf_map_subtype,subgroupOf_map_subtype] at hm
    have hm' := (commutator_mono inf_le_left inf_le_left) hm
    exact ⟨hcommR hm',hcomm hm'⟩
  have hRA : ⁅R,A⁆ ≤ R ⊓ A := by
    change ⁅((F.Ri L 1).subgroupOf F.H).map (starMap F),
      ((F.Li L 1).subgroupOf F.H).map (starMap F)⁆ ≤ _
    rw [←map_commutator]
    exact le_inf (map_mono (hrel.trans inf_le_left)) (map_mono (hrel.trans inf_le_right))
  have hd : Disjoint R A := (isPGroup_pCoreIn 2 B).comap_subtype.map (starMap F)
    |>.disjoint_of_coprime (hp.to_le point_star_le_residual') (by decide : Nat.Coprime 2 3)
  exact commutator_eq_bot_iff_le_centralizer.mp (bot_unique (hRA.trans hd.le_bot))

private theorem residual_actor_faithful'
    {D : Type*} [Group D] [Finite D]
    (hcore : pCore 2 D = ⊥) (hodd : Odd (Nat.card (pResidual 2 D)))
    (A : Subgroup D) (hA : IsPGroup 2 A) :
    Function.Injective ((MulAut.conjNormal : D →* MulAut (pResidual 2 D)).comp A.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  have hc : (a : D) ∈ centralizer (pResidual 2 D : Set D) := by
    rw [←MulAut.conjNormal_ker_eq_centralizer]
    exact ha
  have hp := Theory.GroupTheory.centralizer_pResidual_le_of_pCore_eq_bot hcore hc
  have hdis : Disjoint A (pResidual 2 D) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨n,hn⟩ := hA.exists_card_eq
    rw [hn]
    exact hodd.coprime_two_left.pow_left n
  exact Subtype.ext (mem_bot.mp (hdis.le_bot ⟨a.property,hp⟩))

/-- The extraspecial residual bounds the point core rank before point normality is known. -/
theorem point_core_rank_one_of_extraspecial_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27) :
    primeRank 2 (star F (F.Ri L 1)) ≤ 1 := by
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  let X := (star F (F.Li L 1)).subgroupOf P
  have hX : Nat.card X = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe point_star_le_residual').toEquiv]
    exact point_star_card_of_three_residual h structural (IsExtraspecial.isPGroup 3 P)
  let R := star F (F.Ri L 1)
  apply (primeRank_le_iff_elementary_card_le R).mpr
  intro E hE
  let := hE
  let A := E.map R.subtype
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map R.subtype
  let f : A →* MulAut P := (MulAut.conjNormal : HStar F.H →* MulAut P).comp A.subtype
  have hf : Function.Injective f := residual_actor_faithful' (pCore_quotient_pCore_eq_bot 2)
    (by rw [hP]; decide) A (IsElementaryAbelian.isPGroup 2 A)
  have hfix : ∀ a : A, ∀ x ∈ X, f a x = x := by
    intro a x hx
    apply Subtype.ext
    have hc := point_core_centralizes_of_three_residual h structural
      (IsExtraspecial.isPGroup 3 P) (map_subtype_le E a.property)
    change (a : HStar F.H)*(x : HStar F.H)*(a : HStar F.H)⁻¹=x
    rw [←hc x hx,mul_inv_cancel_right]
  have hb := MulAut.elementary_two_cubic_fixer_card_le_two hP f hf X hX hfix
  simpa only [A,card_map_of_injective R.subtype_injective,pow_one] using hb
private theorem extraspecial_actor_trivial_of_line_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (A C : Subgroup G) [IsElementaryAbelian 2 A]
    (hc : ⁅A,F.U⁆ ≤ C) (hC : Nat.card C ≤ 2)
    (a : F.H) (ha : (a : G) ∈ A) : ρ a = 1 := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have himageCard : Nat.card (s.imageSpace C) ≤ 2 := by
    change Nat.card ((C.subgroupOf F.U).map s.coordinates) ≤ 2
    have hm := Nat.card_le_card_of_surjective (s.coordinates.subgroupMap
      (C.subgroupOf F.U)) (s.coordinates.subgroupMap_surjective _)
    have hs : Nat.card (C.subgroupOf F.U) ≤ Nat.card C :=
      Nat.card_le_card_of_injective (fun y => (⟨y.val,y.property⟩ : C))
        (fun x y he => Subtype.ext (Subtype.ext (congrArg (fun z : C => (z : G)) he)))
    exact hm.trans (hs.trans hC)
  have hdim : Module.finrank (ZMod 2) (s.imageSpace C) ≤ 1 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at himageCard
    by_contra hn
    have he := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
      (show 2 ≤ Module.finrank (ZMod 2) (s.imageSpace C) by omega)
    omega
  have hr : Module.finrank (ZMod 2) (ρ a - LinearMap.id).range ≤ 1 :=
    (Submodule.finrank_mono
      (s.displacement_range_le_imageSpace_of_commutator_le A C hc a ha)).trans hdim
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  have heP : Monoid.exponent P = 3 := by
    rw [←Monoid.exponent_eq_of_mulEquiv (residualStarEquiv F),hexp]
  obtain ⟨σ,hσ⟩ := exists_star_representation h s
  have hf : Function.Injective σ := by
    apply (MonoidHom.ker_eq_bot_iff σ).mp
    apply bot_unique
    intro x hx
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 F.H) x
    have hk : a ∈ ρ.ker := by rw [←hσ]; exact hx
    rw [section_action_kernel_eq_core_of_escape h structural hescape s] at hk
    exact (QuotientGroup.eq_one_iff _).mpr hk
  have ht : starMap F a ^ 2 = 1 := by
    rw [←map_pow]
    have he : (a : G)^2=1 := congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) (⟨a,ha⟩ : A))
    rw [show a^2=1 from Subtype.ext he,map_one]
  have hs : fixedCodim σ (zpowers (starMap F a)) ≤ 1 := by
    rw [fixedCodim_zpowers_eq_displacement_rank]
    change Module.finrank (ZMod 2) (σ.comp (starMap F) a - LinearMap.id).range ≤ 1
    rwa [hσ]
  have he := Representation.ExtraspecialBinarySix.rank_one_actor_trivial σ hf P hP heP
    (Theory.GroupTheory.centralizer_pResidual_le_of_pCore_eq_bot (pCore_quotient_pCore_eq_bot 2))
    (starMap F a) ht hs
  rw [←hσ]
  change σ (starMap F a) = 1
  rw [he,map_one]

private theorem extraspecial_actor_in_core_of_line_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (A C : Subgroup G) [IsElementaryAbelian 2 A] (hA : A ≤ F.Ri L 1)
    (hc : ⁅A,F.U⁆ ≤ C) (hC : Nat.card C ≤ 2) :
    A ≤ F.H.pCoreIn 2 := by
  intro a ha
  have haH : a ∈ F.H := ((pCoreIn_le 2 B).trans
    (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1))) (hA ha)
  have he := extraspecial_actor_trivial_of_line_commutator h structural hescape hex hcard hexp s
    A C hc hC ⟨a,haH⟩ ha
  exact mem_map_of_mem F.H.subtype
    ((section_action_kernel_eq_core_of_escape h structural hescape s).le
      (show (⟨a,haH⟩ : F.H) ∈ ρ.ker from he))

/-- Source 14.7.5's even-displacement argument forces the reciprocal actor
to have nontrivial star image on the actual critical path. -/
theorem critical_star_nontrivial_of_extraspecial_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (c : CriticalPath (L := L) F) : star F c.Uα ≠ ⊥ := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  intro hz
  have hAH : c.Uα ≤ F.H := (critical_le_Ri h structural c).trans
    ((pCoreIn_le 2 B).trans
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  have hαQ : c.Uα ≤ F.H.pCoreIn 2 := by
    have hk : c.Uα.subgroupOf F.H ≤ pCore 2 F.H := by
      simpa only [CriticalFusion.Source.star, Subgroup.map_eq_bot_iff, starMap,
        QuotientGroup.ker_mk'] using hz
    intro x hx
    exact mem_map.mpr ⟨⟨x,hAH hx⟩,hk hx,rfl⟩
  have hcomm : ⁅F.U,c.Uα⁆ ≤ F.Vi 1 := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro a ha u hu
    have haH : a ∈ F.H := hAH ha
    have hqa : (⟨a,haH⟩ : F.H) ∈ pCore 2 F.H := by
      obtain ⟨a',ha',he⟩ := hαQ ha
      exact (show a' = ⟨a,haH⟩ from Subtype.ext he) ▸ ha'
    exact (s.action_mem_ker_iff ⟨a,haH⟩).mp (core_le_action_kernel h s hqa) u hu
  obtain ⟨g,hUg,hHg,hAR⟩ := exists_terminal_edge_transport h structural c
  let f := (MulAut.conj g).toMonoidHom
  let A := F.U.map f
  let C := (F.Vi 1).map f
  have hc : ⁅A,F.U⁆ ≤ C := by
    have hm := map_mono (f := f) hcomm
    change c.Uα.map f = F.U at hUg
    rw [map_commutator,hUg] at hm
    exact hm
  have hC : Nat.card C ≤ 2 := by
    rw [card_map_of_injective (MulAut.conj g).injective]
    exact (show Nat.card (F.Vi 1) = 2 by simpa using F.card 1 (by decide)).le
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map f
  have hAQ := extraspecial_actor_in_core_of_line_commutator h structural hescape hex hcard hexp
    s A C hAR hc hC
  have hQmap : c.Qα.map f = F.H.pCoreIn 2 := by
    change ((conjugate F.H c.conjugator).pCoreIn 2).map f = _
    rw [map_pCoreIn_of_injective 2 _ f (MulAut.conj g).injective,hHg]
  exact critical_span_not_le_reciprocal_core c
    ((map_le_map_iff_of_injective (f := f) (MulAut.conj g).injective).mp
      (hAQ.trans_eq hQmap.symm))


/-- The actual extraspecial residual forces relative point normality. -/
theorem pointResidual_normal_of_extraspecial_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3) :
    ((F.Li L 1).subgroupOf F.H).Normal := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  have hescape := h.flag_escape F previous
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S M hM
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hM
  obtain ⟨c⟩ := exists_criticalPath h hab hescape structural uniqueness
  obtain ⟨c,hs⟩ := select_critical_orientation_of_nontrivial_star h structural c
    (critical_star_nontrivial_of_extraspecial_residual h hab structural hescape hex hcard hexp c)
  have hA := critical_card_two_of_point_core_rank_one h hab structural c hs
    (point_core_rank_one_of_extraspecial_residual h structural hex hcard)
  let A := star F c.Uα
  let : Nontrivial A := (nontrivial_iff_ne_bot _).mpr (c.star_ne_bot hs)
  obtain ⟨t,htne⟩ := exists_ne (1 : A)
  have ht2 : (t : HStar F.H)^2=1 := by
    have he := pow_card_eq_one' (x := t)
    rw [hA] at he
    exact congrArg Subtype.val he
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  obtain ⟨σ,hσ⟩ := exists_star_representation h s
  have hkernel := section_action_kernel_eq_core_of_escape h structural hescape s
  have hf : Function.Injective σ := by
    apply (MonoidHom.ker_eq_bot_iff σ).mp
    apply bot_unique
    intro x hx
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 F.H) x
    have hk : a ∈ ρ.ker := by rw [←hσ]; exact hx
    rw [hkernel] at hk
    exact (QuotientGroup.eq_one_iff _).mpr hk
  obtain ⟨a,ha,he⟩ := t.property
  have hsmall : fixedCodim σ (zpowers (t : HStar F.H)) ≤ 2 := by
    have hb := (critical_fixedCodim_bounds_of_kernel h hab structural hkernel s c).2 a ha
    rw [selected_critical_indices_of_card_two h hab c hs hA] at hb
    norm_num at hb
    rw [fixedCodim_zpowers_eq_displacement_rank,←he]
    change Module.finrank (ZMod 2) (σ.comp (starMap F) a - LinearMap.id).range ≤ 2
    rwa [hσ]
  have hcenter := Representation.ExtraspecialBinarySix.small_actor_fixes_extraspecial_center
    σ hf P hP t hsmall
  have hfaith := residual_actor_faithful' (pCore_quotient_pCore_eq_bot 2)
    (by rw [hP]; decide) A (IsPGroup.of_card (n := 1) (by simpa using hA))
  have hne : (MulAut.conjNormal (t : HStar F.H) : MulAut P) ≠ 1 := by
    intro he
    exact htne (hfaith (he.trans (map_one _).symm))
  have hinv : Function.Involutive (MulAut.conjNormal (t : HStar F.H) : MulAut P) := by
    intro x
    have he : (MulAut.conjNormal (t : HStar F.H) : MulAut P)^2=1 := by
      rw [←map_pow,ht2,map_one]
    exact congrArg (fun f : MulAut P => f x) (by simpa only [pow_two] using he)
  have hfixed := MulAut.fixed_eq_center_of_extraspecial27_involution hP
    (MulAut.conjNormal (t : HStar F.H)) hinv hne hcenter
  have hle : star F (F.Li L 1) ≤ (center P).map P.subtype := by
    intro x hx
    let xP : P := ⟨x,point_star_le_residual' hx⟩
    have hxP : xP ∈ center P := by
      rw [←hfixed]
      apply (MulAut.mem_fixedSubgroup _ _).mpr
      apply Subtype.ext
      have htR : (t : HStar F.H) ∈ star F (F.Ri L 1) :=
        (map_mono (subgroupOf_mono F.H (critical_le_Ri h structural c))) t.property
      have hc := point_core_centralizes_of_three_residual h structural
        (IsExtraspecial.isPGroup 3 P) htR x hx
      change (t : HStar F.H)*x*(t : HStar F.H)⁻¹=x
      rw [←hc,mul_inv_cancel_right]
    exact mem_map_of_mem P.subtype hxP
  have heq : star F (F.Li L 1) = (center P).map P.subtype :=
    eq_of_le_of_card_ge hle (by
      rw [point_star_card_of_three_residual h structural (IsExtraspecial.isPGroup 3 P),
        card_map_of_injective P.subtype_injective,IsExtraspecial.center_order_p 3 P])
  apply pointResidual_normal_of_star_normal h structural
  rw [heq]
  infer_instance

/-- The embedded point cubic is the actual residual center, with no normality premise. -/
theorem point_star_eq_center_of_extraspecial_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3) :
    star F (F.Li L 1) = (center (pResidual 2 (HStar F.H))).map
      (pResidual 2 (HStar F.H)).subtype :=
  point_star_eq_residual_center_of_normal h structural
    (pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp) hex

/-- Apply the proved point normality to any literal binary section, retaining its star map. -/
theorem extraspecial_section
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) :
    ∃ σ : Representation (ZMod 2) (HStar F.H) W,
      σ.comp (starMap F) = ρ ∧ Function.Injective σ ∧
      Module.finrank (ZMod 2) W = 6 ∧
      IsIrreducible (σ.comp (pResidual 2 (HStar F.H)).subtype) :=
  normal_extraspecial_section h hab structural previous
    (pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp)
    hex hcard s

/-- The original extraspecial branch now discharges the point-normality premise. -/
theorem extraspecial_source_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ((F.Li L 1).subgroupOf F.H).Normal ∧
    Nat.card F.U = 128 ∧
      ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
        Nat.card (star F c.Uα) = 2 ∧ (F.U ⊓ c.Qα).relIndex F.U = 2 ∧
        ⁅F.U ⊓ c.Qα,c.Uα⁆ = c.Zα ∧
        ⁅c.Uα ⊓ F.H.pCoreIn 2,F.U⁆ = F.Vi 1 ∧
        Disjoint (F.Vi 1) c.Zα ∧
        ⁅F.U ⊓ c.Qα,c.Uα ⊓ F.H.pCoreIn 2⁆ = ⊥ ∧
        Nat.card (⁅F.U,c.Uα⁆ : Subgroup G) = 8 ∧
        (F.U ⊓ centralizer (c.Uα : Set G)).relIndex (F.U ⊓ c.Qα) = 2 ∧
        (F.U ⊓ centralizer (c.Uα : Set G)).relIndex F.U = 4 := by
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  exact ⟨hn,normal_extraspecial_source_reduction h hab structural previous hn ⟨e⟩⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
