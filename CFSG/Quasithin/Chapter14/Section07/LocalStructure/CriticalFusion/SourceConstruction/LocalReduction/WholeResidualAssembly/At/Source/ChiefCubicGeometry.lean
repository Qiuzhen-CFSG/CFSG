module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialChiefFactors
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.LocalAction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Alternating.NaturalRecognition
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Source.PointGeometry
public import Theory.GroupTheory.NoncentralChiefRefinement.NormalPerfectMovement
public import Theory.GroupTheory.PGroup.ExtraspecialThreeActorGeneration
public import Theory.Representation.ExtraspecialCentralQuotientDegree
public import Theory.Representation.ExtraspecialCenterKernel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialCentralizerFactors
public import Theory.GroupTheory.PResidual.NormalizedSupplement
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.Quotient
public import Theory.Representation.BinaryConjugationSection.ActionKernel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialPointCentral
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialSmallChief
public import Theory.Representation.ExtraspecialSmallCentralQuotient
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialChiefSylow
public import Theory.GroupTheory.PGroup.ExtraspecialThreeSmallKernel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialCubicLifts
public import Theory.GroupTheory.PGroup.ExtraspecialThreeCubicLifts
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialCubicQuotient
public import Theory.GroupTheory.NormalizedCubicSylowQuotient
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicGeometry
public import CFSG.Quasithin.ChapterF.Section06.Basic
public import Theory.GroupTheory.PResidual.Restriction
public import Theory.GroupTheory.ConjugateSpanNormalizer
public import Theory.GroupTheory.ConjugateSpanSupplement
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicLocalStructure
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.HighRankMarked
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.Complete
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.Mathieu.OuterNormalRank
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.ElementaryAbelian.PrimeRankCard
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry

/-!
# Guarded chief cubic geometry

This unit collects the indicated original source arguments at the same G,T.
Each constituent overview records its proof and source; the universal exports
remain unchanged. The larger unit avoids repeated loading of the common source
imports. Public mathematical statements and literal subgroup maps are retained.
-/

/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Chief factors in the original extraspecial centralizer section

A selected reciprocal involution fixes the center of the extraspecial
star residual and inverts its Frattini quotient. Its normal closure
contains that residual; two-perfectness removes the original two-core
when lifting back to H. Thus any H-invariant section centralized by the
reciprocal span is centralized by the actual K.

For an irreducible binary section B/N of C_H(U)/U moved by the point
residual L₁, the point image is the extraspecial center. Detecting this
center makes the whole H/O₂(H)-action faithful. The displacement bound
then forces degree six and irreducibility on the residual. Saturation
makes K centralize both C_H(U)/B and N/U, proving uniqueness among
noncentral factors along that series.

When L₁ moves C_H(U)/U, a maximal-normal-subgroup argument constructs
the actual chief interval, its binary action, order 64, and the exact
action kernel O₂(H). The final application starts with the original
Heisenberg residual isomorphism and requires no chief or module witness.
In the point-central branch, any K-moved chief section now has degree
two or four. Its literal residual action quotient is elementary abelian
of order dividing nine; the center is contained in its kernel.
The point-central branch is retained explicitly: proving K-centrality
there, the rest of the extraspecial exclusion, and the residual
classification through 14.7.52 remain obligations of the local reduction.

Source: Aschbacher–Smith 14.7.20(2), printed p.1049, using 14.7.15–18,
printed pp.1047–1048. Numerators B and denominators N are kept in the
order N ≤ B; relative normality is always inside the original H.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

omit [Finite G] in
private theorem ExtraspecialChiefFactors_section_commutator_iff_kernel
    {B N A : Subgroup G} (hA : A ≤ F.H)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H B N ρ) :
    ⁅A,B⁆ ≤ N ↔ A.subgroupOf F.H ≤ ρ.ker := by
  constructor
  · intro hc a ha
    exact (s.action_mem_ker_iff a).mpr fun b hb => commutator_le.mp hc a ha b hb
  · intro hk
    exact commutator_le.mpr fun a ha b hb =>
      (s.action_mem_ker_iff ⟨a,hA ha⟩).mp (hk ha) b hb


/-- A selected reciprocal span contains a nontrivial star involution fixing
the extraspecial center. Its actual representative is retained in H. -/
theorem exists_extraspecial_critical_actor
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    ∃ a : F.H, (a : G) ∈ c.Uα ∧ starMap F a ≠ 1 ∧ (starMap F a)^2 = 1 ∧
      (MulAut.conjNormal (starMap F a) : MulAut (pResidual 2 (HStar F.H))) ≠ 1 ∧
      ∀ z ∈ center (pResidual 2 (HStar F.H)),
        (MulAut.conjNormal (starMap F a) : MulAut (pResidual 2 (HStar F.H))) z = z := by
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have hA := critical_card_two_of_normal_extraspecial_residual h hab structural hn hex hcard c hs
  let A := star F c.Uα
  let : Nontrivial A := (nontrivial_iff_ne_bot _).mpr (c.star_ne_bot hs)
  obtain ⟨x,hx⟩ := exists_ne (1 : A)
  have hxne : (x : HStar F.H) ≠ 1 := fun he => hx (Subtype.ext he)
  have hx2 : (x : HStar F.H)^2 = 1 := by
    have he := pow_card_eq_one' (x := x)
    rw [hA] at he
    exact congrArg Subtype.val he
  have hne : (MulAut.conjNormal (x : HStar F.H) : MulAut P) ≠ 1 := by
    intro he
    have hc : (x : HStar F.H) ∈ centralizer (P : Set (HStar F.H)) := by
      rw [←MulAut.conjNormal_ker_eq_centralizer]
      exact he
    have hp := Theory.GroupTheory.centralizer_pResidual_le_of_pCore_eq_bot
      (pCore_quotient_pCore_eq_bot 2) hc
    have hx27 : (x : HStar F.H)^27=1 := by
      have hh := pow_card_eq_one' (x := (⟨x,hp⟩ : P))
      rw [hP] at hh
      exact congrArg Subtype.val hh
    exact hxne (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (by decide : Nat.Coprime 2 27)
      (orderOf_dvd_of_pow_eq_one hx2) (orderOf_dvd_of_pow_eq_one hx27)))
  have hcenter : ∀ z ∈ center P, (MulAut.conjNormal (x : HStar F.H) : MulAut P) z = z := by
    intro z hz
    apply Subtype.ext
    have hz' : (z : HStar F.H) ∈ star F (F.Li L 1) := by
      rw [point_star_eq_residual_center_of_normal h structural hn hex]
      exact mem_map_of_mem P.subtype hz
    have hc := critical_actor_star_centralizes_of_point_normal h structural hn c x.property
    change (x : HStar F.H)*(z : HStar F.H)*(x : HStar F.H)⁻¹ = z
    rw [←hc z hz',mul_inv_cancel_right]
  obtain ⟨a,ha,he⟩ := x.property
  exact ⟨a,ha,he ▸ hxne,he ▸ hx2,he ▸ hne,he ▸ hcenter⟩

/-- The selected reciprocal span normally generates the whole original
residual. Containment in an H-normal subgroup is checked before quotienting. -/
theorem extraspecial_residual_le_of_critical_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (X : Subgroup G) (hXH : X ≤ F.H) (hX : F.H ≤ normalizer (X : Set G))
    (hcX : c.Uα ≤ X) : K F ≤ X := by
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  let N := X.subgroupOf F.H
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hXH).mpr hX
  let M := N.map (starMap F)
  let : M.Normal := (inferInstance : N.Normal).map (starMap F) (QuotientGroup.mk'_surjective _)
  obtain ⟨a,ha,_,ht,hne,hcenter⟩ :=
    exists_extraspecial_critical_actor h hab structural previous hex hcard hexp c hs
  have hPM : P ≤ M := IsExtraspecial.le_normal_of_center_fixing_involution
    P hP (starMap F a) ht hne hcenter M (mem_map_of_mem _ (hcX ha))
  have hres : (pResidual 2 F.H).map (starMap F) = P :=
    map_pResidual_of_surjective 2 (starMap F) (QuotientGroup.mk'_surjective _)
  have hsup : pResidual 2 F.H ≤ N ⊔ pCore 2 F.H := by
    have he := (le_comap_map (starMap F) (pResidual 2 F.H)).trans
      (comap_mono (hres.le.trans hPM))
    simpa only [M,comap_map_eq,starMap,QuotientGroup.ker_mk'] using he
  have hn : pResidual 2 F.H ≤ N := le_of_isPPerfect_of_le_sup_of_normalizes
    (pResidual 2 F.H) N (pCore 2 F.H) (isPPerfect_pResidual 2)
    pCore_isPGroup le_normalizer_of_normal hsup
  intro k hk
  have hk' : (⟨k,(map_subtype_le _ : K F ≤ F.H) hk⟩ : F.H) ∈ (K F).subgroupOf F.H := hk
  exact hn ((residual_subgroupOf F).le hk')

/-- The actual chief action descends faithfully to H/O₂(H) and has degree
six when its point cubic acts nontrivially. Neither faithfulness nor degree
is assumed in the section hypotheses. -/
theorem extraspecial_point_noncentral_chief
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    {B N : Subgroup G} (hB : B ≤ centralizer (F.U : Set G)) (hUN : F.U ≤ N)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W} [ρ.IsIrreducible]
    (s : BinaryConjugationSection F.H B N ρ)
    (hm : ¬ ⁅F.Li L 1,B⁆ ≤ N) :
    ∃ σ : Representation (ZMod 2) (HStar F.H) W,
      σ.comp (starMap F) = ρ ∧ Function.Injective σ ∧
      Module.finrank (ZMod 2) W = 6 ∧
      IsIrreducible (σ.comp (pResidual 2 (HStar F.H)).subtype) := by
  let : Finite W := Finite.of_surjective (fun b : B => (s.coordinates b).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have hk : pCore 2 F.H ≤ ρ.ker := normal_p_subgroup_le_ker ρ _ pCore_isPGroup
  let σ := quotientOfLEKer ρ (pCore 2 F.H) hk
  have hσ : σ.comp (starMap F) = ρ := rfl
  let : σ.IsIrreducible := (quotientOfLEKer_irreducible_iff ρ _ hk).mpr inferInstance
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have hZm : ¬ (center P).map P.subtype ≤ σ.ker := by
    intro hz
    apply hm
    apply (ExtraspecialChiefFactors_section_commutator_iff_kernel ((F.Li_le L 1).trans inf_le_right) s).mpr
    intro a ha
    have he : starMap F a ∈ (center P).map P.subtype := by
      rw [←point_star_eq_residual_center_of_normal h structural hn hex]
      exact mem_map_of_mem _ ha
    exact hz he
  obtain ⟨hf,hfix⟩ := faithful_of_extraspecial_center_not_le_kernel σ P
    (Theory.GroupTheory.centralizer_pResidual_le_of_pCore_eq_bot (pCore_quotient_pCore_eq_bot 2)) hZm
  obtain ⟨c,hs,_,_,_⟩ := exists_selected_critical_geometry_of_point_normal h hab structural previous hn
  obtain ⟨a,ha,_,ht,hne,hcenter⟩ :=
    exists_extraspecial_critical_actor h hab structural previous hex hcard hexp c hs
  have hsmall : fixedCodim σ (zpowers (starMap F a)) ≤ 2 := by
    rw [fixedCodim_zpowers_eq_displacement_rank]
    exact extraspecial_centralizer_section_displacement
      h hab structural previous hex hcard hexp c hs hB hUN s a ha
  exact ⟨σ,hσ,hf,ExtraspecialBinarySix.six_and_irreducible_of_small_involution
    σ hf P hP hfix (starMap F a) ht hne hcenter hsmall⟩


/-- Every H-invariant section centralized by the reciprocal span is
centralized by the original residual K. The two-core is removed using
K = O²(K), so no star-triviality premise is silently substituted. -/
theorem extraspecial_residual_commutator_of_critical_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (X Y : Subgroup G) (hX : F.H ≤ normalizer (X : Set G))
    (hY : F.H ≤ normalizer (Y : Set G)) (hc : ⁅X,c.Uα⁆ ≤ Y) :
    ⁅X,K F⁆ ≤ Y := by
  let D := commutatorPreimage F.H X Y
  have hn : F.H ≤ normalizer (D : Set G) :=
    commutatorPreimage_normalized F.H X Y F.H hY F.H.le_normalizer hX hY
  have ha : c.Uα ≤ D := le_commutatorPreimage
    ((critical_le_Q_at h structural c).trans (Q_le_H F)) (by rw [commutator_comm]; exact hc)
  have hK := extraspecial_residual_le_of_critical_normal
    h hab structural previous hex hcard hexp c hs D (commutatorPreimage_le _ _ _) hn ha
  rw [commutator_comm]
  exact (commutator_mono hK le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hY)

omit [Finite G] in
private theorem ExtraspecialChiefFactors_section_kernel_normalized
    {B N : Subgroup G} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H B N ρ) : F.H ≤ normalizer (N : Set G) := by
  apply le_normalizer_iff.mpr
  intro x hx n hn
  have hnB := s.kernel_le hn
  apply (s.coordinates_eq_one_iff ⟨x*n*x⁻¹,
    (mem_normalizer_iff.mp (s.normalized hx) n).mp hnB⟩).mp
  apply Multiplicative.toAdd.injective
  rw [s.equivariant ⟨x,hx⟩ ⟨n,hnB⟩,(s.coordinates_eq_one_iff _).mpr hn]
  exact map_zero _

/-- A point-noncentral chief factor exhausts the reciprocal displacement.
The full original residual centralizes the centralizer series above and
below that factor. Its full star action and exact quotient kernel remain
part of the conclusion. -/
theorem extraspecial_point_noncentral_chief_localization
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    {B N : Subgroup G} (hB : B ≤ centralizer (F.U : Set G)) (hUN : F.U ≤ N)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W} [ρ.IsIrreducible]
    (s : BinaryConjugationSection F.H B N ρ)
    (hm : ¬ ⁅F.Li L 1,B⁆ ≤ N) :
    (∃ σ : Representation (ZMod 2) (HStar F.H) W,
      σ.comp (starMap F) = ρ ∧ Function.Injective σ ∧
      Module.finrank (ZMod 2) W = 6 ∧
      IsIrreducible (σ.comp (pResidual 2 (HStar F.H)).subtype)) ∧
      ⁅centralizer (F.U : Set G),K F⁆ ≤ B ∧ ⁅N,K F⁆ ≤ F.U := by
  let : Finite W := Finite.of_surjective (fun b : B => (s.coordinates b).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨σ,hσ,hf,hd,hi⟩ := extraspecial_point_noncentral_chief
    h hab structural previous hex hcard hexp hB hUN s hm
  refine ⟨⟨σ,hσ,hf,hd,hi⟩,?_⟩
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  have hExp : Monoid.exponent P = 3 := by
    rw [←Monoid.exponent_eq_of_mulEquiv (residualStarEquiv F),hexp]
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨c,hs,_,_,_⟩ := exists_selected_critical_geometry_of_point_normal h hab structural previous hn
  obtain ⟨a,ha,hane,ht,_,_⟩ :=
    exists_extraspecial_critical_actor h hab structural previous hex hcard hexp c hs
  have hr : 2 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) := by
    by_contra hh
    have hsmall : fixedCodim σ (zpowers (starMap F a)) ≤ 1 := by
      rw [fixedCodim_zpowers_eq_displacement_rank]
      change Module.finrank (ZMod 2) (σ.comp (starMap F) a - 1).range ≤ 1
      rw [hσ]
      omega
    exact hane (ExtraspecialBinarySix.rank_one_actor_trivial σ hf P hP hExp
      (Theory.GroupTheory.centralizer_pResidual_le_of_pCore_eq_bot (pCore_quotient_pCore_eq_bot 2))
      (starMap F a) ht hsmall)
  obtain ⟨_,_,hupper,hlower⟩ := extraspecial_centralizer_section_saturation
    h hab structural previous hex hcard hexp c hs hB hUN s a ha hr
  have hU : F.H ≤ normalizer (F.U : Set G) := le_normalizer_conjugateSpanBy V F.H
  exact ⟨extraspecial_residual_commutator_of_critical_commutator
    h hab structural previous hex hcard hexp c hs _ _
      (hU.trans (normalizer_le_normalizer_centralizer _)) s.normalized hupper,
    extraspecial_residual_commutator_of_critical_commutator
      h hab structural previous hex hcard hexp c hs _ _ (ExtraspecialChiefFactors_section_kernel_normalized s) hU hlower⟩


/-- Once a point-noncentral chief factor occurs, no residual-noncentral
section can lie above or below it in a chief series. This is the uniqueness
step on the literal numerators and denominators. -/
theorem extraspecial_noncentral_sections_not_separated
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    {B N : Subgroup G} (hB : B ≤ centralizer (F.U : Set G)) (hUN : F.U ≤ N)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W} [ρ.IsIrreducible]
    (s : BinaryConjugationSection F.H B N ρ)
    (hm : ¬ ⁅F.Li L 1,B⁆ ≤ N)
    {B' N' : Subgroup G} (hB' : B' ≤ centralizer (F.U : Set G))
    (hUN' : F.U ≤ N') (hm' : ¬ ⁅B',K F⁆ ≤ N') :
    ¬ B ≤ N' ∧ ¬ B' ≤ N := by
  obtain ⟨_,hupper,hlower⟩ := extraspecial_point_noncentral_chief_localization
    h hab structural previous hex hcard hexp hB hUN s hm
  exact ⟨fun hBN' => hm' ((commutator_mono hB' le_rfl).trans (hupper.trans hBN')),
    fun hB'N => hm' ((commutator_mono hB'N le_rfl).trans (hlower.trans hUN'))⟩

/-- Original Heisenberg-residual application. Every literal irreducible
centralizer section either centralizes the point residual, or has the
faithful six-dimensional full star action and is the only possible
residual-noncentral factor along its series. The first branch is retained
explicitly; it is not silently identified with K-centrality. -/
theorem extraspecial_chief_source_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
      (∀ X : Subgroup G, X ≤ F.H → F.H ≤ normalizer (X : Set G) →
        c.Uα ≤ X → K F ≤ X) ∧
      ∀ (B N : Subgroup G), B ≤ centralizer (F.U : Set G) → F.U ≤ N →
      ∀ (W : Type u) [AddCommGroup W] [Module (ZMod 2) W]
        (ρ : Representation (ZMod 2) F.H W),
      ρ.IsIrreducible → BinaryConjugationSection F.H B N ρ →
      ⁅F.Li L 1,B⁆ ≤ N ∨
        ((∃ σ : Representation (ZMod 2) (HStar F.H) W,
          σ.comp (starMap F) = ρ ∧ Function.Injective σ ∧
          Module.finrank (ZMod 2) W = 6 ∧
          IsIrreducible (σ.comp (pResidual 2 (HStar F.H)).subtype)) ∧
        ⁅centralizer (F.U : Set G),K F⁆ ≤ B ∧ ⁅N,K F⁆ ≤ F.U) := by
  classical
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨c,hs,hplace,_,_⟩ := exists_selected_critical_geometry_of_point_normal h hab structural previous hn
  refine ⟨c,hs,hplace,fun X hXH hX hcX =>
    extraspecial_residual_le_of_critical_normal h hab structural previous hex hcard hexp c hs X hXH hX hcX,?_⟩
  intro B N hB hUN W aW mW ρ hi s
  let := hi
  by_cases hm : ⁅F.Li L 1,B⁆ ≤ N
  · exact Or.inl hm
  · exact Or.inr (extraspecial_point_noncentral_chief_localization
      h hab structural previous hex hcard hexp hB hUN s hm)


open NoncentralChiefRefinement in
/-- If the point residual moves the full centralizer modulo U, a genuine
chief interval has order 64 and exactly O₂(H) as its full action kernel.
Its endpoints are normal in the original H and bound all K-movement. -/
theorem extraspecial_exists_point_moved_chief
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (hm : ¬ ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U) :
    ∃ N B : NormalNode F.H, N ⋖ B ∧
      F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
      ¬ ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ N.val.map F.H.subtype ∧
      Nat.card (Section N B) = 64 ∧ (sectionAction N B).ker = pCore 2 F.H ∧
      ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
      ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨τ,⟨sU⟩⟩ := exists_section F
  have hUH := sU.section_le
  have hCH : centralizer (F.U : Set G) ≤ F.H :=
    (centralizer_U_le_core_of_escape h structural (h.flag_escape_at F previous) sU).trans
      (pCoreIn_le 2 F.H)
  have hLH : F.Li L 1 ≤ F.H := (F.Li_le L 1).trans inf_le_right
  have hUn := sU.normalized
  let Z : NormalNode F.H := ⟨F.U.subgroupOf F.H,
    (normal_subgroupOf_iff_le_normalizer hUH).mpr hUn⟩
  let Q : NormalNode F.H := ⟨(centralizer (F.U : Set G)).subgroupOf F.H,
    (normal_subgroupOf_iff_le_normalizer hCH).mpr
      (hUn.trans (normalizer_le_normalizer_centralizer _))⟩
  let R : NormalNode F.H := ⟨(F.Li L 1).subgroupOf F.H,
    pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp⟩
  have hQ : IsPGroup 2 Q.val :=
    ((isPGroup_pCoreIn 2 F.H).to_le
      (centralizer_U_le_core_of_escape h structural (h.flag_escape_at F previous) sU)).comap_subtype
  have hR : IsPPerfect 2 R.val := by
    have hp : IsPPerfect 2 (F.Li L 1) := by
      change IsPPerfect 2 ((pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype)
      exact isPPerfect_embedded_pResidual 2 _
    let e := (subgroupOfEquivOfLe hLH).symm
    exact hp.of_surjective e.toMonoidHom e.surjective
  have hm' : ¬ ⁅Q.val,R.val⁆ ≤ Z.val := by
    intro hc
    apply hm
    have hh := map_mono (f := F.H.subtype) hc
    change (⁅(centralizer (F.U : Set G)).subgroupOf F.H,
      (F.Li L 1).subgroupOf F.H⁆).map F.H.subtype ≤
        (F.U.subgroupOf F.H).map F.H.subtype at hh
    rwa [map_commutator,map_subgroupOf_eq_of_le hCH,map_subgroupOf_eq_of_le hLH,
      map_subgroupOf_eq_of_le hUH] at hh
  obtain ⟨N,B,hZN,hNB,hBQ,hmove⟩ := exists_moved_chief_of_normal_twoPerfect
    Z Q R (subgroupOf_mono F.H F.U.le_centralizer) hQ hR hm'
  have hUN : F.U ≤ N.val.map F.H.subtype := by
    have hh := map_mono (f := F.H.subtype) hZN
    change (F.U.subgroupOf F.H).map F.H.subtype ≤ _ at hh
    rwa [map_subgroupOf_eq_of_le hUH] at hh
  have hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G) := by
    have hh := map_mono (f := F.H.subtype) hBQ
    change _ ≤ ((centralizer (F.U : Set G)).subgroupOf F.H).map F.H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hCH] at hh
  let : IsElementaryAbelian 2 (Section N B) := chief_elementary N B hNB (hQ.to_le hBQ)
  let ρ := binarySectionRepresentation N B
  let : ρ.IsIrreducible := binarySection_irreducible N B hNB
  let s := ambientBinarySection F.H N B hNB.le
  have hpoint : ¬ ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ N.val.map F.H.subtype := by
    intro hc
    apply hmove
    intro x hx
    have hh := mem_map_of_mem F.H.subtype hx
    change (x : G) ∈ (⁅B.val,(F.Li L 1).subgroupOf F.H⁆).map F.H.subtype at hh
    rw [map_commutator,map_subgroupOf_eq_of_le hLH,commutator_comm] at hh
    exact (mem_map_iff_mem F.H.subtype_injective).mp (hc hh)
  obtain ⟨⟨σ,hσ,hf,hd,_⟩,hupper,hlower⟩ := extraspecial_point_noncentral_chief_localization
    h hab structural previous hex hcard hexp hBC hUN s hpoint
  have hk : ρ.ker = pCore 2 F.H := by
    change (binarySectionRepresentation N B).ker = pCore 2 F.H
    rw [←hσ,MonoidHom.ker_comp_of_injective _ _ hf,starMap,QuotientGroup.ker_mk']
  have hact : (sectionAction N B).ker = ρ.ker := by
    ext a
    change sectionAction N B a = 1 ↔ ρ a = 1
    constructor
    · intro ha
      ext w
      exact congrArg (fun f : MulAut (Section N B) => f w.toMul) ha
    · intro ha
      ext w
      exact congrArg Additive.toMul
        (congrArg (fun f : Module.End (ZMod 2) (Additive (Section N B)) => f (Additive.ofMul w)) ha)
  refine ⟨N,B,hNB,hUN,hBC,hpoint,?_,hact.trans hk,hupper,hlower⟩
  change Nat.card (Additive (Section N B)) = 64
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd]
  norm_num

open NoncentralChiefRefinement in
/-- The actual Heisenberg residual supplies the chief interval and all its
coordinates whenever the point residual moves C_H(U)/U. The remaining
point-central branch is stated on that same original quotient. -/
theorem extraspecial_centralizer_chief_source
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U ∨
      ∃ N B : NormalNode F.H, N ⋖ B ∧
        F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
        ¬ ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ N.val.map F.H.subtype ∧
        Nat.card (Section N B) = 64 ∧ (sectionAction N B).ker = pCore 2 F.H ∧
        ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
        ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U := by
  classical
  by_cases hm : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U
  · exact Or.inl hm
  obtain ⟨e⟩ := he
  apply Or.inr
  exact extraspecial_exists_point_moved_chief h hab structural previous
    ((HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm)
    ((Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3)))
    ((Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))) hm

/-- A point-central chief section moved by K has degree two or four.
Its literal star action kills the extraspecial center, and the actual residual
action quotient is elementary abelian with order dividing nine. -/
theorem extraspecial_point_central_chief_degree
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    {B N : Subgroup G} (hB : B ≤ centralizer (F.U : Set G)) (hUN : F.U ≤ N)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W} [ρ.IsIrreducible]
    (s : BinaryConjugationSection F.H B N ρ)
    (hp : ⁅B,F.Li L 1⁆ ≤ N) (hm : ¬ ⁅B,K F⁆ ≤ N) :
    ∃ σ : Representation (ZMod 2) (HStar F.H) W,
      σ.comp (starMap F) = ρ ∧
      (center (pResidual 2 (HStar F.H))).map (pResidual 2 (HStar F.H)).subtype ≤ σ.ker ∧
      ¬ pResidual 2 (HStar F.H) ≤ σ.ker ∧
      IsElementaryAbelian 3 ((pResidual 2 (HStar F.H)) ⧸
        (σ.comp (pResidual 2 (HStar F.H)).subtype).ker) ∧
      Nat.card ((pResidual 2 (HStar F.H)) ⧸
        (σ.comp (pResidual 2 (HStar F.H)).subtype).ker) ∣ 9 ∧
      (Module.finrank (ZMod 2) W = 2 ∨ Module.finrank (ZMod 2) W = 4) := by
  let : Finite W := Finite.of_surjective (fun b : B => (s.coordinates b).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have hk : pCore 2 F.H ≤ ρ.ker := normal_p_subgroup_le_ker ρ _ pCore_isPGroup
  let σ := quotientOfLEKer ρ (pCore 2 F.H) hk
  have hσ : σ.comp (starMap F) = ρ := rfl
  let : σ.IsIrreducible := (quotientOfLEKer_irreducible_iff ρ _ hk).mpr inferInstance
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have hZ : (center P).map P.subtype ≤ σ.ker := by
    rw [←point_star_eq_residual_center_of_normal h structural hn hex]
    rintro _ ⟨a,ha,rfl⟩
    change a ∈ ρ.ker
    apply (s.action_mem_ker_iff a).mpr
    intro b hb
    exact commutator_le.mp (by rw [commutator_comm]; exact hp) (a : G) ha b hb
  have hmove : ¬ P ≤ σ.ker := by
    intro hPker
    apply hm
    rw [commutator_comm]
    apply commutator_le.mpr
    intro k hk b hb
    let a : F.H := ⟨k,(map_subtype_le _ : K F ≤ F.H) hk⟩
    have hkres : a ∈ pResidual 2 F.H := by
      rw [←residual_subgroupOf F]
      exact hk
    have haker : a ∈ ρ.ker := hPker
      (map_pResidual_le 2 (starMap F) (mem_map_of_mem (starMap F) hkres))
    exact (s.action_mem_ker_iff a).mp haker b hb
  obtain ⟨c,hs,_,_,_⟩ := exists_selected_critical_geometry_of_point_normal h hab structural previous hn
  obtain ⟨a,ha,_,ht,hne,hcenter⟩ :=
    exists_extraspecial_critical_actor h hab structural previous hex hcard hexp c hs
  obtain ⟨hel,hquot⟩ := extraspecial_center_kernel_quotient σ P hP hZ
  refine ⟨σ,hσ,hZ,hmove,hel,hquot,?_⟩
  exact extraspecial_center_kernel_small_involution_degree σ P hP hZ hmove
    (starMap F a) ht hne hcenter
    (extraspecial_centralizer_section_displacement h hab structural previous
      hex hcard hexp c hs hB hUN s a ha)


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The remaining point-central chief intervals in the extraspecial branch

If L₁ centralizes C_H(U)/U but K does not, normal two-perfect movement
constructs an actual H-chief interval inside that quotient. The small
involution calculation forces its order to be four or sixteen. Its
literal conjugation kernel contains O₂(H)L₁. Thus this branch cannot
be treated as the faithful order-64 interval already constructed when
L₁ moves the quotient.

The final application starts with the actual Heisenberg residual
isomorphism and exposes all cases: K centralizes the quotient, an
order-64 chief interval has exact kernel O₂(H) and localizes movement,
or the remaining point-central interval has order four or sixteen.
No chief section or action witness is assumed. Excluding the last case,
the rest of the extraspecial exclusion and the residual classification
through 14.7.52 remain obligations of the local reduction.

Source: Aschbacher–Smith, 14.7.20(2), printed p.1049. The smaller intervals
are an intermediate reduction, not an extra alternative in that theorem.
Numerators, denominators and all normalities use the original H.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

open NoncentralChiefRefinement in
/-- A K-moved interval in the point-central branch is small. Both normal
endpoints, the quotient order, and the original kernel containment are retained. -/
theorem extraspecial_exists_point_central_moved_chief
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U)
    (hm : ¬ ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U) :
    ∃ N B : NormalNode F.H, N ⋖ B ∧
      F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
      ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype ∧
      (Nat.card (Section N B) = 4 ∨ Nat.card (Section N B) = 16) ∧
      pCore 2 F.H ⊔ (F.Li L 1).subgroupOf F.H ≤ (sectionAction N B).ker := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨τ,⟨sU⟩⟩ := exists_section F
  have hUH := sU.section_le
  have hCH : centralizer (F.U : Set G) ≤ F.H :=
    (centralizer_U_le_core_of_escape h structural (h.flag_escape_at F previous) sU).trans
      (pCoreIn_le 2 F.H)
  have hUn := sU.normalized
  let Z : NormalNode F.H := ⟨F.U.subgroupOf F.H,
    (normal_subgroupOf_iff_le_normalizer hUH).mpr hUn⟩
  let Q : NormalNode F.H := ⟨(centralizer (F.U : Set G)).subgroupOf F.H,
    (normal_subgroupOf_iff_le_normalizer hCH).mpr
      (hUn.trans (normalizer_le_normalizer_centralizer _))⟩
  let R : NormalNode F.H := ⟨pResidual 2 F.H,(inferInstance : (pResidual 2 F.H).Normal)⟩
  have hRmap : R.val.map F.H.subtype = K F := rfl
  have hQ : IsPGroup 2 Q.val :=
    ((isPGroup_pCoreIn 2 F.H).to_le
      (centralizer_U_le_core_of_escape h structural (h.flag_escape_at F previous) sU)).comap_subtype
  have hm' : ¬ ⁅Q.val,R.val⁆ ≤ Z.val := by
    intro hc
    apply hm
    have hh := map_mono (f := F.H.subtype) hc
    rw [map_commutator,hRmap] at hh
    change ⁅((centralizer (F.U : Set G)).subgroupOf F.H).map F.H.subtype,K F⁆ ≤
      (F.U.subgroupOf F.H).map F.H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hCH,map_subgroupOf_eq_of_le hUH] at hh
  obtain ⟨N,B,hZN,hNB,hBQ,hmove⟩ := exists_moved_chief_of_normal_twoPerfect
    Z Q R (subgroupOf_mono F.H F.U.le_centralizer) hQ (isPPerfect_pResidual 2) hm'
  have hUN : F.U ≤ N.val.map F.H.subtype := by
    have hh := map_mono (f := F.H.subtype) hZN
    change (F.U.subgroupOf F.H).map F.H.subtype ≤ _ at hh
    rwa [map_subgroupOf_eq_of_le hUH] at hh
  have hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G) := by
    have hh := map_mono (f := F.H.subtype) hBQ
    change _ ≤ ((centralizer (F.U : Set G)).subgroupOf F.H).map F.H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hCH] at hh
  let : IsElementaryAbelian 2 (Section N B) := chief_elementary N B hNB (hQ.to_le hBQ)
  let ρ := binarySectionRepresentation N B
  let : ρ.IsIrreducible := binarySection_irreducible N B hNB
  let s := ambientBinarySection F.H N B hNB.le
  have hKmove : ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype := by
    intro hc
    apply hmove
    intro x hx
    have hh := mem_map_of_mem F.H.subtype hx
    rw [map_commutator,hRmap] at hh
    exact (mem_map_iff_mem F.H.subtype_injective).mp (hc hh)
  have hpoint : ⁅B.val.map F.H.subtype,F.Li L 1⁆ ≤ N.val.map F.H.subtype :=
    (commutator_mono hBC le_rfl).trans (hp.trans hUN)
  obtain ⟨σ,hσ,_,_,_,_,hd⟩ := extraspecial_point_central_chief_degree
    h hab structural previous hex hcard hexp hBC hUN s hpoint hKmove
  have hact : (sectionAction N B).ker = ρ.ker := by
    ext a
    change sectionAction N B a = 1 ↔ ρ a = 1
    constructor
    · intro ha
      ext w
      exact congrArg (fun f : MulAut (Section N B) => f w.toMul) ha
    · intro ha
      ext w
      exact congrArg Additive.toMul
        (congrArg (fun f : Module.End (ZMod 2) (Additive (Section N B)) => f (Additive.ofMul w)) ha)
  refine ⟨N,B,hNB,hUN,hBC,hKmove,?_,?_⟩
  · change Nat.card (Additive (Section N B)) = 4 ∨ Nat.card (Additive (Section N B)) = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    rcases hd with hd | hd
    · exact Or.inl (by rw [hd]; norm_num)
    · exact Or.inr (by rw [hd]; norm_num)
  · rw [hact]
    refine sup_le (normal_p_subgroup_le_ker ρ _ pCore_isPGroup) ?_
    intro a ha
    apply (s.action_mem_ker_iff a).mpr
    intro b hb
    exact commutator_le.mp (by rw [commutator_comm]; exact hpoint) (a : G) ha b hb


open NoncentralChiefRefinement in
/-- Original Heisenberg application with every remaining action branch exposed.
The small point-central interval is an unresolved exclusion, not the faithful
six-dimensional alternative of source 14.7.20(2). -/
theorem extraspecial_centralizer_chief_alternatives
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U ∨
      ∃ N B : NormalNode F.H, N ⋖ B ∧
        F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
        ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype ∧
        ((Nat.card (Section N B) = 64 ∧ (sectionAction N B).ker = pCore 2 F.H ∧
          ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
          ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U) ∨
         (⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U ∧
          (Nat.card (Section N B) = 4 ∨ Nat.card (Section N B) = 16) ∧
          pCore 2 F.H ⊔ (F.Li L 1).subgroupOf F.H ≤ (sectionAction N B).ker)) := by
  classical
  by_cases hc : ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U
  · exact Or.inl hc
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  apply Or.inr
  by_cases hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U
  · obtain ⟨N,B,hNB,hUN,hBC,hm,hd,hker⟩ := extraspecial_exists_point_central_moved_chief
      h hab structural previous hex hcard hexp hp hc
    exact ⟨N,B,hNB,hUN,hBC,hm,Or.inr ⟨hp,hd,hker⟩⟩
  · obtain ⟨N,B,hNB,hUN,hBC,hm,hd,hker,hu,hl⟩ := extraspecial_exists_point_moved_chief
      h hab structural previous hex hcard hexp hp
    refine ⟨N,B,hNB,hUN,hBC,?_,Or.inl ⟨hd,hker,hu,hl⟩⟩
    intro hh
    apply hm
    rw [commutator_comm]
    exact (commutator_mono le_rfl (pointResidual_le F)).trans hh

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end

/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Exact kernels of the remaining small extraspecial chief intervals

A point-central, K-moved chief interval in C_H(U)/U has dimension two
or four. The literal star residual image has order three in dimension
two, with residual kernel of order nine. In dimension four its image
has order nine and the full star kernel is exactly L₁*, the embedded
extraspecial center. Pullback identifies the original H-action kernel
as O₂(H)L₁, retaining the original quotient map.

In the four-dimensional case the selected reciprocal involution moves
at least two dimensions, by inversion on the elementary residual image.
The previously proved centralizer bound is therefore saturated. Its
upper and lower centralization, together with reciprocal normal
generation, confines all original K-movement to this chief interval.

The final Heisenberg application constructs the interval and gives its
exact original action data. It preserves the order-64 faithful branch.
The order-four and order-sixteen branches still require exclusion from
the original ambient hypotheses; this is not source 14.7.20(2) or the
residual classification through 14.7.52.

Source: Aschbacher–Smith, 14.7.20(2), printed p.1049, with the small
central-quotient representations distinguished in D.2.17, printed p.188.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The small chief action retains its exact residual image and, in
dimension four, its full star kernel. -/
theorem extraspecial_point_central_chief_kernel
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    {B N : Subgroup G} (hB : B ≤ centralizer (F.U : Set G)) (hUN : F.U ≤ N)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W} [ρ.IsIrreducible]
    (s : BinaryConjugationSection F.H B N ρ)
    (hp : ⁅B,F.Li L 1⁆ ≤ N) (hm : ¬ ⁅B,K F⁆ ≤ N) :
    ∃ σ : Representation (ZMod 2) (HStar F.H) W,
      σ.comp (starMap F) = ρ ∧
      ((Module.finrank (ZMod 2) W = 2 ∧
        Nat.card ((pResidual 2 (HStar F.H)) ⧸
          (σ.comp (pResidual 2 (HStar F.H)).subtype).ker) = 3 ∧
        Nat.card (σ.ker.subgroupOf (pResidual 2 (HStar F.H))) = 9) ∨
      (Module.finrank (ZMod 2) W = 4 ∧
        Nat.card ((pResidual 2 (HStar F.H)) ⧸
          (σ.comp (pResidual 2 (HStar F.H)).subtype).ker) = 9 ∧
        σ.ker = star F (F.Li L 1))) := by
  let : Finite W := Finite.of_surjective (fun b : B => (s.coordinates b).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨σ,hσ,hZ,hmP,_,_,hd⟩ := extraspecial_point_central_chief_degree
    h hab structural previous hex hcard hexp hB hUN s hp hm
  let : σ.IsIrreducible := (irreducible_comp_surjective_iff (starMap F)
    (QuotientGroup.mk'_surjective _) σ).mp (hσ ▸ inferInstance)
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  refine ⟨σ,hσ,?_⟩
  rcases extraspecial_center_kernel_residual_card σ P hP rfl hZ hmP hd with h2 | h4
  · exact Or.inl h2
  · refine Or.inr ⟨h4.1,h4.2.1,?_⟩
    rw [extraspecial_full_kernel_of_restriction_kernel σ P
      (Theory.GroupTheory.centralizer_pResidual_le_of_pCore_eq_bot
        (pCore_quotient_pCore_eq_bot 2)) h4.2.2]
    exact (point_star_eq_center_of_extraspecial_residual h hab structural previous hex hcard hexp).symm


/-- A four-dimensional point-central chief factor exhausts the original
K-movement above and below its literal interval. -/
theorem extraspecial_four_chief_localization
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    {B N : Subgroup G} (hB : B ≤ centralizer (F.U : Set G)) (hUN : F.U ≤ N)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W} [ρ.IsIrreducible]
    (s : BinaryConjugationSection F.H B N ρ)
    (hp : ⁅B,F.Li L 1⁆ ≤ N) (hm : ¬ ⁅B,K F⁆ ≤ N)
    (hd : Module.finrank (ZMod 2) W = 4) :
    ⁅centralizer (F.U : Set G),K F⁆ ≤ B ∧ ⁅N,K F⁆ ≤ F.U := by
  let : Finite W := Finite.of_surjective (fun b : B => (s.coordinates b).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨σ,hσ,hZ,hmP,_,_,_⟩ := extraspecial_point_central_chief_degree
    h hab structural previous hex hcard hexp hB hUN s hp hm
  subst ρ
  let : σ.IsIrreducible := (irreducible_comp_surjective_iff (starMap F)
    (QuotientGroup.mk'_surjective _) σ).mp inferInstance
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨c,hs,_,_,_⟩ := exists_selected_critical_geometry_of_point_normal h hab structural previous hn
  obtain ⟨a,ha,_,ht,hne,hcenter⟩ :=
    exists_extraspecial_critical_actor h hab structural previous hex hcard hexp c hs
  have hb := extraspecial_center_kernel_dimension_bound σ P hP hZ hmP
    (starMap F a) ht hne hcenter
  have hr : 2 ≤ Module.finrank (ZMod 2) (LinearMap.range (σ (starMap F a) - 1)) := by
    rw [hd] at hb
    omega
  obtain ⟨_,_,hupper,hlower⟩ := extraspecial_centralizer_section_saturation
    h hab structural previous hex hcard hexp c hs hB hUN s a ha hr
  have hU : F.H ≤ normalizer (F.U : Set G) := le_normalizer_conjugateSpanBy V F.H
  have hN : F.H ≤ normalizer (N : Set G) := by
    apply le_normalizer_iff.mpr
    intro x hx n hnN
    have hnB := s.kernel_le hnN
    apply (s.coordinates_eq_one_iff ⟨x*n*x⁻¹,
      (mem_normalizer_iff.mp (s.normalized hx) n).mp hnB⟩).mp
    apply Multiplicative.toAdd.injective
    rw [s.equivariant ⟨x,hx⟩ ⟨n,hnB⟩,(s.coordinates_eq_one_iff _).mpr hnN]
    exact map_zero _
  exact ⟨extraspecial_residual_commutator_of_critical_commutator
    h hab structural previous hex hcard hexp c hs _ _
      (hU.trans (normalizer_le_normalizer_centralizer _)) s.normalized hupper,
    extraspecial_residual_commutator_of_critical_commutator
      h hab structural previous hex hcard hexp c hs _ _ hN hU hlower⟩


open NoncentralChiefRefinement in
/-- Construct the small chief interval and pull its precise action kernel
back to the original H, keeping its residual index and adjacent layers. -/
theorem extraspecial_point_central_interval_kernels
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U)
    (hm : ¬ ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U) :
    ∃ N B : NormalNode F.H, N ⋖ B ∧
      F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
      ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype ∧
      pCore 2 F.H ⊔ (F.Li L 1).subgroupOf F.H ≤ (sectionAction N B).ker ∧
      ((Nat.card (Section N B) = 4 ∧
        (sectionAction N B).ker.relIndex (pResidual 2 F.H) = 3) ∨
       (Nat.card (Section N B) = 16 ∧
        (sectionAction N B).ker = pCore 2 F.H ⊔ (F.Li L 1).subgroupOf F.H ∧
        ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
        ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U)) := by
  obtain ⟨N,B,hNB,hUN,hBC,hmove,_,hker⟩ := extraspecial_exists_point_central_moved_chief
    h hab structural previous hex hcard hexp hp hm
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨τ,⟨sU⟩⟩ := exists_section F
  let Q := (centralizer (F.U : Set G)).subgroupOf F.H
  have hQ : IsPGroup 2 Q :=
    ((isPGroup_pCoreIn 2 F.H).to_le
      (centralizer_U_le_core_of_escape h structural (h.flag_escape_at F previous) sU)).comap_subtype
  have hBQ : B.val ≤ Q := fun b hb => hBC (mem_map_of_mem F.H.subtype hb)
  let : IsElementaryAbelian 2 (Section N B) := chief_elementary N B hNB (hQ.to_le hBQ)
  let ρ := binarySectionRepresentation N B
  let : ρ.IsIrreducible := binarySection_irreducible N B hNB
  let s := ambientBinarySection F.H N B hNB.le
  have hpoint : ⁅B.val.map F.H.subtype,F.Li L 1⁆ ≤ N.val.map F.H.subtype :=
    (commutator_mono hBC le_rfl).trans (hp.trans hUN)
  obtain ⟨σ,hσ,hcases⟩ := extraspecial_point_central_chief_kernel
    h hab structural previous hex hcard hexp hBC hUN s hpoint hmove
  have hact : (sectionAction N B).ker = ρ.ker := by
    ext a
    change sectionAction N B a = 1 ↔ ρ a = 1
    constructor
    · intro ha
      ext w
      exact congrArg (fun f : MulAut (Section N B) => f w.toMul) ha
    · intro ha
      ext w
      exact congrArg Additive.toMul
        (congrArg (fun f : Module.End (ZMod 2) (Additive (Section N B)) => f (Additive.ofMul w)) ha)
  refine ⟨N,B,hNB,hUN,hBC,hmove,hker,?_⟩
  rcases hcases with h2 | h4
  · refine Or.inl ⟨?_,?_⟩
    · change Nat.card (Additive (Section N B)) = 4
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,h2.1]
      norm_num
    · rw [hact]
      change (binarySectionRepresentation N B).ker.relIndex (pResidual 2 F.H) = 3
      rw [←hσ,←MonoidHom.comap_ker,relIndex_comap,
        map_pResidual_of_surjective 2 (starMap F) (QuotientGroup.mk'_surjective _)]
      exact h2.2.1
  · refine Or.inr ⟨?_,?_,extraspecial_four_chief_localization
      h hab structural previous hex hcard hexp hBC hUN s hpoint hmove h4.1⟩
    · change Nat.card (Additive (Section N B)) = 16
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,h4.1]
      norm_num
    · rw [hact]
      change (binarySectionRepresentation N B).ker = _
      rw [←hσ,←MonoidHom.comap_ker,h4.2.2]
      change (((F.Li L 1).subgroupOf F.H).map (starMap F)).comap (starMap F) = _
      rw [comap_map_eq,starMap,QuotientGroup.ker_mk',sup_comm]


open NoncentralChiefRefinement in
/-- Original-group application with exact kernels for every chief alternative.
The small point-central branches are retained as outstanding exclusions. -/
theorem extraspecial_centralizer_exact_chief_alternatives
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U ∨
      ∃ N B : NormalNode F.H, N ⋖ B ∧
        F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
        ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype ∧
        ((Nat.card (Section N B) = 64 ∧ (sectionAction N B).ker = pCore 2 F.H ∧
          ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
          ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U) ∨
         (⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U ∧
          pCore 2 F.H ⊔ (F.Li L 1).subgroupOf F.H ≤ (sectionAction N B).ker ∧
          ((Nat.card (Section N B) = 4 ∧
            (sectionAction N B).ker.relIndex (pResidual 2 F.H) = 3) ∨
           (Nat.card (Section N B) = 16 ∧
            (sectionAction N B).ker = pCore 2 F.H ⊔ (F.Li L 1).subgroupOf F.H ∧
            ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
            ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U)))) := by
  classical
  by_cases hc : ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U
  · exact Or.inl hc
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  apply Or.inr
  by_cases hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U
  · obtain ⟨N,B,hNB,hUN,hBC,hm,hker,hsmall⟩ := extraspecial_point_central_interval_kernels
      h hab structural previous hex hcard hexp hp hc
    exact ⟨N,B,hNB,hUN,hBC,hm,Or.inr ⟨hp,hker,hsmall⟩⟩
  · obtain ⟨N,B,hNB,hUN,hBC,hm,hd,hker,hu,hl⟩ := extraspecial_exists_point_moved_chief
      h hab structural previous hex hcard hexp hp
    refine ⟨N,B,hNB,hUN,hBC,?_,Or.inl ⟨hd,hker,hu,hl⟩⟩
    intro hh
    apply hm
    rw [commutator_comm]
    exact (commutator_mono le_rfl (pointResidual_le F)).trans hh

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end

/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The star Sylow restriction from an order-four chief interval

In the point-central extraspecial branch, an order-four chief interval
has a normal residual kernel of order nine. That kernel defines a stable
line in the extraspecial Frattini quotient. Coprime complements give two
Sylow-invariant generating cubics, so the faithful star Sylow action is
elementary abelian of order at most four. Original critical reciprocity
supplies divisibility by four, and the literal point-core index is two.
Thus the star Sylow has order four and the point-core image has order two.

The original Heisenberg application constructs the binary chief action and
retains the existing exact kernels and localization in all three dimensions.
If the point-core image is known to have order different from two, the
order-four case is excluded and point-central movement is confined to an
order-sixteen interval with kernel O₂(H)L₁. The required source Sylow
restriction, the order-sixteen exclusion, and the remaining classification
through 14.7.52 are still unproved; none is assumed by the unconditional
original-group application.

Source: Aschbacher–Smith, 14.7.15(2) and 14.7.20(2), printed pp.1047–1049.
This is a restriction on the remaining branch, not a proof of either source
statement from the chief interval's order alone.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- A point-central chief factor of binary dimension two forces the original
star Sylow to be elementary of order four and its point core to have order two. -/
theorem extraspecial_two_chief_star_orders
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    {B N : Subgroup G} (hB : B ≤ centralizer (F.U : Set G)) (hUN : F.U ≤ N)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W} [ρ.IsIrreducible]
    (s : BinaryConjugationSection F.H B N ρ)
    (hp : ⁅B,F.Li L 1⁆ ≤ N) (hm : ¬ ⁅B,K F⁆ ≤ N)
    (hd : Module.finrank (ZMod 2) W = 2) :
    IsElementaryAbelian 2 (star F (T : Subgroup G)) ∧
      Nat.card (star F (T : Subgroup G)) = 4 ∧
      Nat.card (star F (F.Ri L 1)) = 2 := by
  let : Finite W := Finite.of_surjective (fun b : B => (s.coordinates b).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨σ,hσ,hZ,hmP,_,_,_⟩ := extraspecial_point_central_chief_degree
    h hab structural previous hex hcard hexp hB hUN s hp hm
  let : σ.IsIrreducible := (irreducible_comp_surjective_iff (starMap F)
    (QuotientGroup.mk'_surjective _) σ).mp (hσ ▸ inferInstance)
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  have heP : Monoid.exponent P = 3 :=
    (Monoid.exponent_eq_of_mulEquiv (residualStarEquiv F)).symm.trans hexp
  have hN : Nat.card (σ.ker.subgroupOf P) = 9 := by
    rcases extraspecial_center_kernel_residual_card σ P hP rfl hZ hmP (Or.inl hd) with h2 | h4
    · exact h2.2.2
    · omega
  have hS2 : IsPGroup 2 (star F (T : Subgroup G)) :=
    T.isPGroup'.comap_subtype.map (starMap F)
  obtain ⟨hel,hbound⟩ := IsExtraspecial.small_two_subgroup_of_normal_nine_intersection P hP heP
    (Theory.GroupTheory.centralizer_pResidual_le_of_pCore_eq_bot (pCore_quotient_pCore_eq_bot 2))
    σ.ker hN (fun z hz => hZ (mem_map_of_mem P.subtype hz)) _ hS2
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨c,hs,_,_,_⟩ := exists_selected_critical_geometry_of_point_normal h hab structural previous hn
  let S : Sylow 2 (HStar F.H) := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective (pCore 2 F.H))
  have hSc : (S : Subgroup (HStar F.H)) = star F (T : Subgroup G) := rfl
  have hdiv : 4 ∣ Nat.card (star F (T : Subgroup G)) := by
    rw [←hSc]
    exact four_dvd_star_sylow_card h structural c S
  have hsize : Nat.card (star F (T : Subgroup G)) = 4 :=
    Nat.le_antisymm hbound (Nat.le_of_dvd Nat.card_pos hdiv)
  have hRT : star F (F.Ri L 1) ≤ star F (T : Subgroup G) := by
    rw [point_core_star_eq_centralizer_of_normal h structural hn]
    exact inf_le_left
  have hcount := relIndex_mul_card_of_le hRT
  rw [point_core_star_index_two_of_normal h structural hn,hsize] at hcount
  exact ⟨hel,hsize,by omega⟩

open NoncentralChiefRefinement in
/-- Apply the Sylow restriction to the literal original order-four chief
interval, constructing its binary action rather than assuming a module. -/
theorem extraspecial_four_interval_star_orders
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (N B : NormalNode F.H) (hNB : N ⋖ B)
    (hUN : F.U ≤ N.val.map F.H.subtype)
    (hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G))
    (hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U)
    (hm : ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype)
    (hc : Nat.card (Section N B) = 4) :
    IsElementaryAbelian 2 (star F (T : Subgroup G)) ∧
      Nat.card (star F (T : Subgroup G)) = 4 ∧
      Nat.card (star F (F.Ri L 1)) = 2 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨τ,⟨sU⟩⟩ := exists_section F
  let Q := (centralizer (F.U : Set G)).subgroupOf F.H
  have hQ : IsPGroup 2 Q :=
    ((isPGroup_pCoreIn 2 F.H).to_le
      (centralizer_U_le_core_of_escape h structural (h.flag_escape_at F previous) sU)).comap_subtype
  have hBQ : B.val ≤ Q := fun b hb => hBC (mem_map_of_mem F.H.subtype hb)
  let : IsElementaryAbelian 2 (Section N B) := chief_elementary N B hNB (hQ.to_le hBQ)
  let ρ := binarySectionRepresentation N B
  let : ρ.IsIrreducible := binarySection_irreducible N B hNB
  let s := ambientBinarySection F.H N B hNB.le
  have hd : Module.finrank (ZMod 2) (Additive (Section N B)) = 2 := by
    have he : Nat.card (Additive (Section N B)) = 4 := hc
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at he
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) he
  exact extraspecial_two_chief_star_orders h hab structural previous hex hcard hexp hBC hUN s
    ((commutator_mono hBC le_rfl).trans (hp.trans hUN)) hm hd


open NoncentralChiefRefinement in
/-- The actual Heisenberg branch with exact chief kernels and the forced
original Sylow structure in the order-four case. No irreducibility of the
Sylow action on the extraspecial Frattini quotient is assumed. -/
theorem extraspecial_centralizer_chief_sylow_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U ∨
      ∃ N B : NormalNode F.H, N ⋖ B ∧
        F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
        ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype ∧
        ((Nat.card (Section N B) = 64 ∧ (sectionAction N B).ker = pCore 2 F.H ∧
          ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
          ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U) ∨
         (⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U ∧
          pCore 2 F.H ⊔ (F.Li L 1).subgroupOf F.H ≤ (sectionAction N B).ker ∧
          ((Nat.card (Section N B) = 4 ∧
            (sectionAction N B).ker.relIndex (pResidual 2 F.H) = 3 ∧
            IsElementaryAbelian 2 (star F (T : Subgroup G)) ∧
            Nat.card (star F (T : Subgroup G)) = 4 ∧
            Nat.card (star F (F.Ri L 1)) = 2) ∨
           (Nat.card (Section N B) = 16 ∧
            (sectionAction N B).ker = pCore 2 F.H ⊔ (F.Li L 1).subgroupOf F.H ∧
            ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
            ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U)))) := by
  rcases extraspecial_centralizer_exact_chief_alternatives h hab structural previous he with hc | hc
  · exact Or.inl hc
  obtain ⟨N,B,hNB,hUN,hBC,hm,hcases⟩ := hc
  refine Or.inr ⟨N,B,hNB,hUN,hBC,hm,?_⟩
  rcases hcases with h64 | ⟨hp,hker,h4 | h16⟩
  · exact Or.inl h64
  · obtain ⟨e⟩ := he
    have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
      (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
    have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
      (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
    have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
      (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
    exact Or.inr ⟨hp,hker,Or.inl ⟨h4.1,h4.2,
      extraspecial_four_interval_star_orders h hab structural previous hex hcard hexp
        N B hNB hUN hBC hp hm h4.1⟩⟩
  · exact Or.inr ⟨hp,hker,Or.inr h16⟩

open NoncentralChiefRefinement in
/-- Once the order-two point-core image is excluded, the point-central
movement has an order-sixteen interval exhausting K-movement, with original action
kernel O₂(H)L₁. The remaining point-core bound and this interval's exclusion
are explicit source obligations, not consequences of this conditional lemma. -/
theorem extraspecial_point_central_sixteen_of_point_core_ne_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (hR : Nat.card (star F (F.Ri L 1)) ≠ 2)
    (hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U)
    (hm : ¬ ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U) :
    ∃ N B : NormalNode F.H, N ⋖ B ∧
      F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
      ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype ∧
      Nat.card (Section N B) = 16 ∧
      (sectionAction N B).ker = pCore 2 F.H ⊔ (F.Li L 1).subgroupOf F.H ∧
      ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
      ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U := by
  obtain ⟨N,B,hNB,hUN,hBC,hmove,_,h4 | h16⟩ :=
    extraspecial_point_central_interval_kernels h hab structural previous hex hcard hexp hp hm
  · exact (hR (extraspecial_four_interval_star_orders h hab structural previous
      hex hcard hexp N B hNB hUN hBC hp hmove h4.1).2.2).elim
  · exact ⟨N,B,hNB,hUN,hBC,hmove,h16⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end

/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Original cubic lifts from the remaining order-four chief interval

The kernel of the binary chief action meets the extraspecial star residual
in order nine. Its stable Frattini line supplies two Sylow-normalized cubic
generators. Taking two-residuals of their literal preimages produces two
subgroups of the original H generating O²(H), with exact intrinsic two-cores
as kernels of the restricted star maps.

Since H = O²(H)T escapes N_G(L) while T lies there, at least one of these
lifts escapes N_G(L). The ambient subgroup is two-perfect, is T-invariant,
and normalizes L₁ by the already proved relative point normality. Its
quotient by its own two-core has order three, and its star image is a
noncentral cubic. The final theorem constructs the action on the literal
chief interval; no module or point-normality callback is assumed.

This supplies the original cubic subgroups needed in the reducible Sylow
step of Aschbacher–Smith 14.7.9 and 14.7.15(2), printed pp.1045–1047,
as it arises in the remaining order-four case of 14.7.20(2), p.1049.
The S₃ quotient of YT and the geometric containment argument of 14.5.3(2)
remain to be proved. Consequently these lifts do not yet exclude the
order-four interval or prove the residual classification through 14.7.52.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The order-four chief action supplies cubic generators in the original H. -/
theorem extraspecial_two_chief_cubic_lifts
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    {B N : Subgroup G} (hB : B ≤ centralizer (F.U : Set G)) (hUN : F.U ≤ N)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W} [ρ.IsIrreducible]
    (s : BinaryConjugationSection F.H B N ρ)
    (hp : ⁅B,F.Li L 1⁆ ≤ N) (hm : ¬ ⁅B,K F⁆ ≤ N)
    (hd : Module.finrank (ZMod 2) W = 2) :
    ∃ A B : Subgroup F.H, A ⊔ B = pResidual 2 F.H ∧
      (IsPPerfect 2 A ∧ (T : Subgroup G).subgroupOf F.H ≤ normalizer (A : Set F.H) ∧
        Nat.card (A.map (starMap F)) = 3 ∧
        A.map (starMap F) ≠ (center (pResidual 2 (HStar F.H))).map (pResidual 2 (HStar F.H)).subtype ∧
        ((starMap F).comp A.subtype).ker = pCore 2 A ∧ Nat.card (A ⧸ pCore 2 A) = 3) ∧
      (IsPPerfect 2 B ∧ (T : Subgroup G).subgroupOf F.H ≤ normalizer (B : Set F.H) ∧
        Nat.card (B.map (starMap F)) = 3 ∧
        B.map (starMap F) ≠ (center (pResidual 2 (HStar F.H))).map (pResidual 2 (HStar F.H)).subtype ∧
        ((starMap F).comp B.subtype).ker = pCore 2 B ∧ Nat.card (B ⧸ pCore 2 B) = 3) := by
  let : Finite W := Finite.of_surjective (fun b : B => (s.coordinates b).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨σ,hσ,hZ,hmP,_,_,_⟩ := extraspecial_point_central_chief_degree
    h hab structural previous hex hcard hexp hB hUN s hp hm
  let : σ.IsIrreducible := (irreducible_comp_surjective_iff (starMap F)
    (QuotientGroup.mk'_surjective _) σ).mp (hσ ▸ inferInstance)
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  have heP : Monoid.exponent P = 3 :=
    (Monoid.exponent_eq_of_mulEquiv (residualStarEquiv F)).symm.trans hexp
  have hN : Nat.card (σ.ker.subgroupOf P) = 9 := by
    rcases extraspecial_center_kernel_residual_card σ P hP rfl hZ hmP (Or.inl hd) with h2 | h4
    · exact h2.2.2
    · omega
  have hk : IsPGroup 2 (starMap F).ker := by
    change IsPGroup 2 (QuotientGroup.mk' (pCore 2 F.H)).ker
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  exact IsExtraspecial.exists_cubic_lifts_of_normal_nine (starMap F)
    (QuotientGroup.mk'_surjective _) hk hP heP σ.ker hN
    (fun z hz => hZ (mem_map_of_mem P.subtype hz))
    ((T : Subgroup G).subgroupOf F.H) T.isPGroup'.comap_subtype

/-- At least one cubic lift escapes the original normalizer of L, while
normalizing the point residual and retaining the literal star-map kernel. -/
theorem extraspecial_two_chief_escaping_cubic
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    {B N : Subgroup G} (hB : B ≤ centralizer (F.U : Set G)) (hUN : F.U ≤ N)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W} [ρ.IsIrreducible]
    (s : BinaryConjugationSection F.H B N ρ)
    (hp : ⁅B,F.Li L 1⁆ ≤ N) (hm : ¬ ⁅B,K F⁆ ≤ N)
    (hd : Module.finrank (ZMod 2) W = 2) :
    ∃ Y : Subgroup G, ∃ hYH : Y ≤ F.H,
      Y ≤ K F ∧ IsPPerfect 2 Y ∧
      (T : Subgroup G) ≤ normalizer (Y : Set G) ∧
      Y ≤ normalizer (F.Li L 1 : Set G) ∧ ¬ Y ≤ normalizer (L : Set G) ∧
      Nat.card (star F Y) = 3 ∧
      star F Y ≠ (center (pResidual 2 (HStar F.H))).map (pResidual 2 (HStar F.H)).subtype ∧
      ((starMap F).comp (inclusion hYH)).ker = pCore 2 Y ∧
      Nat.card (Y ⧸ pCore 2 Y) = 3 := by
  obtain ⟨A,B,hAB,hA,hB⟩ := extraspecial_two_chief_cubic_lifts
    h hab structural previous hex hcard hexp hB hUN s hp hm hd
  have hgen : A.map F.H.subtype ⊔ B.map F.H.subtype = K F := by
    rw [←Subgroup.map_sup,hAB]
    rfl
  have he : ¬ A.map F.H.subtype ≤ normalizer (L : Set G) ∨
      ¬ B.map F.H.subtype ≤ normalizer (L : Set G) := by
    by_contra! hn
    apply h.flag_escape_at F previous
    rw [residual_product F,←hgen]
    exact sup_le (sup_le hn.1 hn.2) (h.sylow_normalizes_at structural)
  obtain ⟨A,hAK,hperfect,hAT,hcardA,hAZ,hker,hquot,hesc⟩ :
      ∃ A : Subgroup F.H, A ≤ pResidual 2 F.H ∧ IsPPerfect 2 A ∧
        (T : Subgroup G).subgroupOf F.H ≤ normalizer (A : Set F.H) ∧
        Nat.card (A.map (starMap F)) = 3 ∧
        A.map (starMap F) ≠ (center (pResidual 2 (HStar F.H))).map (pResidual 2 (HStar F.H)).subtype ∧
        ((starMap F).comp A.subtype).ker = pCore 2 A ∧ Nat.card (A ⧸ pCore 2 A) = 3 ∧
        ¬ A.map F.H.subtype ≤ normalizer (L : Set G) := by
    rcases he with he | he
    · exact ⟨A,le_sup_left.trans_eq hAB,hA.1,hA.2.1,hA.2.2.1,hA.2.2.2.1,
        hA.2.2.2.2.1,hA.2.2.2.2.2,he⟩
    · exact ⟨B,le_sup_right.trans_eq hAB,hB.1,hB.2.1,hB.2.2.1,hB.2.2.2.1,
        hB.2.2.2.2.1,hB.2.2.2.2.2,he⟩
  let Y := A.map F.H.subtype
  have hYH : Y ≤ F.H := map_subtype_le A
  let e : A ≃* Y := equivMapOfInjective A F.H.subtype F.H.subtype_injective
  have hstar : star F Y = A.map (starMap F) := by
    change ((A.map F.H.subtype).comap F.H.subtype).map (starMap F) = _
    rw [comap_map_eq_self_of_injective F.H.subtype_injective]
  have hnorm : (T : Subgroup G) ≤ normalizer (Y : Set G) := by
    rw [←map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ F.H from F.invariant 1)]
    exact (map_mono hAT).trans (le_normalizer_map F.H.subtype)
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have hHL : F.H ≤ normalizer (F.Li L 1 : Set G) :=
    (normal_subgroupOf_iff_le_normalizer ((F.Li_le L 1).trans inf_le_right)).mp hn
  let f := (starMap F).comp (inclusion hYH)
  have hke : f.ker.comap e.toMonoidHom = pCore 2 A := hker
  have hkerY : f.ker = pCore 2 Y := by
    calc
      f.ker = (f.ker.comap e.toMonoidHom).map e.toMonoidHom :=
        (map_comap_eq_self_of_surjective e.surjective _).symm
      _ = (pCore 2 A).map e.toMonoidHom := congrArg (map e.toMonoidHom) hke
      _ = pCore 2 Y := pCore_map_iso 2 e
  refine ⟨Y,hYH,map_mono hAK,hperfect.of_surjective e.toMonoidHom e.surjective,
    hnorm,hYH.trans hHL,hesc,hstar.symm ▸ hcardA,hstar.symm ▸ hAZ,hkerY,?_⟩
  exact (Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv).symm.trans hquot

open NoncentralChiefRefinement in
/-- Construct the cubic escape directly from the literal original chief interval.
No representation or normalization premise is supplied by a caller. -/
theorem extraspecial_four_interval_escaping_cubic
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (N B : NormalNode F.H) (hNB : N ⋖ B)
    (hUN : F.U ≤ N.val.map F.H.subtype)
    (hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G))
    (hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U)
    (hm : ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype)
    (hc : Nat.card (Section N B) = 4) :
    ∃ Y : Subgroup G, ∃ hYH : Y ≤ F.H,
      Y ≤ K F ∧ IsPPerfect 2 Y ∧
      (T : Subgroup G) ≤ normalizer (Y : Set G) ∧
      Y ≤ normalizer (F.Li L 1 : Set G) ∧ ¬ Y ≤ normalizer (L : Set G) ∧
      Nat.card (star F Y) = 3 ∧
      star F Y ≠ (center (pResidual 2 (HStar F.H))).map (pResidual 2 (HStar F.H)).subtype ∧
      ((starMap F).comp (inclusion hYH)).ker = pCore 2 Y ∧
      Nat.card (Y ⧸ pCore 2 Y) = 3 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨τ,⟨sU⟩⟩ := exists_section F
  let Q := (centralizer (F.U : Set G)).subgroupOf F.H
  have hQ : IsPGroup 2 Q :=
    ((isPGroup_pCoreIn 2 F.H).to_le
      (centralizer_U_le_core_of_escape h structural (h.flag_escape_at F previous) sU)).comap_subtype
  have hBQ : B.val ≤ Q := fun b hb => hBC (mem_map_of_mem F.H.subtype hb)
  let : IsElementaryAbelian 2 (Section N B) := chief_elementary N B hNB (hQ.to_le hBQ)
  let ρ := binarySectionRepresentation N B
  let : ρ.IsIrreducible := binarySection_irreducible N B hNB
  let s := ambientBinarySection F.H N B hNB.le
  have hd : Module.finrank (ZMod 2) (Additive (Section N B)) = 2 := by
    have he : Nat.card (Additive (Section N B)) = 4 := hc
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at he
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) he
  exact extraspecial_two_chief_escaping_cubic h hab structural previous hex hcard hexp hBC hUN s
    ((commutator_mono hBC le_rfl).trans (hp.trans hUN)) hm hd

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The actual symmetric-three quotient of an escaping cubic overgroup

The selected reciprocal critical involution fixes exactly the center
of the extraspecial star residual. It therefore cannot centralize a
noncentral cubic star subgroup. The exact kernel of the restricted
star map lifts this movement to [Y,T] not contained in O₂(Y).
The three-coset action then constructs YT/O₂(YT) ≃ S₃.

Applying this to the literal order-four chief interval retains the
original escaping subgroup Y, its T-invariance, its normalization of L₁,
and its exact star kernel. Thus the S₃ quotient premise of source
14.5.3(2) is now discharged for that subgroup. The geometric containment
implication of 14.5.3(2) remains unproved here, so the interval is not yet
excluded and this is not the residual classification through 14.7.52.

Source: Aschbacher–Smith, 14.5.3(2), printed p.1013, the reducible Sylow
step in 14.7.9 and 14.7.15(2), pp.1045,1047, and 14.7.20(2), p.1049.
-/

public noncomputable section
open scoped commutatorElement
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The selected critical involution moves every normalized noncentral cubic
star subgroup, giving S₃ modulo the intrinsic two-core of its Sylow overgroup. -/
theorem extraspecial_cubic_sylow_quotient
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYK : Y ≤ K F)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hc : Nat.card (star F Y) = 3)
    (hZ : star F Y ≠ (center (pResidual 2 (HStar F.H))).map (pResidual 2 (HStar F.H)).subtype)
    (hker : ((starMap F).comp (inclusion hYH)).ker = pCore 2 Y)
    (hq : Nat.card (Y ⧸ pCore 2 Y) = 3) :
    Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) := by
  apply cubic_sylow_join_symmetricThree T Y hYT hq
  intro hm
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨c,hs,hcR,_,_⟩ := exists_selected_critical_geometry_of_point_normal h hab structural previous hn
  obtain ⟨a,ha,_,ht,hne,hcenter⟩ :=
    exists_extraspecial_critical_actor h hab structural previous hex hcard hexp c hs
  have hRT : F.Ri L 1 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow _ (T.subtype le_sup_right)).trans_eq (map_subgroupOf_eq_of_le le_sup_right)
  have haT : (a : G) ∈ (T : Subgroup G) := hRT (hcR ha)
  let α : MulAut P := MulAut.conjNormal (starMap F a)
  have hinv : Function.Involutive α := by
    intro x
    have he : α ^ 2 = 1 := by
      change (MulAut.conjNormal (starMap F a) : MulAut P) ^ 2 = 1
      rw [←map_pow,ht,map_one]
    exact congrArg (fun f : MulAut P => f x) (by simpa only [pow_two] using he)
  have hfix := MulAut.fixed_eq_center_of_extraspecial27_involution hP α hinv hne hcenter
  have hYP : star F Y ≤ P := by
    have hh := map_mono (f := starMap F) (subgroupOf_mono F.H hYK)
    rw [residual_subgroupOf,map_pResidual_of_surjective 2 (starMap F)
      (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  have hle : star F Y ≤ (center P).map P.subtype := by
    intro x hx
    have hxp : x ∈ P := hYP hx
    apply mem_map_of_mem P.subtype (x := (⟨x,hxp⟩ : P))
    rw [←hfix]
    apply (MulAut.mem_fixedSubgroup α _).mpr
    apply Subtype.ext
    change starMap F a * x * (starMap F a)⁻¹ = x
    obtain ⟨y,hy,rfl⟩ := hx
    have hcom : starMap F ⁅y,a⁆ = 1 := by
      have hcY : (⁅y,a⁆ : F.H).val ∈ Y.pCoreIn 2 :=
        hm (commutator_mem_commutator hy haT)
      obtain ⟨k,hk,hval⟩ := hcY
      have hk' : ((starMap F).comp (inclusion hYH)) k = 1 := hker.ge hk
      have he : inclusion hYH k = ⁅y,a⁆ := Subtype.ext hval
      change starMap F (inclusion hYH k) = 1 at hk'
      rwa [he] at hk'
    rw [map_commutatorElement] at hcom
    have hcomm := commutatorElement_eq_one_iff_mul_comm.mp hcom
    rw [←hcomm,mul_inv_cancel_right]
  apply hZ
  apply eq_of_le_of_card_ge hle
  rw [card_map_of_injective P.subtype_injective,IsExtraspecial.center_order_p 3 P,hc]
open NoncentralChiefRefinement in
/-- The original order-four chief interval supplies an escaping cubic whose
Sylow overgroup has its own two-core quotient isomorphic to S₃. -/
theorem extraspecial_four_interval_escaping_symmetricThree
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (N B : NormalNode F.H) (hNB : N ⋖ B)
    (hUN : F.U ≤ N.val.map F.H.subtype)
    (hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G))
    (hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U)
    (hm : ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype)
    (hc : Nat.card (Section N B) = 4) :
    ∃ Y : Subgroup G, ∃ hYH : Y ≤ F.H,
      Y ≤ K F ∧ IsPPerfect 2 Y ∧
      (T : Subgroup G) ≤ normalizer (Y : Set G) ∧
      Y ≤ normalizer (F.Li L 1 : Set G) ∧ ¬ Y ≤ normalizer (L : Set G) ∧
      Nat.card (star F Y) = 3 ∧
      star F Y ≠ (center (pResidual 2 (HStar F.H))).map (pResidual 2 (HStar F.H)).subtype ∧
      ((starMap F).comp (inclusion hYH)).ker = pCore 2 Y ∧
      Nat.card (Y ⧸ pCore 2 Y) = 3 ∧
      Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨Y,hYH,hYK,hYperfect,hYT,hYL,hout,hcY,hZ,hker,hquot⟩ :=
    extraspecial_four_interval_escaping_cubic h hab structural previous hex hcard hexp
      N B hNB hUN hBC hp hm hc
  exact ⟨Y,hYH,hYK,hYperfect,hYT,hYL,hout,hcY,hZ,hker,hquot,
    extraspecial_cubic_sylow_quotient h hab structural previous hex hcard hexp
      Y hYH hYK hYT hcY hZ hker hquot⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The original plane vertex in the cubic amalgam

The literal plane action identifies P = L₂T and P/O₂(P) with S₃.
Fixing the point as well as the plane gives exactly the original Sylow T.
Thus P and any cubic Sylow overgroup inside G₁ form a Goldschmidt triple
in their generated subgroup. The L₂-orbit of V₁ spans precisely V₂.

In the normal-point branch, an escaping Y cannot normalize L₂C_D(W),
where D = ⟨P,YT⟩ and W = ⟨V₁^D⟩: that would make Y preserve V₂ and
hence normalize L. The later module transports this to D/C_D(W).

Source: Aschbacher–Smith, 14.5.3--6, printed pp.1013--1014;
normal-point geometry in 14.7.15, printed p.1047, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

omit [Finite G] in
private theorem CubicGeometry_cubic_P_eq : F.P L = (L ⊔ (T : Subgroup G)) ⊓ F.Gi 2 := by
  ext x
  simp only [InvariantFlag.P, mem_inf, mem_iInf]
  constructor
  · exact fun hx => ⟨hx.1,hx.2 2 ⟨le_rfl,by decide⟩⟩
  · rintro ⟨hx,h2⟩
    refine ⟨hx,fun i hi => ?_⟩
    have : i = 2 := by omega
    subst i
    exact h2

/-- The plane parabolic retains the original two-residual L₂. -/
theorem plane_parabolic_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    (pResidual 2 (F.P L)).map (F.P L).subtype = F.Li L 2 := by
  have hLT : (pResidual 2 (L ⊔ (T : Subgroup G) : Subgroup G)).map
      (L ⊔ (T : Subgroup G)).subtype = L :=
    embedded_pResidual_join_pGroup L _ ((pResidual_eq_top_iff 2 L).mp h.residual)
      T.isPGroup' (h.sylow_normalizes_at structural)
  have hN : L ⊓ F.Gi 2 ≤ F.P L := by
    rw [CubicGeometry_cubic_P_eq]
    exact inf_le_inf_right _ le_sup_left
  have hR : (pResidual 2 (F.P L)).map (F.P L).subtype ≤ L ⊓ F.Gi 2 :=
    le_inf ((embedded_pResidual_mono 2 (show F.P L ≤ L ⊔ (T : Subgroup G) from inf_le_left)).trans_eq hLT)
      ((map_subtype_le _).trans (F.P_le_G₂ (by decide) L h.chosen.normalizes))
  have he := embedded_pResidual_eq_of_le_of_residual_le 2 hN hR
  simpa [InvariantFlag.Li] using he.symm

/-- The flag-defined parabolic is precisely L₂T, with the original Sylow. -/
theorem plane_parabolic_eq_join
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    F.P L = F.Li L 2 ⊔ (T : Subgroup G) := by
  have he := congrArg (map (F.P L).subtype)
    (pResidual_sup_sylow_eq_top (T.subtype (F.binary_sylow_le_P L)))
  rw [Subgroup.map_sup,plane_parabolic_residual h structural,
    Sylow.coe_subtype,map_subgroupOf_eq_of_le (F.binary_sylow_le_P L),
    ←MonoidHom.range_eq_map,range_subtype] at he
  exact he.symm

/-- Conjugation on the literal plane identifies the full two-core quotient. -/
def planeParabolicQuotientEquiv
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    (F.P L ⧸ pCore 2 (F.P L)) ≃* Equiv.Perm (Fin 3) := by
  let := h.chosen.elementary
  let f := F.binaryPermutationAction (by decide) L h.chosen.normalizes
  have hf : Function.Surjective f :=
    F.binaryPermutationAction_surjective (by decide) L h.chosen.normalizes (h.full_LT_action_at structural)
  have hk : f.ker = pCore 2 (F.P L) :=
    (F.binaryPermutationAction_ker (by decide) L h.chosen.normalizes).trans
      (F.binaryPlaneAction_ker_eq_twoCore (by decide) L h.chosen.normalizes
        (h.full_LT_action_at structural) (h.centralizer_LT_at structural))
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

/-- Fixing the point as well as the remaining flag cuts gives exactly T. -/
theorem plane_parabolic_inf_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    F.P L ⊓ F.H = (T : Subgroup G) := by
  let := h.chosen.elementary
  let A := F.P L ⊓ F.H
  let j := inclusion (show A ≤ L ⊔ (T : Subgroup G) from inf_le_left.trans inf_le_left)
  let f := (F.binarySeedAction L h.chosen.normalizes).comp j
  have hp : IsPGroup 2 (F.binaryFullFlag.comap f) :=
    (F.binaryFullFlag_isPGroup.comap_of_ker_isPGroup
      (F.binarySeedAction L h.chosen.normalizes)
      (F.binarySeedAction_ker_isPGroup L h.chosen.normalizes (h.centralizer_LT_at structural))).comap_of_injective
        j (inclusion_injective _)
  have he : F.binaryFullFlag.comap f = ⊤ := by
    apply top_unique
    intro x _ i v
    have hxi : (x : G) ∈ F.Gi i := by
      by_cases hi : i < 3
      · by_cases hi0 : i = 0
        · subst i
          have hz : F.Vi 0 = ⊥ := card_eq_one.mp (by simpa using F.card 0 (by decide))
          change (x : G) ∈ normalizer (F.Vi 0 : Set G)
          rw [hz,normalizer_eq_top]
          trivial
        · by_cases hi1 : i = 1
          · subst i
            exact x.property.2
          · have hi2 : i = 2 := by omega
            subst i
            exact (F.P_le_G₂ (by decide) L h.chosen.normalizes) x.property.1
      · have hv : F.Vi i = V := le_antisymm (F.le_seed i)
          (F.last.ge.trans (F.monotone (by omega)))
        change (x : G) ∈ normalizer (F.Vi i : Set G)
        rw [hv]
        exact F.P_le_seed_normalizer L h.chosen.normalizes x.property.1
    exact (mem_normalizer_iff.mp hxi (v : G)).symm
  have hA : IsPGroup 2 A := (he ▸ hp).of_equiv Subgroup.topEquiv
  exact T.is_maximal' hA (le_inf (F.binary_sylow_le_P L) (F.invariant 1))

/-- The second plane vertex and any S₃ overgroup inside G₁ form the
literal source Goldschmidt triple in their generated subgroup. -/
theorem cubic_goldschmidt_triple
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    ChapterF.IsGoldschmidtTriple ((F.P L).subgroupOf D)
      ((Y ⊔ (T : Subgroup G)).subgroupOf D) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  have hP : F.P L ≤ D := le_sup_left
  have hY : Y ⊔ (T : Subgroup G) ≤ D := le_sup_right
  have hinter : F.P L ⊓ (Y ⊔ (T : Subgroup G)) = (T : Subgroup G) :=
    le_antisymm ((inf_le_inf_left _ (sup_le hYH (F.invariant 1))).trans_eq
      (plane_parabolic_inf_point h structural))
      (le_inf (F.binary_sylow_le_P L) le_sup_right)
  let eP := subgroupOfEquivOfLe hP
  let eY := subgroupOfEquivOfLe hY
  refine ⟨?_,⟨(QuotientGroup.congr _ _ eP (pCore_map_iso 2 eP)).trans
    (planeParabolicQuotientEquiv h structural)⟩,
    ⟨(QuotientGroup.congr _ _ eY (pCore_map_iso 2 eY)).trans he.some⟩,
    T.subtype ((F.binary_sylow_le_P L).trans hP),?_⟩
  · rw [←subgroupOf_sup hP hY,subgroupOf_self]
  · exact congrArg (fun A : Subgroup G => A.subgroupOf D) hinter

/-- The original plane is generated by the L₂-conjugates of the original point. -/
theorem plane_eq_point_residual_span
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    conjugateSpanBy (F.Vi 1) (F.Li L 2) = F.Vi 2 := by
  let C := conjugateSpanBy (F.Vi 1) (F.Li L 2)
  have hC : C ≤ F.Vi 2 := conjugateSpanBy_le (F.monotone (by decide : 1 ≤ 2))
    ((F.Li_le L 2).trans inf_le_right)
  have h2 : 2 ≤ Nat.card C := by
    have hc := card_le_of_le (le_conjugateSpanBy (F.Vi 1) (F.Li L 2))
    simpa only [F.card 1 (by decide),pow_one] using hc
  have h4 : Nat.card C ≤ 4 := by
    simpa only [F.card 2 (by decide), show (2 : ℕ) ^ 2 = 4 from rfl] using card_le_of_le hC
  have hd : Nat.card C ∣ 4 := by simpa only [F.card 2 (by decide), show (2 : ℕ) ^ 2 = 4 from rfl] using card_dvd_of_le hC
  have h3 : Nat.card C ≠ 3 := by intro he; norm_num [he] at hd
  have hc : Nat.card C = 2 ∨ Nat.card C = 4 := by omega
  rcases hc with hc | hc
  · have he : F.Vi 1 = C := eq_of_le_of_card_ge (le_conjugateSpanBy _ _) (by rw [hc,F.card 1 (by decide)]; rfl)
    have hLH : F.Li L 2 ≤ F.H := by
      change F.Li L 2 ≤ normalizer (F.Vi 1 : Set G)
      rw [he]
      exact le_normalizer_conjugateSpanBy _ _
    have hPH : F.P L ≤ F.H := by
      rw [plane_parabolic_eq_join h structural]
      exact sup_le hLH (F.invariant 1)
    have hPT : F.P L = (T : Subgroup G) := by
      rw [←plane_parabolic_inf_point h structural,inf_eq_left.mpr hPH]
    have hi := SymmetricThreeTwoCore.sylow_index_three
      (planeParabolicQuotientEquiv h structural) (T.subtype (F.binary_sylow_le_P L))
    change (T : Subgroup G).relIndex (F.P L) = 3 at hi
    rw [hPT,relIndex_self] at hi
    omega
  · exact eq_of_le_of_card_ge hC (by change Nat.card (F.Vi 2) ≤ Nat.card C; rw [hc,F.card 2 (by decide)]; rfl)

/-- Preserving the original point residual and plane preserves their natural seed. -/
theorem point_plane_normalizer_le
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (A : Subgroup G) (hn : A ≤ normalizer (F.Li L 1 : Set G))
    (hc : A ≤ normalizer (F.Vi 2 : Set G)) :
    A ≤ normalizer (L : Set G) := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro D _ _ hD S N hN
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hD S hN
  apply le_trans _ (h.seed_normalizer_le_at structural)
  rw [←F.seed_eq_plane_span L (by decide) h.chosen.normalizes
    (F.invariant_subgroup_of_ambient_natural h.naturalMarking (by decide))]
  exact normalizes_conjugateSpanBy _ _ A hc hn


/-- In the normal-point branch an escaping actor cannot normalize L₂ even
modulo the centralizer of the point span in the newly generated group. -/
theorem cubic_plane_normalizer_obstruction_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hout : ¬ Y ≤ normalizer (L : Set G)) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    ¬ Y ≤ normalizer ((F.Li L 2 ⊔ (D ⊓ centralizer (W : Set G)) : Subgroup G) : Set G) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let C := D ⊓ centralizer (W : Set G)
  have hXD : F.Li L 2 ≤ D := by
    change F.Li L 2 ≤ F.P L ⊔ (Y ⊔ (T : Subgroup G))
    rw [plane_parabolic_eq_join h structural]
    exact le_sup_left.trans le_sup_left
  have hplane : F.Vi 2 ≤ W := by
    rw [←plane_eq_point_residual_span h structural]
    exact conjugateSpanBy_mono le_rfl hXD
  have hCplane : C ≤ normalizer (F.Vi 2 : Set G) :=
    (inf_le_right.trans (centralizer_le hplane)).trans (Subgroup.centralizer_le_normalizer _)
  have hspan : conjugateSpanBy (F.Vi 1) (F.Li L 2 ⊔ C) = F.Vi 2 := by
    apply le_antisymm
    · exact conjugateSpanBy_le (F.monotone (by decide : 1 ≤ 2))
        (sup_le ((F.Li_le L 2).trans inf_le_right) hCplane)
    · rw [←plane_eq_point_residual_span h structural]
      exact conjugateSpanBy_mono le_rfl le_sup_left
  change ¬ Y ≤ normalizer ((F.Li L 2 ⊔ C : Subgroup G) : Set G)
  intro hnorm
  apply hout
  apply point_plane_normalizer_le h structural Y hYL
  rw [←hspan]
  exact normalizes_conjugateSpanBy _ _ Y hYH hnorm

/-- The original full point-normality interface. -/
theorem cubic_plane_normalizer_obstruction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hout : ¬ Y ≤ normalizer (L : Set G)) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    ¬ Y ≤ normalizer ((F.Li L 2 ⊔ (D ⊓ centralizer (W : Set G)) : Subgroup G) : Set G) := by
  apply cubic_plane_normalizer_obstruction_of_normalizes_point h structural Y hYH _ hout
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# A nontrivial core for the original cubic completion

The original elementary span U is larger than the rank-three seed V,
is contained in T, and is normal in YT. If D = ⟨L₂,Y,T⟩ had trivial
two-core, the marked Goldschmidt classification and the rank of U would
select the Aut(M₁₂) amalgam. The centered vertex has no normal elementary
two-subgroup of rank four, contradicting the actual U inside YT.

Consequently D is a local subgroup of characteristic two. The original
point V₁ centralizes T, so its D-span W lies in Z(O₂(D)) and is elementary
abelian. All marked-amalgam inputs are supplied by their source proofs.

Source: Aschbacher–Smith, 14.5.5 and 14.5.7(3), printed pp.1013--1014,
and B.2.14, printed p.78, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Escape of G₁ forces its original elementary span to be larger than the seed. -/
private theorem CubicLocalStructure_span_card_gt_eight
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T) :
    8 < Nat.card F.U := by
  have hVU : V ≤ F.U := le_conjugateSpanBy _ _
  have hne : V ≠ F.U := by
    intro he
    apply h.flag_escape_at F previous
    have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
      intro X _ _ hX S M hM
      exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hM
    apply le_trans _ (h.seed_normalizer_le_at structural)
    have hh : F.H ≤ normalizer (F.U : Set G) := le_normalizer_conjugateSpanBy _ _
    exact hh.trans_eq (congrArg (fun A : Subgroup G => normalizer (A : Set G)) he).symm
  by_contra! hc
  apply hne
  apply eq_of_le_of_card_ge hVU
  simpa only [h.seed_card, show (2 : ℕ) ^ 3 = 8 from rfl] using hc

/-- Source 14.5.5 on the original generated group: a core-free marked
amalgam cannot contain the large normal elementary span at its centered vertex. -/
theorem cubic_generated_core_ne_bot
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    pCore 2 (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G) ≠ ⊥ := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let A := (F.P L).subgroupOf D
  let B := (Y ⊔ (T : Subgroup G)).subgroupOf D
  have ht := cubic_goldschmidt_triple h structural Y hYH he
  have hTD : (T : Subgroup G) ≤ D := le_sup_right.trans le_sup_right
  have hUT : F.U ≤ (T : Subgroup G) :=
    (IsElementaryAbelian.isPGroup 2 F.U).le_sylow_of_normalized T
      ((F.invariant 1).trans (le_normalizer_conjugateSpanBy V F.H))
  have hUD : F.U ≤ D := hUT.trans hTD
  have hYTH : Y ⊔ (T : Subgroup G) ≤ F.H := sup_le hYH (F.invariant 1)
  have hnorm : Y ⊔ (T : Subgroup G) ≤ normalizer (F.U : Set G) :=
    hYTH.trans (le_normalizer_conjugateSpanBy V F.H)
  let U₀ := F.U.subgroupOf D
  let : IsElementaryAbelian 2 U₀ := IsElementaryAbelian.subgroupOf hUD
  have hUB : U₀ ≤ B := fun x hx => (le_sup_right : (T : Subgroup G) ≤ Y ⊔ (T : Subgroup G)) (hUT hx)
  let E := U₀.subgroupOf B
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hUB
  let : E.Normal := normal_subgroupOf_of_le_normalizer
    ((show B ≤ (normalizer (F.U : Set G)).comap D.subtype from fun x hx => hnorm hx).trans
      (le_normalizer_comap D.subtype))
  let eU := (subgroupOfEquivOfLe hUB).trans (subgroupOfEquivOfLe hUD)
  have hcard : 8 < Nat.card E := by
    rw [Nat.card_congr eU.toEquiv]
    exact CubicLocalStructure_span_card_gt_eight h structural previous
  have hr : 4 ≤ primeRank 2 D := by
    by_contra! hr
    have hc := (primeRank_le_iff_elementary_card_le D).mp (show primeRank 2 D ≤ 3 by omega)
      U₀ inferInstance
    rw [Nat.card_congr (subgroupOfEquivOfLe hUD).toEquiv] at hc
    have hh := CubicLocalStructure_span_card_gt_eight (F := F) h structural previous
    norm_num at hc
    omega
  have hZ : center B ≠ ⊥ := by
    obtain ⟨z,hz,hpoint⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
    have hzP : z ∈ F.Vi 1 := hpoint ▸ mem_zpowers z
    have hzT : z ∈ (T : Subgroup G) := h.chosen.le_sylow (F.le_seed 1 hzP)
    let b : B := ⟨⟨z,hTD hzT⟩,(le_sup_right : (T : Subgroup G) ≤ Y ⊔ (T : Subgroup G)) hzT⟩
    have hb : b ∈ center B := by
      apply mem_center_iff.mpr
      intro a
      apply Subtype.ext
      apply Subtype.ext
      exact (mem_centralizer_iff.mp
        ((hYTH.trans (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))))
          a.property) z hzP).symm
    intro hzbot
    have heq := congrArg (fun a : B => (a.val : G)) (mem_bot.mp (hzbot ▸ hb))
    exact hz heq
  intro hcore
  have hc : ChapterF.SourceAssembly.CharacteristicTwoMarkedAmalgamInput.{u} :=
    ChapterF.SourceAssembly.characteristicTwoMarked_of_large_nonabelian
      ChapterF.SourceAssembly.Goldschmidt.largeNonabelianMarkedAmalgams
  obtain hm | hm := ht.aut_mathieu_marked_of_high_rank hc hcore hr
  all_goals
    have hrE : primeRank 2 E ≤ 3 := by
      first
      | exact ChapterF.SourceAssembly.Mathieu.outer_centered_parabolic_normal_elementary_primeRank_le_three
          hm B (Or.inr rfl) hZ E
      | exact ChapterF.SourceAssembly.Mathieu.outer_centered_parabolic_normal_elementary_primeRank_le_three
          hm B (Or.inl rfl) hZ E
    have hu : Nat.card E ≤ 2 ^ 3 := by
      rw [IsElementaryAbelian.card_eq_pow_primeRank (p := 2) E]
      exact Nat.pow_le_pow_right (by decide) hrE
    norm_num at hu
    omega

/-- The actual point span is elementary and lies in the center of the
nontrivial two-core of the source Goldschmidt completion. -/
theorem cubic_generated_local_structure
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    D ∈ Chapter1.He G ∧ IsSQTK KnownSimple.IsKnownSimple D ∧
      IsElementaryAbelian 2 W ∧ W ≤ D.pCoreIn 2 ∧
      W ≤ centralizer (D.pCoreIn 2 : Set G) := by
  let := h.chosen.elementary
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  have hTD : (T : Subgroup G) ≤ D := le_sup_right.trans le_sup_right
  have hZD : F.Vi 1 ≤ D := (F.le_seed 1).trans (h.chosen.le_sylow.trans hTD)
  have hWD : W ≤ D := conjugateSpanBy_le_self hZD
  have hn := cubic_generated_core_ne_bot h hab structural previous Y hYH he
  have hDH : D ∈ Chapter1.H G := by
    intro hz
    exact hn (((pCore 2 D).map_eq_bot_iff_of_injective D.subtype_injective).mp hz)
  have hHe : D ∈ Chapter1.He G := Chapter1.lemma_1_1_4_6 T
    (h.source.simpleQTKE.evenCharacteristic T) ⟨hDH,hTD⟩
  have hQT : D.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hq := pCoreIn_le_sylow D (T.subtype hTD)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTD] using hq
  have hZC : F.Vi 1 ≤ centralizer (T : Set G) :=
    le_centralizer_iff.mp ((F.invariant 1).trans
      (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))))
  have hQC : W ≤ centralizer (D.pCoreIn 2 : Set G) :=
    conjugateSpanBy_le (hZC.trans (centralizer_le hQT))
      ((D.le_normalizer.trans (normalizer_le_normalizer_characteristic_image D (pCore 2 D))).trans
        (normalizer_le_normalizer_centralizer _))
  have hWQ : W ≤ D.pCoreIn 2 := (le_inf hWD hQC).trans hHe
  let : IsElementaryAbelian 2 (F.Vi 1) := IsElementaryAbelian.of_le (F.le_seed 1)
  let : IsMulCommutative W := le_centralizer_iff_isMulCommutative.mp
    (hQC.trans (centralizer_le hWQ))
  exact ⟨hHe,Chapter3.sqtk_of_mem_H h.source.simpleQTKE hDH,
    conjugateSpanBy_elementary_of_commutative _ _,hWQ,hQC⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end
