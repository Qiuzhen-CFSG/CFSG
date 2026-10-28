module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ThreeCoreActions
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.LocalAction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Alternating.NaturalRecognition
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Source.LargePrimeExclusion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeExclusion
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Noncontained.Extraspecial.Rank
public import Theory.GroupTheory.PGroup.SelfCentralizingSupercritical
public import CFSG.Quasithin.ChapterA.Section01.RankActions.ThreeAutomorphisms
public import Theory.SpecificGroups.GL2.PrimeThreeFiveResidual.Coordinates
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ThreeCorePoint
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Noncontained.ElementaryNine.Offender
public import Theory.GroupTheory.CubicSmallAction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ThreeCoreLifts
public import Theory.GroupTheory.PGroup.SupercriticalCubic
public import Theory.GroupTheory.SmallFittingResidual
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ThreeCoreAmbient
public import Theory.GroupTheory.TwoPerfectNormalizerControl
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ThreeCoreMinimal
public import Theory.GroupTheory.CubicFixedLineOvergroup
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ThreeCoreIntersection
public import Theory.GroupTheory.PResidual.CentralThreeLift
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ThreeCoreContainment
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms
public import Theory.SpecificGroups.PSL3Two.Parabolics.ResidualCommutator
public import Theory.GroupTheory.PResidual.NormalizedImageContainment
public import Theory.SpecificGroups.PSL3Two.Parabolics.NormalAction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ThreeCoreCenter
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableGeometry
public import Theory.GroupTheory.ConjugateSpanNormalizer
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableCubicContainment
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicContainment
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LocalOvergroups
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableNineContainment
public import Theory.GroupTheory.PGroup.ElementaryNineCubicLifts
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableNineKernel
public import Theory.GroupTheory.PCoreNormalizerAction.Kernel
public import Theory.SpecificGroups.PSL3Two.Automorphisms
public import Theory.GroupTheory.PResidual.CubicKernelResidual
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableNinePoint
public import Theory.GroupTheory.PGroup.NormalNineFixedLine
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableNineEnlargement
public import Theory.GroupTheory.PGroup.NormalNineInvariantActor
public import Theory.GroupTheory.PGroup.SupercriticalNineCyclic
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Guarded three core lifts

This unit collects the indicated original source arguments at the same G,T.
Each constituent overview records its proof and source; the universal exports
remain unchanged. The larger unit avoids repeated loading of the common source
imports. Public mathematical statements and literal subgroup maps are retained.
-/

/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Three-core actions in the original solvable local family

For every original J in H_z, the proved large-prime exclusion and solvability
make O₃(J/O₂(J)) self-centralizing. The rank-two automorphism bound then
shows that J is a {2,3}-group.

A normal Heisenberg subgroup cannot be moved by O₂(L₁): the cubic-residual
inverter construction would give an elementary subgroup of order 27 in the
same quotient, contradicting the original local three-rank bound. For a
supercritical Heisenberg subgroup, automorphism detection therefore gives
the exact point-image kernel O₂(L₁). Its full Frattini-action kernel is the
entire O₃(J/O₂(J)), retaining the inner action.

For an elementary-nine supercritical subgroup, either the same point kernel
occurs or the actual L₁ action is SL₂(3). The latter action has precisely the
original star-map kernel. The source applications construct the same normal
lift as before, retain its full two-core kernel, and prove that the original
point image has order three or twenty-four. These action reductions do not
yet exclude the proper Heisenberg and elementary-nine local configurations.

Source: Aschbacher–Smith, A.1.25(3), printed p.25, and the noncyclic branches
of 14.7.27, printed pp.1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem ThreeCoreActions_local_three_rank
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G))) :
    primeRank 3 (HStar J) ≤ 2 := by
  have hpoint : F.Vi 1 ≠ ⊥ := by
    intro he
    have hc := F.card 1 (by decide)
    rw [he,card_bot] at hc
    norm_num at hc
  have hH : IsTwoLocal F.H := ⟨F.Vi 1,hpoint,
    IsPGroup.of_card (p := 2) (n := 1) (F.card 1 (by decide)),rfl⟩
  exact (primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 J) pCore_isPGroup).trans
    ((Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion hJ.2.1) (inclusion_injective hJ.2.1)).trans
      ((h.source.simpleQTKE.twoLocal_sqtk hH).stronglyQuasithin 3 (by decide) (by decide)))

private theorem ThreeCoreActions_point_perfect : IsPPerfect 2 (F.Li L 1) := by
  simp only [InvariantFlag.Li]
  exact isPPerfect_embedded_pResidual 2 _

/-- The two-core of the original L₁ centralizes every actual normal Heisenberg subgroup of J/O₂(J). -/
theorem local_normal_heisenberg_pointResidual_core_action_eq_bot
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (Z : Subgroup (HStar J)) [Z.Normal] (e : Z ≃* HeisenbergPrime 3) :
    (pCore 2 (F.Li L 1)).map
      ((MulAut.conjNormal : HStar J →* MulAut Z).comp
        ((QuotientGroup.mk' (pCore 2 J)).comp
          (inclusion (F.Li_one_le_of_mem_Hz hJ)))) = ⊥ := by
  let : IsExtraspecial 3 Z := IsExtraspecial.of_mulEquiv e.symm
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2))
  have hc : Nat.card Z = 27 := by rw [Nat.card_congr e.toEquiv,HeisenbergPrime.card]; decide
  have hexp (x : Z) : x ^ 3 = 1 := by
    apply e.injective
    rw [map_pow,HeisenbergPrime.pow_prime (by decide : 3 ≠ 2),map_one]
  by_contra hne
  obtain ⟨A,_,hA,hcard⟩ :=
    Chapter13.Section08.SolvableExclusion.Three.Extraspecial.elementary_of_cubic_residual
      Z ⊤ hc hexp le_top ThreeCoreActions_point_perfect
      (pointResidual_core_quotient_card h structural)
      ((QuotientGroup.mk' (pCore 2 J)).comp (inclusion (F.Li_one_le_of_mem_Hz hJ)))
      (fun _ => mem_top _) hne
  have hb := (primeRank_le_iff_elementary_card_le (HStar J)).mp
    (ThreeCoreActions_local_three_rank h J hJ) A hA
  rw [hcard] at hb
  norm_num at hb

/-- The actual three-core is self-centralizing in each solvable local quotient. -/
theorem local_solvable_threeCore_selfCentralizing
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    centralizer (pCore 3 (HStar J) : Set (HStar J)) ≤ pCore 3 (HStar J) := by
  let := hs
  rw [←local_fitting_eq_threeCore h hab structural previous faithful J hJ]
  exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable inferInstance

/-- Every prime divisor of the whole original solvable J is two or three. -/
theorem local_solvable_prime_divisors
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) (p : ℕ) (hp : p.Prime) (hd : p ∣ Nat.card J) :
    p = 2 ∨ p = 3 := by
  by_contra hn
  have hp2 : p ≠ 2 := fun he => hn (Or.inl he)
  have hp3 : p ≠ 3 := fun he => hn (Or.inr he)
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' p hd
  let P := pCore 3 (HStar J)
  let q := QuotientGroup.mk' (pCore 2 J)
  let a := (MulAut.conjNormal : HStar J →* MulAut P).comp q
  have hr : primeRank 3 P ≤ 2 := (primeRank_subgroup_le 3 P).trans (ThreeCoreActions_local_three_rank h J hJ)
  have ha : a x = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes
      (hp.coprime_iff_not_dvd.mpr (fun hd => hn (ChapterA.lemma_A_1_25_3 pCore_isPGroup hr hp hd)))
    · exact hx ▸ orderOf_map_dvd a x
    · exact orderOf_dvd_natCard _
  have hq : orderOf (q x) = p :=
    (q.orderOf_map_eq_of_coprime_of_isPGroup_ker
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) x
      (by rw [hx]; exact (Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm)).trans hx
  have hcent : q x ∈ centralizer (P : Set (HStar J)) := by
    rw [←MulAut.conjNormal_ker_eq_centralizer]
    exact ha
  have hmem : q x ∈ P :=
    local_solvable_threeCore_selfCentralizing h hab structural previous faithful J hJ hs hcent
  have hdiv : p ∣ Nat.card P := by
    have hh := orderOf_dvd_natCard (⟨q x,hmem⟩ : P)
    have hy : orderOf (⟨q x,hmem⟩ : P) = p := (Subgroup.orderOf_coe _).symm.trans hq
    exact hy ▸ hh
  obtain ⟨n,hcard⟩ := (pCore_isPGroup (p := 3) (G := HStar J)).exists_card_eq
  have hd3 : p ∣ 3 := hp.dvd_of_dvd_pow (hcard ▸ hdiv)
  exact hp3 ((Nat.dvd_prime Nat.prime_three).mp hd3 |>.resolve_left hp.ne_one)

/-- Trivial O₂(L₁)-action on the selected supercritical subgroup determines the full original point kernel. -/
theorem local_solvable_supercritical_point_kernel_of_trivial_action
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (X : Subgroup (pCore 3 (HStar J))) (hX : IsSupercriticalPSubgroup 3 X)
    (hact : letI : X.Characteristic := hX.characteristic
      (pCore 2 (F.Li L 1)).map
      ((MulAut.conjNormal : HStar J →* MulAut (X.map (pCore 3 (HStar J)).subtype)).comp
        ((QuotientGroup.mk' (pCore 2 J)).comp
          (inclusion (F.Li_one_le_of_mem_Hz hJ)))) = ⊥) :
    ((QuotientGroup.mk' (pCore 2 J)).comp
      (inclusion (F.Li_one_le_of_mem_Hz hJ))).ker = pCore 2 (F.Li L 1) ∧
    Nat.card (((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) = 3 := by
  let P := pCore 3 (HStar J)
  let : X.Characteristic := hX.characteristic
  let Z := X.map P.subtype
  let : Z.Characteristic := inferInstance
  let q := (QuotientGroup.mk' (pCore 2 J)).comp (inclusion (F.Li_one_le_of_mem_Hz hJ))
  have hcent : (pCore 2 (F.Li L 1)).map q ≤ centralizer (Z : Set (HStar J)) := by
    rw [←MulAut.conjNormal_ker_eq_centralizer]
    rw [map_le_iff_le_comap,MonoidHom.comap_ker]
    exact (Subgroup.map_eq_bot_iff _).mp hact
  have hC := hX.ambient_centralizer_le_pCore P pCore_isPGroup
    (local_solvable_threeCore_selfCentralizing h hab structural previous faithful J hJ hs) X
    (by decide : Odd 3)
  have hbot : (pCore 2 (F.Li L 1)).map q = ⊥ := by
    have hd := (pCore_isPGroup.map q).disjoint_of_coprime
      (pCore_isPGroup (p := 3) (G := HStar J)) (by decide : Nat.Coprime 2 3)
    exact bot_unique ((le_inf le_rfl (hcent.trans hC)).trans hd.le_bot)
  have hkle : q.ker ≤ pCore 2 (F.Li L 1) := by
    apply le_sSup
    refine ⟨inferInstance,?_⟩
    exact (show IsPGroup 2 (QuotientGroup.mk' (pCore 2 J)).ker by
      rw [QuotientGroup.ker_mk']; exact pCore_isPGroup).comap_of_injective
        (inclusion (F.Li_one_le_of_mem_Hz hJ)) (inclusion_injective _)
  have hk : q.ker = pCore 2 (F.Li L 1) :=
    le_antisymm hkle ((Subgroup.map_eq_bot_iff _).mp hbot)
  refine ⟨hk,?_⟩
  have hr : q.range = ((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) := by
    rw [MonoidHom.range_comp,inclusion_range]
  rw [←hr,←Nat.card_congr (QuotientGroup.quotientKerEquivRange q).toEquiv,hk]
  exact pointResidual_core_quotient_card h structural

/-- The Heisenberg branch has point-image order three and exactly O₂(L₁) as its star-map kernel. -/
theorem local_solvable_heisenberg_point_kernel
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (X : Subgroup (pCore 3 (HStar J))) (hX : IsSupercriticalPSubgroup 3 X)
    (e : X ≃* HeisenbergPrime 3) :
    ((QuotientGroup.mk' (pCore 2 J)).comp
      (inclusion (F.Li_one_le_of_mem_Hz hJ))).ker = pCore 2 (F.Li L 1) ∧
    Nat.card (((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) = 3 := by
  let : X.Characteristic := hX.characteristic
  let eX := equivMapOfInjective X (pCore 3 (HStar J)).subtype
    (pCore 3 (HStar J)).subtype_injective
  apply local_solvable_supercritical_point_kernel_of_trivial_action
    h hab structural previous faithful J hJ hs X hX
  exact local_normal_heisenberg_pointResidual_core_action_eq_bot h structural J hJ _
    (eX.symm.trans e)

/-- The full action on the actual Heisenberg Frattini quotient has exactly the three-core as kernel. -/
theorem local_solvable_heisenberg_frattini_kernel
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (X : Subgroup (pCore 3 (HStar J))) (hX : IsSupercriticalPSubgroup 3 X)
    (e : X ≃* HeisenbergPrime 3) :
    letI : X.Characteristic := hX.characteristic
    (((quotientAut (frattini X)).comp (MulAut.characteristic X)).comp
      (MulAut.conjNormal : HStar J →* MulAut (pCore 3 (HStar J)))).ker =
        pCore 3 (HStar J) := by
  let : IsExtraspecial 3 X := IsExtraspecial.of_mulEquiv e.symm
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2))
  exact hX.ambient_frattini_kernel_eq_pCore (pCore 3 (HStar J)) pCore_isPGroup
    (local_solvable_threeCore_selfCentralizing h hab structural previous faithful J hJ hs)
    X (by decide : Odd 3) rfl (IsExtraspecial.frattini_eq_center (p := 3)).symm.le

private def ThreeCoreActions_liftModelEquiv
    (J : Subgroup G) (X : Subgroup (pCore 3 (HStar J))) (Y : Subgroup J)
    (hm : Y.map (QuotientGroup.mk' (pCore 2 J)) = X.map (pCore 3 (HStar J)).subtype)
    (hk : ((QuotientGroup.mk' (pCore 2 J)).comp Y.subtype).ker = pCore 2 Y) :
    (Y ⧸ pCore 2 Y) ≃* X := by
  let f := (QuotientGroup.mk' (pCore 2 J)).comp Y.subtype
  have hr : f.range = X.map (pCore 3 (HStar J)).subtype := by
    rw [MonoidHom.range_comp,range_subtype,hm]
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans
      ((MulEquiv.subgroupCongr hr).trans
        (equivMapOfInjective X (pCore 3 (HStar J)).subtype
          (pCore 3 (HStar J)).subtype_injective).symm))

/-- Apply the action-kernel deductions to the supercritical subgroup and normal lift constructed on the original local group. -/
theorem local_solvable_threeCore_source_actions
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ∃ (X : Subgroup (pCore 3 (HStar J))) (hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup J),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 J ∧
      Y.map (QuotientGroup.mk' (pCore 2 J)) = X.map (pCore 3 (HStar J)).subtype ∧
      ((QuotientGroup.mk' (pCore 2 J)).comp Y.subtype).ker = pCore 2 Y ∧
      (Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∨
        (Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3) ∧
          ((QuotientGroup.mk' (pCore 2 J)).comp
            (inclusion (F.Li_one_le_of_mem_Hz hJ))).ker = pCore 2 (F.Li L 1) ∧
          Nat.card (((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) = 3 ∧
          letI : X.Characteristic := hX.characteristic
          (((quotientAut (frattini X)).comp (MulAut.characteristic X)).comp
            (MulAut.conjNormal : HStar J →* MulAut (pCore 3 (HStar J)))).ker =
              pCore 3 (HStar J))) := by
  obtain ⟨X,hX,Y,hYn,hYp,hYle,hYm,hYk,he⟩ :=
    local_solvable_threeCore_source h hab structural previous faithful J hJ hs
  refine ⟨X,hX,Y,hYn,hYp,hYle,hYm,hYk,?_⟩
  rcases he with he | he
  · exact Or.inl he
  let e := (ThreeCoreActions_liftModelEquiv J X Y hYm hYk).symm.trans he.some
  have hp := local_solvable_heisenberg_point_kernel h hab structural previous faithful
    J hJ hs X hX e
  exact Or.inr ⟨he,hp.1,hp.2,
    local_solvable_heisenberg_frattini_kernel h hab structural previous faithful J hJ hs X hX e⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
end

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Matrix.GeneralLinearGroup PrimeThreeFiveResidual
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The elementary-nine branch gives a cubic point image or actual SL₂(3) coordinates, retaining the star-map kernel. -/
theorem local_solvable_nine_point_action
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (X : Subgroup (pCore 3 (HStar J))) (hX : IsSupercriticalPSubgroup 3 X)
    (e₀ : X ≃* (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) :
    letI : X.Characteristic := hX.characteristic
    let Z := X.map (pCore 3 (HStar J)).subtype
    let q := (QuotientGroup.mk' (pCore 2 J)).comp (inclusion (F.Li_one_le_of_mem_Hz hJ))
    let a := (MulAut.conjNormal : HStar J →* MulAut Z).comp q
    (q.ker = pCore 2 (F.Li L 1) ∧ Nat.card q.range = 3) ∨
      ∃ (c : Z ≃* Multiplicative (Fin 2 → ZMod 3))
        (e : MulAut Z ≃* GL (Fin 2) (ZMod 3)),
        (∀ α z, planeAction 3 (e α) (c z) = c (α z)) ∧
        (e.toMonoidHom.comp a).range = threeSpecialLinear ∧
        a.ker = q.ker ∧ Nat.card q.range = 24 := by
  let : X.Characteristic := hX.characteristic
  let Z := X.map (pCore 3 (HStar J)).subtype
  let : Z.Characteristic := inferInstance
  let q := (QuotientGroup.mk' (pCore 2 J)).comp (inclusion (F.Li_one_le_of_mem_Hz hJ))
  let a := (MulAut.conjNormal : HStar J →* MulAut Z).comp q
  by_cases hzero : (pCore 2 (F.Li L 1)).map a = ⊥
  · have hh := local_solvable_supercritical_point_kernel_of_trivial_action
      h hab structural previous faithful J hJ hs X hX hzero
    refine Or.inl ⟨hh.1,?_⟩
    rw [MonoidHom.range_comp,inclusion_range]
    exact hh.2
  let eX := equivMapOfInjective X (pCore 3 (HStar J)).subtype
    (pCore 3 (HStar J)).subtype_injective
  let eZ := eX.symm.trans e₀
  let : IsElementaryAbelian 3 Z := IsElementaryAbelian.of_injective eZ.toMonoidHom eZ.injective
  have hc : Nat.card Z = 3 ^ 2 := by
    rw [Nat.card_congr eZ.toEquiv,Nat.card_prod]
    norm_num [Nat.card_zmod]
  obtain ⟨c,e,he⟩ := exists_plane_coordinates hc
  have hp : IsPPerfect 2 (F.Li L 1) := by
    simp only [InvariantFlag.Li]
    exact isPPerfect_embedded_pResidual 2 _
  have hnonzero : (pCore 2 (F.Li L 1)).map (e.toMonoidHom.comp a) ≠ ⊥ := by
    intro hz
    apply hzero
    apply bot_unique
    rintro y ⟨x,hx,rfl⟩
    apply e.injective
    simpa only [map_one] using mem_bot.mp (hz ▸ mem_map_of_mem (e.toMonoidHom.comp a) hx)
  have hr := ternary_range_eq hp (e.toMonoidHom.comp a) hnonzero
  have hak : a.ker ≠ ⊤ := by
    intro heq
    exact hzero ((Subgroup.map_eq_bot_iff _).mpr (heq ▸ le_top))
  have hle : a.ker ≤ pCore 2 (F.Li L 1) :=
    normal_le_pCore_of_pPerfect_prime_quotient hp
      (by rw [pointResidual_core_quotient_card h structural]; decide) a.ker hak
  have hcent := hX.ambient_centralizer_le_pCore (pCore 3 (HStar J)) pCore_isPGroup
    (local_solvable_threeCore_selfCentralizing h hab structural previous faithful J hJ hs)
    X (by decide : Odd 3)
  have hk : a.ker = q.ker := by
    apply le_antisymm
    · intro x hx
      have hcx : q x ∈ centralizer (Z : Set (HStar J)) := by
        rw [←MulAut.conjNormal_ker_eq_centralizer]
        exact hx
      have hd := (pCore_isPGroup.map q).disjoint_of_coprime
        (pCore_isPGroup (p := 3) (G := HStar J)) (by decide : Nat.Coprime 2 3)
      exact hd.le_bot ⟨mem_map_of_mem q (hle hx),hcent hcx⟩
    · intro x hx
      change MulAut.conjNormal (q x) = 1
      rw [show q x = 1 from hx,map_one]
  have heker : (e.toMonoidHom.comp a).ker = q.ker := by
    ext x
    change e (a x) = 1 ↔ q x = 1
    rw [←e.map_one,e.injective.eq_iff]
    exact SetLike.ext_iff.mp hk x
  have hcard := ternary_range_card hp (e.toMonoidHom.comp a) hnonzero
  have hcards : Nat.card q.range = Nat.card (e.toMonoidHom.comp a).range := by
    rw [←Nat.card_congr (QuotientGroup.quotientKerEquivRange q).toEquiv,
      ←Nat.card_congr (QuotientGroup.quotientKerEquivRange (e.toMonoidHom.comp a)).toEquiv,
      heker]
  exact Or.inr ⟨c,e,he,hr,hk,hcards.trans hcard⟩

/-- The original solvable-local consumer supplies every model and action premise: its literal point image has order three or twenty-four. -/
theorem local_solvable_point_star_card_three_or_twenty_four
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    Nat.card (((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) = 3 ∨
      Nat.card (((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) = 24 := by
  obtain ⟨X,hX,Y,hYn,hYp,hYle,hYm,hYk,he⟩ :=
    local_solvable_threeCore_source h hab structural previous faithful J hJ hs
  let e := ThreeCoreActions_liftModelEquiv J X Y hYm hYk
  rcases he with he | he
  · have hh := local_solvable_nine_point_action h hab structural previous faithful J hJ hs
      X hX (e.symm.trans he.some)
    rcases hh with hh | ⟨c,e,he,hr,hk,hc⟩
    · exact Or.inl (by simpa only [MonoidHom.range_comp,inclusion_range] using hh.2)
    · exact Or.inr (by simpa only [MonoidHom.range_comp,inclusion_range] using hc)
  · exact Or.inl (local_solvable_heisenberg_point_kernel h hab structural previous faithful
      J hJ hs X hX (e.symm.trans he.some)).2

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
end



/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Cubic point images in the original solvable local groups

For a supercritical elementary-nine subgroup, an SL₂(3) conjugation image
would force every faithful elementary two-actor to have fixed codimension
greater than twice its rank. The original flag supplies an actor with the
opposite bound. Supercritical detection makes that actor faithful, using
the full three-core centralizer bound. Thus the order-24 point-image branch
is impossible: every original solvable J in H_z has |L₁*| = 3, with
exactly O₂(L₁) as the star-map kernel.

The same image obstruction makes the two-residual of J/O₂(J) equal its
three-core in the elementary-nine branch. In the Heisenberg branch,
the full Frattini-action kernel is O₃(J/O₂(J)). The Sylow-normalized
cubic has normal image in GL₂(3), so it too lies in the three-core.
The final theorem applies both arguments to the original selected lift,
placing L₁* inside O₃(J/O₂(J)) without a placement premise.

The proper supercritical lifts and the remaining ambient noncyclic
three-core exclusions are still required for 14.7.27–29. None of these
results asserts nonsolvability or the final residual classification.

Source: Aschbacher–Smith, 14.7.27, printed pp.1054–1055; D.2.17,
pp.186–188; the elementary-nine character bound in 13.8.13, p.951,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Matrix.GeneralLinearGroup PrimeThreeFiveResidual
open Chapter13.Section08.SolvableExclusion.Three.Noncontained.ElementaryNine
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The actual quadratic actor excludes a special-linear image on a supercritical nine-group. -/
theorem local_solvable_nine_no_special_image
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (X : Subgroup (pCore 3 (HStar J))) (hX : IsSupercriticalPSubgroup 3 X)
    (c : ConjugationCoordinates (X.map (pCore 3 (HStar J)).subtype)) :
    ¬ threeSpecialLinear ≤ c.action.range := by
  intro hSL
  obtain ⟨hU,a,hq,A,hAR,hA,hquad,hcod⟩ :=
    local_quadratic_actor_at h structural hab J hJ
  let := hU
  let B := A.map (QuotientGroup.mk' (pCore 2 J))
  let : IsElementaryAbelian 2 B := hA.2
  have hcent := hX.ambient_centralizer_le_pCore (pCore 3 (HStar J)) pCore_isPGroup
    (local_solvable_threeCore_selfCentralizing h hab structural previous faithful J hJ hs)
    X (by decide : Odd 3)
  have hd := (IsElementaryAbelian.isPGroup 2 B).disjoint_of_coprime
    (pCore_isPGroup (p := 3) (G := HStar J)) (by decide : Nat.Coprime 2 3)
  have hb : B ⊓ centralizer (X.map (pCore 3 (HStar J)).subtype : Set (HStar J)) = ⊥ :=
    bot_unique ((inf_le_inf_left B hcent).trans hd.le_bot)
  have hlt := strict_fixedCodim_of_special_image c a.representation a.faithful hSL B hA hb
  exact (not_lt_of_ge hcod) hlt

/-- The elementary-nine branch has exactly the original two-core kernel and cubic point image. -/
theorem local_solvable_nine_point_kernel
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (X : Subgroup (pCore 3 (HStar J))) (hX : IsSupercriticalPSubgroup 3 X)
    (e₀ : X ≃* (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) :
    ((QuotientGroup.mk' (pCore 2 J)).comp
      (inclusion (F.Li_one_le_of_mem_Hz hJ))).ker = pCore 2 (F.Li L 1) ∧
    Nat.card (((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) = 3 := by
  let : X.Characteristic := hX.characteristic
  let Z := X.map (pCore 3 (HStar J)).subtype
  let : Z.Characteristic := inferInstance
  let q := (QuotientGroup.mk' (pCore 2 J)).comp (inclusion (F.Li_one_le_of_mem_Hz hJ))
  rcases local_solvable_nine_point_action h hab structural previous faithful J hJ hs X hX e₀ with
    hh | ⟨c,e,he,hr,hk,hcard⟩
  · exact ⟨hh.1,by simpa only [MonoidHom.range_comp,inclusion_range] using hh.2⟩
  let coord : ConjugationCoordinates Z := {
    coordinate := c
    action := e.toMonoidHom.comp (MulAut.conjNormal : HStar J →* MulAut Z)
    conjugates := by
      intro k z
      have hh := he (MulAut.conjNormal k) z
      have hh' : Representation.AffineNine.naturalAction (e (MulAut.conjNormal k)) (c z) =
          c (MulAut.conjNormal k z) := hh
      change k * (z : HStar J) * k⁻¹ =
        (c.symm (Representation.AffineNine.naturalAction (e (MulAut.conjNormal k)) (c z)) : Z)
      rw [hh',c.symm_apply_apply]
      rfl }
  apply (local_solvable_nine_no_special_image h hab structural previous faithful J hJ hs X hX coord).elim
  rw [←hr]
  rintro y ⟨x,rfl⟩
  exact ⟨q x,rfl⟩


private def ThreeCorePoint_threeCoreLiftEquiv
    (J : Subgroup G) (X : Subgroup (pCore 3 (HStar J))) (Y : Subgroup J)
    (hm : Y.map (QuotientGroup.mk' (pCore 2 J)) = X.map (pCore 3 (HStar J)).subtype)
    (hk : ((QuotientGroup.mk' (pCore 2 J)).comp Y.subtype).ker = pCore 2 Y) :
    (Y ⧸ pCore 2 Y) ≃* X := by
  let f := (QuotientGroup.mk' (pCore 2 J)).comp Y.subtype
  have hr : f.range = X.map (pCore 3 (HStar J)).subtype := by
    rw [MonoidHom.range_comp,range_subtype,hm]
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans
      ((MulEquiv.subgroupCongr hr).trans
        (equivMapOfInjective X (pCore 3 (HStar J)).subtype
          (pCore 3 (HStar J)).subtype_injective).symm))

/-- Both original solvable three-core branches have the same full point kernel and cubic image. -/
theorem local_solvable_point_kernel
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ((QuotientGroup.mk' (pCore 2 J)).comp
      (inclusion (F.Li_one_le_of_mem_Hz hJ))).ker = pCore 2 (F.Li L 1) ∧
    Nat.card (((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) = 3 := by
  obtain ⟨X,hX,Y,hYn,hYp,hYle,hYm,hYk,he⟩ :=
    local_solvable_threeCore_source h hab structural previous faithful J hJ hs
  let e := ThreeCorePoint_threeCoreLiftEquiv J X Y hYm hYk
  rcases he with he | he
  · exact local_solvable_nine_point_kernel h hab structural previous faithful
      J hJ hs X hX (e.symm.trans he.some)
  · exact local_solvable_heisenberg_point_kernel h hab structural previous faithful
      J hJ hs X hX (e.symm.trans he.some)

/-- The original point residual’s two-core lies in the two-core of each solvable local overgroup. -/
theorem local_solvable_point_core_le
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    (F.Li L 1).pCoreIn 2 ≤ J.pCoreIn 2 := by
  have hk := (local_solvable_point_kernel h hab structural previous faithful J hJ hs).1
  rintro x ⟨y,hy,rfl⟩
  have hyk : ((QuotientGroup.mk' (pCore 2 J)).comp
      (inclusion (F.Li_one_le_of_mem_Hz hJ))) y = 1 := by
    change y ∈ ((QuotientGroup.mk' (pCore 2 J)).comp
      (inclusion (F.Li_one_le_of_mem_Hz hJ))).ker
    rwa [hk]
  exact mem_map_of_mem J.subtype ((QuotientGroup.eq_one_iff _).mp hyk)


/-- The entire two-residual is a three-group in the elementary-nine branch. -/
theorem local_solvable_nine_residual_isThreeGroup
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (X : Subgroup (pCore 3 (HStar J))) (hX : IsSupercriticalPSubgroup 3 X)
    (e₀ : X ≃* (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) :
    IsPGroup 3 (pResidual 2 (HStar J)) := by
  let : X.Characteristic := hX.characteristic
  let Z := X.map (pCore 3 (HStar J)).subtype
  let : Z.Characteristic := inferInstance
  let eX := equivMapOfInjective X (pCore 3 (HStar J)).subtype
    (pCore 3 (HStar J)).subtype_injective
  let eZ := eX.symm.trans e₀
  let : IsElementaryAbelian 3 Z := IsElementaryAbelian.of_injective eZ.toMonoidHom eZ.injective
  have hc : Nat.card Z = 3 ^ 2 := by
    rw [Nat.card_congr eZ.toEquiv,Nat.card_prod]
    norm_num [Nat.card_zmod]
  let c := conjugationCoordinates Z hc
  have hn := local_solvable_nine_no_special_image h hab structural previous faithful J hJ hs X hX c
  have hcent := hX.ambient_centralizer_le_pCore (pCore 3 (HStar J)) pCore_isPGroup
    (local_solvable_threeCore_selfCentralizing h hab structural previous faithful J hJ hs)
    X (by decide : Odd 3)
  have hk : IsPGroup 3 c.action.ker := by
    rw [c.ker_eq_centralizer]
    exact pCore_isPGroup.to_le hcent
  let R := (pResidual 2 (HStar J)).map c.action
  have hR : IsPGroup 3 R := by
    by_cases hz : R = ⊥
    · rw [hz]
      exact IsPGroup.of_card (n := 0) (by simp)
    have hp : IsPPerfect 2 R := (isPPerfect_pResidual 2).of_surjective
      (c.action.subgroupMap (pResidual 2 (HStar J))) (c.action.subgroupMap_surjective _)
    rcases three_twoPerfect_subgroup R hp hz with hc | he
    · exact IsPGroup.of_card (n := 1) hc
    · exact (hn (he ▸ map_le_range c.action _)).elim
  exact (hR.comap_of_ker_isPGroup c.action hk).to_le (le_comap_map _ _)

/-- The literal two-residual and three-core coincide in the elementary-nine branch. -/
theorem local_solvable_nine_residual_eq_threeCore
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (X : Subgroup (pCore 3 (HStar J))) (hX : IsSupercriticalPSubgroup 3 X)
    (e₀ : X ≃* (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) :
    pResidual 2 (HStar J) = pCore 3 (HStar J) := by
  have hp := local_solvable_nine_residual_isThreeGroup h hab structural previous faithful
    J hJ hs X hX e₀
  have hle : pResidual 2 (HStar J) ≤ pCore 3 (HStar J) :=
    le_sSup ⟨inferInstance,hp⟩
  refine le_antisymm hle ?_
  let q := QuotientGroup.mk' (pResidual 2 (HStar J))
  have hz : (pCore 3 (HStar J)).map q = ⊥ := by
    have hd := (pCore_isPGroup (p := 3) (G := HStar J)).map q |>.disjoint_of_coprime
      ((isPGroup_quotient_pResidual 2).to_subgroup ⊤) (by decide : Nat.Coprime 3 2)
    simpa using hd.eq_bot
  simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hz

/-- The selected original lift retains its exact kernel. The elementary-nine
branch now has three-group residual; both branches have the same cubic point image. -/
theorem local_solvable_threeCore_point_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ((QuotientGroup.mk' (pCore 2 J)).comp
      (inclusion (F.Li_one_le_of_mem_Hz hJ))).ker = pCore 2 (F.Li L 1) ∧
    Nat.card (((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) = 3 ∧
    ∃ (X : Subgroup (pCore 3 (HStar J))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup J),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 J ∧
      Y.map (QuotientGroup.mk' (pCore 2 J)) = X.map (pCore 3 (HStar J)).subtype ∧
      ((QuotientGroup.mk' (pCore 2 J)).comp Y.subtype).ker = pCore 2 Y ∧
      ((Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∧
          pResidual 2 (HStar J) = pCore 3 (HStar J)) ∨
        Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3)) := by
  have hp := local_solvable_point_kernel h hab structural previous faithful J hJ hs
  refine ⟨hp.1,hp.2,?_⟩
  obtain ⟨X,hX,Y,hYn,hYp,hYle,hYm,hYk,he⟩ :=
    local_solvable_threeCore_source h hab structural previous faithful J hJ hs
  refine ⟨X,hX,Y,hYn,hYp,hYle,hYm,hYk,?_⟩
  rcases he with he | he
  · exact Or.inl ⟨he,local_solvable_nine_residual_eq_threeCore h hab structural previous faithful
      J hJ hs X hX ((ThreeCorePoint_threeCoreLiftEquiv J X Y hYm hYk).symm.trans he.some)⟩
  · exact Or.inr he

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource


namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Matrix.GeneralLinearGroup PrimeThreeFiveResidual
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original point cubic lies in the three-core through the full Heisenberg Frattini action. -/
theorem local_solvable_heisenberg_point_le_threeCore
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (X : Subgroup (pCore 3 (HStar J))) (hX : IsSupercriticalPSubgroup 3 X)
    (e₀ : X ≃* HeisenbergPrime 3) :
    ((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) ≤ pCore 3 (HStar J) := by
  let : X.Characteristic := hX.characteristic
  let : IsExtraspecial 3 X := IsExtraspecial.of_mulEquiv e₀.symm
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2))
  let : Fact (IsPGroup 3 X) := ⟨IsExtraspecial.isPGroup 3 X⟩
  let : IsElementaryAbelian 3 (X ⧸ frattini X) := isElementaryAbelian_quotient_frattini
  have hcX : Nat.card X = 27 := by rw [Nat.card_congr e₀.toEquiv,HeisenbergPrime.card]; decide
  have hc : Nat.card (X ⧸ frattini X) = 3 ^ 2 := by
    have hh := card_eq_card_quotient_mul_card_subgroup (frattini X)
    have hf : Nat.card (frattini X) = 3 := by
      rw [IsExtraspecial.frattini_eq_center (p := 3),IsExtraspecial.center_order_p 3 X]
    rw [hcX,hf] at hh
    omega
  obtain ⟨c,e,he⟩ := exists_plane_coordinates hc
  let b := (((quotientAut (frattini X)).comp (MulAut.characteristic X)).comp
    (MulAut.conjNormal : HStar J →* MulAut (pCore 3 (HStar J))))
  let a := e.toMonoidHom.comp b
  have hb : b.ker = pCore 3 (HStar J) :=
    local_solvable_heisenberg_frattini_kernel h hab structural previous faithful J hJ hs X hX e₀
  have ha : a.ker = b.ker := by
    ext x
    change e (b x) = 1 ↔ b x = 1
    rw [←e.map_one,e.injective.eq_iff]
  have hak : IsPGroup 3 a.ker := by rw [ha,hb]; exact pCore_isPGroup
  have hGL : Nat.card (GL (Fin 2) (ZMod 3)) = 48 := by
    rw [Matrix.card_GL_field]
    decide
  have hcard : Nat.card a.range ∣ 48 := hGL ▸ a.range.card_subgroup_dvd_card
  let q := QuotientGroup.mk' (pCore 2 J)
  let S := T.subtype (show (T : Subgroup G) ≤ J from fun x hx => hJ.1.2 (Or.inr hx))
  let S₀ := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J))
  have hn : (S : Subgroup J) ≤ normalizer ((F.Li L 1).subgroupOf J : Set J) := by
    rw [←subgroupOf_normalizer_eq (F.Li_one_le_of_mem_Hz hJ)]
    intro x hx
    exact T_normalizes_L₁_at h structural hx
  exact cubic_le_threeCore_of_small_action a hak hcard S₀ _
    (local_solvable_heisenberg_point_kernel h hab structural previous faithful J hJ hs X hX e₀).2
    ((map_mono hn).trans (le_normalizer_map q))

/-- Every original solvable local overgroup has its literal point image contained in its three-core. -/
theorem local_solvable_point_le_threeCore
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) ≤ pCore 3 (HStar J) := by
  obtain ⟨X,hX,Y,hYn,hYp,hYle,hYm,hYk,he⟩ :=
    local_solvable_threeCore_source h hab structural previous faithful J hJ hs
  let e := ThreeCorePoint_threeCoreLiftEquiv J X Y hYm hYk
  rcases he with he | he
  · rw [←local_solvable_nine_residual_eq_threeCore h hab structural previous faithful J hJ hs
      X hX (e.symm.trans he.some)]
    have hp : IsPPerfect 2 (F.Li L 1) := by
      simp only [InvariantFlag.Li]
      exact isPPerfect_embedded_pResidual 2 _
    let f := (QuotientGroup.mk' (pCore 2 J)).comp (inclusion (F.Li_one_le_of_mem_Hz hJ))
    have hh := map_pResidual_le 2 f
    rw [(pResidual_eq_top_iff 2 _).mpr hp,←MonoidHom.range_eq_map,
      MonoidHom.range_comp,inclusion_range] at hh
    exact hh
  · exact local_solvable_heisenberg_point_le_threeCore h hab structural previous faithful
      J hJ hs X hX (e.symm.trans he.some)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The actual point and the selected supercritical three-core lift

For an extraspecial supercritical subgroup, every ambient order-three
root belongs to that subgroup. Apply this to the original cubic point
image inside O₃(J/O₂(J)). Two-perfectness then lifts its containment
through the full two-core to the selected normal lift Y. Consequently
O₂(Y) is properly contained in Y ∩ N_G(L), with both subgroups transported
to the original ambient group. This is the literal intersection premise
used in source 14.7.9.

In the elementary-nine branch, if the point cubic is outside the selected
supercritical image, its centralizer there is a proper nontrivial cubic.
Take a two-perfect lift inside the same Y. It is proper in Y, normalized
by L₁T and by the whole O₂(J), and its quotient map has exactly O₂(W)
as kernel. Its commutator with L₁ lies in O₂(J).

The final application constructs these alternatives on the original
selected witnesses, retaining the elementary-nine residual equality and
all quotient markings. Ambient 14.7.9 and the minimality exclusions are
still needed; this does not assert nonsolvability or finish 14.7.52.

Source: Aschbacher–Smith, A.1.20–23, printed pp.24–25; 14.7.9,
printed p.1045; 14.7.27, printed pp.1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem ThreeCoreLifts_local_point_le_normal_three_lift
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (Y : Subgroup J) [Y.Normal]
    (him : ((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) ≤
      Y.map (QuotientGroup.mk' (pCore 2 J))) : (F.Li L 1).subgroupOf J ≤ Y := by
  let q := QuotientGroup.mk' (pCore 2 J)
  have hp : IsPPerfect 2 ((F.Li L 1).subgroupOf J) := by
    have hp₀ : IsPPerfect 2 (F.Li L 1) := by
      simp only [InvariantFlag.Li]
      exact isPPerfect_embedded_pResidual 2 _
    let e := (subgroupOfEquivOfLe (F.Li_one_le_of_mem_Hz hJ)).symm
    exact hp₀.of_surjective e.toMonoidHom e.surjective
  apply twoPerfect_le_of_le_sup_twoGroup Y _ q.ker hp
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
  rw [←comap_map_eq]
  exact map_le_iff_le_comap.mp him

/-- Every point cubic in the Heisenberg branch lies in the actual supercritical image. -/
theorem local_solvable_heisenberg_point_le_supercritical
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (X : Subgroup (pCore 3 (HStar J))) (hX : IsSupercriticalPSubgroup 3 X)
    (e : X ≃* HeisenbergPrime 3) :
    ((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) ≤
      X.map (pCore 3 (HStar J)).subtype := by
  let : IsExtraspecial 3 X := IsExtraspecial.of_mulEquiv e.symm
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2))
  let B := ((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))
  have hc : Nat.card B = 3 := (local_solvable_point_kernel h hab structural previous faithful J hJ hs).2
  have hBP := local_solvable_point_le_threeCore h hab structural previous faithful J hJ hs
  intro b hb
  have hb3 : b ^ 3 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨b,hb⟩ : B))
    rw [hc] at hh
    exact congrArg Subtype.val hh
  exact mem_map_of_mem (pCore 3 (HStar J)).subtype
    (hX.prime_root_mem_of_extraspecial (⟨b,hBP hb⟩ : pCore 3 (HStar J)) (Subtype.ext hb3))

/-- Point containment lifts through the whole two-core to every selected normal Heisenberg lift. -/
theorem local_solvable_heisenberg_point_le_lift
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (X : Subgroup (pCore 3 (HStar J))) (hX : IsSupercriticalPSubgroup 3 X)
    (e : X ≃* HeisenbergPrime 3) (Y : Subgroup J) [Y.Normal]
    (hm : Y.map (QuotientGroup.mk' (pCore 2 J)) = X.map (pCore 3 (HStar J)).subtype) :
    (F.Li L 1).subgroupOf J ≤ Y := by
  apply ThreeCoreLifts_local_point_le_normal_three_lift J hJ Y
  rw [hm]
  exact local_solvable_heisenberg_point_le_supercritical h hab structural previous faithful J hJ hs X hX e

/-- In the elementary-nine branch an outside point cubic gives an actual proper cubic lift,
normalized by the original point parabolic and the full quotient kernel. -/
theorem local_solvable_nine_outside_point_lift
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (X : Subgroup (pCore 3 (HStar J))) (hX : IsSupercriticalPSubgroup 3 X)
    (e : X ≃* (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)))
    (Y : Subgroup J) [Y.Normal]
    (hm : Y.map (QuotientGroup.mk' (pCore 2 J)) = X.map (pCore 3 (HStar J)).subtype)
    (hout : ¬ ((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) ≤
      X.map (pCore 3 (HStar J)).subtype) :
    ∃ W : Subgroup J, W < Y ∧ IsPPerfect 2 W ∧
      W.map (QuotientGroup.mk' (pCore 2 J)) =
        X.map (pCore 3 (HStar J)).subtype ⊓
          centralizer (((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) : Set (HStar J)) ∧
      ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf J) ≤ normalizer (W : Set J) ∧
      pCore 2 J ≤ normalizer (W : Set J) ∧
      ((QuotientGroup.mk' (pCore 2 J)).comp W.subtype).ker = pCore 2 W ∧
      Nat.card (W ⧸ pCore 2 W) = 3 ∧
      ⁅W,(F.Li L 1).subgroupOf J⁆ ≤ pCore 2 J := by
  let P := pCore 3 (HStar J)
  let q := QuotientGroup.mk' (pCore 2 J)
  let B := ((F.Li L 1).subgroupOf J).map q
  let Z := X.map P.subtype
  let C := Z ⊓ centralizer (B : Set (HStar J))
  let A := (F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf J
  have hcard : Nat.card X = 9 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_prod]
    norm_num [Nat.card_zmod]
  have hne : X ≠ ⊥ := by intro he; simp [he] at hcard
  have hB : Nat.card B = 3 := (local_solvable_point_kernel h hab structural previous faithful J hJ hs).2
  have hBP := local_solvable_point_le_threeCore h hab structural previous faithful J hJ hs
  obtain ⟨hCne,hCZ,hCN⟩ := hX.cubic_centralizer_proper P pCore_isPGroup X B hBP hB hne hout
  have hCsmall : Nat.card C = 3 := by
    have hh := (hX.cubic_centralizer_elementary P pCore_isPGroup X B hBP hB (Or.inl hcard) hout).2
    apply hh.resolve_right
    intro he
    apply hCZ.ne
    exact eq_of_le_of_card_ge inf_le_left (by rw [he,card_map_of_injective P.subtype_injective,hcard])
  have hAN : A ≤ normalizer ((F.Li L 1).subgroupOf J : Set J) := by
    rw [←subgroupOf_normalizer_eq (F.Li_one_le_of_mem_Hz hJ)]
    intro x hx
    exact (sup_le (F.Li L 1).le_normalizer (T_normalizes_L₁_at h structural)) hx
  have hAC : A.map q ≤ normalizer (C : Set (HStar J)) :=
    ((map_mono hAN).trans (le_normalizer_map q)).trans hCN
  obtain ⟨W,hWY,hWp,hWm,hWA,hWk,hker,⟨eW⟩⟩ := exists_three_lift_within_normal q
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) Y C (A.map q)
    (hm.symm ▸ inf_le_left) hAC (IsPGroup.of_card (n := 1) (by simpa using hCsmall))
  refine ⟨W,lt_of_le_of_ne hWY ?_,hWp,hWm,(le_comap_map _ _).trans hWA,(by simpa only [q,QuotientGroup.ker_mk'] using hWk),hker,
    (Nat.card_congr eW.toEquiv).trans hCsmall,?_⟩
  · intro he
    apply hCZ.ne
    calc C = W.map q := hWm.symm
         _ = Y.map q := congrArg (map q) he
         _ = Z := hm
  · rw [←QuotientGroup.ker_mk' (pCore 2 J),←Subgroup.map_eq_bot_iff,map_commutator,hWm]
    exact commutator_eq_bot_iff_le_centralizer.mpr inf_le_right


/-- A normal lift containing the point residual has the strict normalizer intersection
required in 14.7.9, with the intrinsic two-core retained. -/
private theorem ThreeCoreLifts_local_solvable_lift_point_intersection_relative
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) (Y : Subgroup J) [Y.Normal]
    (hpoint : (F.Li L 1).subgroupOf J ≤ Y) :
    Y.pCoreIn 2 < Y ⊓ (normalizer (L : Set G)).subgroupOf J := by
  have hcore : Y.pCoreIn 2 ≤ pCore 2 J :=
    le_sSup ⟨inferInstanceAs (((pCore 2 Y).map Y.subtype).Normal),pCore_isPGroup.map Y.subtype⟩
  let S := T.subtype (show (T : Subgroup G) ≤ J from fun x hx => hJ.1.2 (Or.inr hx))
  have hCM : Y.pCoreIn 2 ≤ (normalizer (L : Set G)).subgroupOf J := by
    intro x hx
    exact h.sylow_normalizes_at structural ((pCore_isPGroup.le_sylow_of_normal S) (hcore hx))
  have hAM : (F.Li L 1).subgroupOf J ≤ (normalizer (L : Set G)).subgroupOf J := by
    intro x hx
    exact L.le_normalizer ((F.Li_le L 1 hx).1)
  refine lt_of_le_of_ne (le_inf (pCoreIn_le 2 Y) hCM) ?_
  intro he
  have hAcore : (F.Li L 1).subgroupOf J ≤ Y.pCoreIn 2 :=
    (le_inf hpoint hAM).trans_eq he.symm
  have hz : ((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
    exact hAcore.trans hcore
  have hc := (local_solvable_point_kernel h hab structural previous faithful J hJ hs).2
  rw [hz,card_bot] at hc
  omega


/-- The strict 14.7.9 intersection, transported to the original ambient group
and its literal normalizer; the core is the lift's intrinsic two-core. -/
theorem local_solvable_lift_point_intersection
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) (Y : Subgroup J) [Y.Normal]
    (hpoint : (F.Li L 1).subgroupOf J ≤ Y) :
    (Y.map J.subtype).pCoreIn 2 < Y.map J.subtype ⊓ normalizer (L : Set G) := by
  have hh := ThreeCoreLifts_local_solvable_lift_point_intersection_relative
    h hab structural previous faithful J hJ hs Y hpoint
  have hm := lt_of_le_of_ne (map_mono (f := J.subtype) hh.le)
    (fun he => hh.ne (map_injective J.subtype_injective he))
  have hi : (Y ⊓ (normalizer (L : Set G)).subgroupOf J).map J.subtype =
      Y.map J.subtype ⊓ normalizer (L : Set G) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨mem_map_of_mem J.subtype hy.1,hy.2⟩
    · rintro ⟨⟨y,hy,rfl⟩,hyM⟩
      exact ⟨y,⟨hy,hyM⟩,rfl⟩
  rwa [map_pCoreIn_of_injective 2 _ _ J.subtype_injective,hi] at hm

private def ThreeCoreLifts_selectedLiftModel (J : Subgroup G)
    (X : Subgroup (pCore 3 (HStar J))) (Y : Subgroup J)
    (hm : Y.map (QuotientGroup.mk' (pCore 2 J)) = X.map (pCore 3 (HStar J)).subtype)
    (hk : ((QuotientGroup.mk' (pCore 2 J)).comp Y.subtype).ker = pCore 2 Y) :
    (Y ⧸ pCore 2 Y) ≃* X := by
  let f := (QuotientGroup.mk' (pCore 2 J)).comp Y.subtype
  have hr : f.range = X.map (pCore 3 (HStar J)).subtype := by
    rw [MonoidHom.range_comp,range_subtype,hm]
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans
      ((MulEquiv.subgroupCongr hr).trans
        (equivMapOfInjective X (pCore 3 (HStar J)).subtype
          (pCore 3 (HStar J)).subtype_injective).symm))

/-- On the original selected lifts, Heisenberg forces the strict point intersection.
The elementary-nine alternative either has the same intersection or an actual
proper cubic lift centralizing the point modulo precisely the full two-core. -/
theorem local_solvable_threeCore_lift_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ∃ (X : Subgroup (pCore 3 (HStar J))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup J),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 J ∧
      Y.map (QuotientGroup.mk' (pCore 2 J)) = X.map (pCore 3 (HStar J)).subtype ∧
      ((QuotientGroup.mk' (pCore 2 J)).comp Y.subtype).ker = pCore 2 Y ∧
      ((Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∧
          pResidual 2 (HStar J) = pCore 3 (HStar J) ∧
          (((F.Li L 1).subgroupOf J ≤ Y ∧
              (Y.map J.subtype).pCoreIn 2 < Y.map J.subtype ⊓ normalizer (L : Set G)) ∨
            ∃ W : Subgroup J, W < Y ∧ IsPPerfect 2 W ∧
              W.map (QuotientGroup.mk' (pCore 2 J)) =
                X.map (pCore 3 (HStar J)).subtype ⊓
                  centralizer (((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) : Set (HStar J)) ∧
              ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf J) ≤ normalizer (W : Set J) ∧
              pCore 2 J ≤ normalizer (W : Set J) ∧
              ((QuotientGroup.mk' (pCore 2 J)).comp W.subtype).ker = pCore 2 W ∧
              Nat.card (W ⧸ pCore 2 W) = 3 ∧
              ⁅W,(F.Li L 1).subgroupOf J⁆ ≤ pCore 2 J)) ∨
        (Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3) ∧
          (F.Li L 1).subgroupOf J ≤ Y ∧
          (Y.map J.subtype).pCoreIn 2 < Y.map J.subtype ⊓ normalizer (L : Set G))) := by
  obtain ⟨_,_,X,hX,Y,hYn,hYp,hYle,hm,hk,he⟩ :=
    local_solvable_threeCore_point_reduction h hab structural previous faithful J hJ hs
  let := hYn
  let e := ThreeCoreLifts_selectedLiftModel J X Y hm hk
  refine ⟨X,hX,Y,hYn,hYp,hYle,hm,hk,?_⟩
  rcases he with ⟨he,hr⟩ | he
  · refine Or.inl ⟨he,hr,?_⟩
    by_cases hb : ((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) ≤
        X.map (pCore 3 (HStar J)).subtype
    · have hpoint := ThreeCoreLifts_local_point_le_normal_three_lift J hJ Y (hm.symm ▸ hb)
      exact Or.inl ⟨hpoint,local_solvable_lift_point_intersection
        h hab structural previous faithful J hJ hs Y hpoint⟩
    · exact Or.inr (local_solvable_nine_outside_point_lift h hab structural previous faithful
        J hJ hs X hX (e.symm.trans he.some) Y hm hb)
  · have hpoint := local_solvable_heisenberg_point_le_lift h hab structural previous faithful
      J hJ hs X hX (e.symm.trans he.some) Y hm
    exact Or.inr ⟨he,hpoint,local_solvable_lift_point_intersection
      h hab structural previous faithful J hJ hs Y hpoint⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Ambient normalizer control for the selected three-core lifts

A nontrivial T-invariant two-perfect subgroup of an original local J whose
L-commutators lie in O₂(L) has full normalizer in M = N_G(L). Thus an actual
normal two-perfect lift in an escaping J cannot centralize L/O₂(L). When
it lies in M, the literal quotient action is nontrivial.

For the selected Heisenberg subgroup, lift its actual cubic center within
the same normal Y. This is a proper normal two-perfect cubic lift with
exactly O₂(Z) as the original star-map kernel. Its two-core is nontrivial,
and the ambient normalizer argument supplies the same L-commutator
obstruction. This proves the normalizer step, not the full 14.7.9 restriction.

Source: Aschbacher–Smith, 14.5.20, printed pp.1018–1019; 14.7.9 and
14.7.27, printed pp.1045,1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The source's full normalizer bound for T-invariant two-perfect subgroups
centralizing L modulo its intrinsic two-core. -/
theorem local_twoPerfect_core_commutator_normalizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (X : Subgroup G) (hXJ : X ≤ J) (hp : IsPPerfect 2 X) (hne : X ≠ ⊥)
    (hTX : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hc : ⁅L,X⁆ ≤ L.pCoreIn 2) :
    normalizer (X : Set G) ≤ normalizer (L : Set G) := by
  have hu : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro A _ _ hA S M hM
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hA S hM
  apply normalizer_le_of_twoPerfect_core_commutator T L J (normalizer (L : Set G)) X
    (fun x hx => hJ.1.2 (Or.inr hx))
    (F.localKernel_characteristicTwo h.source.simpleQTKE L _ J hJ)
    hXJ hTX hp hne (InvariantFlag.localKernel_L_core_le_T L (h.sylow_normalizes_at structural)) hc
  intro N hN hLN
  exact Set.mem_singleton_iff.mp ((h.maximal_unique_at structural).2 ▸
    show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
      from ⟨hN,hLN⟩)

/-- A nontrivial normal two-perfect lift in an escaping original local
cannot centralize L modulo O₂(L). No containment of the lift in M is needed. -/
theorem local_normal_twoPerfect_not_core_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (Y : Subgroup J) [Y.Normal] (hp : IsPPerfect 2 Y) (hne : Y ≠ ⊥) :
    ¬ ⁅L,Y.map J.subtype⁆ ≤ L.pCoreIn 2 := by
  intro hc
  have hJY : J ≤ normalizer (Y.map J.subtype : Set G) := by
    simpa only [normalizer_eq_top, ←MonoidHom.range_eq_map,range_subtype] using
      Y.le_normalizer_map J.subtype
  have hn := local_twoPerfect_core_commutator_normalizer h structural J hJ
    (Y.map J.subtype) (map_subtype_le Y)
    (hp.of_surjective (J.subtype.subgroupMap Y) (J.subtype.subgroupMap_surjective Y))
    (fun he => hne ((Y.map_eq_bot_iff_of_injective J.subtype_injective).mp he))
    ((show (T : Subgroup G) ≤ J from fun x hx => hJ.1.2 (Or.inr hx)).trans hJY) hc
  exact hJ.2.2 (hJY.trans hn)

/-- If such a lift lies in M, its literal action on L/O₂(L) is nontrivial. -/
theorem local_normal_twoPerfect_quotient_action_nontrivial
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (Y : Subgroup J) [Y.Normal] (hp : IsPPerfect 2 Y) (hne : Y ≠ ⊥)
    (hM : Y.map J.subtype ≤ normalizer (L : Set G)) :
    ∃ x : Y.map J.subtype,
      normalizerQuotientAction L (pCore 2 L) (inclusion hM x) ≠ 1 := by
  by_contra hn
  push Not at hn
  exact local_normal_twoPerfect_not_core_commutator h structural J hJ Y hp hne
    (commutator_le_of_normalizerQuotientAction_eq_one L (Y.map J.subtype) (pCore 2 L) hM hn)

/-- The selected Heisenberg lift has a proper normal cubic-center lift,
with the full original star-map kernel and nontrivial ambient L-action. -/
theorem local_solvable_heisenberg_center_lift
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (X : Subgroup (pCore 3 (HStar J))) (hX : IsSupercriticalPSubgroup 3 X)
    (e : X ≃* HeisenbergPrime 3) (Y : Subgroup J) [Y.Normal]
    (hm : Y.map (QuotientGroup.mk' (pCore 2 J)) = X.map (pCore 3 (HStar J)).subtype) :
    ∃ Z : Subgroup J, Z < Y ∧ Z.Normal ∧ IsPPerfect 2 Z ∧
      Z.map (QuotientGroup.mk' (pCore 2 J)) =
        ((center X).map X.subtype).map (pCore 3 (HStar J)).subtype ∧
      ((QuotientGroup.mk' (pCore 2 J)).comp Z.subtype).ker = pCore 2 Z ∧
      Nat.card (Z ⧸ pCore 2 Z) = 3 ∧
      Nonempty ((Z ⧸ pCore 2 Z) ≃* center X) ∧
      pCore 2 Z ≠ ⊥ ∧ ¬ ⁅L,Z.map J.subtype⁆ ≤ L.pCoreIn 2 := by
  let P := pCore 3 (HStar J)
  let q := QuotientGroup.mk' (pCore 2 J)
  let : X.Characteristic := hX.characteristic
  let : IsExtraspecial 3 X := IsExtraspecial.of_mulEquiv e.symm
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2))
  let C := (center X).map X.subtype
  let D := C.map P.subtype
  let : D.Characteristic := inferInstance
  have hD : Nat.card D = 3 := by
    rw [card_map_of_injective P.subtype_injective,card_map_of_injective X.subtype_injective,
      IsExtraspecial.center_order_p 3 X]
  have hDY : D ≤ Y.map q := by
    rw [hm]
    exact map_mono (map_subtype_le (center X))
  obtain ⟨Z,hZY,hZp,hZm,hZN,hZQ,hZk,⟨eZ⟩⟩ := exists_three_lift_within_normal q
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) Y D ⊤ hDY
    le_normalizer_of_normal (IsPGroup.of_card (n := 1) (by simpa using hD))
  have hZn : Z.Normal := normalizer_eq_top_iff.mp (top_unique (by simpa using hZN))
  let := hZn
  have hZne : Z ≠ ⊥ := by
    intro he
    have hd := hZm
    rw [he,Subgroup.map_bot] at hd
    rw [←hd,card_bot] at hD
    omega
  have hZYlt : Z < Y := lt_of_le_of_ne hZY (by
    intro he
    have hc : Nat.card (Y.map q) = 27 := by
      rw [hm,card_map_of_injective P.subtype_injective,Nat.card_congr e.toEquiv,
        HeisenbergPrime.card]
      decide
    rw [←he,hZm,hD] at hc
    omega)
  have hcore : pCore 2 Z ≠ ⊥ := by
    have hZJ : Z.map J.subtype ≤ J := map_subtype_le Z
    have hnJ : J ≤ normalizer (Z.map J.subtype : Set G) := by
      simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
        Z.le_normalizer_map J.subtype
    have hn := pCore_ne_bot_of_core_normalizes J (Z.map J.subtype) hZJ
      (F.localKernel_characteristicTwo h.source.simpleQTKE L _ J hJ)
      ((pCoreIn_le 2 J).trans hnJ)
      (fun he => hZne ((Z.map_eq_bot_iff_of_injective J.subtype_injective).mp he))
    intro he
    apply hn
    rw [←pCore_map_iso 2 (equivMapOfInjective Z J.subtype J.subtype_injective),he,Subgroup.map_bot]
  let eC : center X ≃* D :=
    (equivMapOfInjective (center X) X.subtype X.subtype_injective).trans
      (equivMapOfInjective C P.subtype P.subtype_injective)
  exact ⟨Z,hZYlt,hZn,hZp,hZm,hZk,(Nat.card_congr eZ.toEquiv).trans hD,
    ⟨eZ.trans eC.symm⟩,hcore,
    local_normal_twoPerfect_not_core_commutator h structural J hJ Z hZp hZne⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Minimal solvable locals and the strict source intersection

Choose a minimal escaping solvable overgroup of the original L₁T. Every
proper subgroup between L₁T and this witness lies in M = N_G(L). In the
outside-point elementary-nine branch, the actual cubic fixed-line lift
and L₁T generate a proper subgroup: otherwise its three-core would have
order at most nine and contain both the selected nine-group and the
outside point. Minimality therefore places this cubic lift in M.

Its nontrivial image through the full O₂(J) kernel gives
O₂(Y) < Y ∩ M for the selected normal lift Y. The other elementary-nine
case and the Heisenberg case already have this intersection by point
containment. The final theorem constructs the minimal witness and all
markings from the original hypotheses, so the intersection now holds in
every remaining solvable branch. It also retains the proper normal
cubic-center lift and ambient commutator obstruction in the Heisenberg case.

The ambient restriction 14.7.9 and terminal exclusions remain required;
this does not assert nonsolvability or the four final Data inputs.
Source: Aschbacher–Smith, 14.7.9 and 14.7.27–29, printed pp.1045,
1054–1055, refs/quasithin.pdf.
-/


public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Choose an actual minimal escaping solvable local subgroup. Every proper
overgroup of the original point parabolic inside it lies in M. -/
theorem exists_minimal_solvable_local
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ∃ I : Subgroup G, I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      Group.IsSolvable I ∧
      ∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < I →
        D ≤ normalizer (L : Set G) := by
  obtain ⟨I,⟨hI,hIs⟩,hIJ,hmin⟩ := exists_minimal_subgroup_of_mem_le
    (fun D : Subgroup G => D ∈ F.Hz L (normalizer (L : Set G)) ∧ Group.IsSolvable D)
    J ⟨hJ,hs⟩
  refine ⟨I,hIJ,hI,hIs,?_⟩
  intro D hBD hDI
  by_contra hout
  have hc : Nat.card (F.Vi 1) = 2 := F.card 1 (by decide)
  have hpoint : F.Vi 1 ≤ D.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsPGroup.of_card (n := 1) (by simpa using hc))
    ((F.le_seed 1).trans (h.chosen.le_sylow.trans (le_sup_right.trans hBD)))
    (hDI.le.trans hI.2.1)
  have hcore : D.pCoreIn 2 ≠ ⊥ := by
    intro he
    have hz := le_bot_iff.mp (he ▸ hpoint)
    rw [hz,card_bot] at hc
    omega
  have hD : D ∈ F.Hz L (normalizer (L : Set G)) :=
    ⟨⟨hcore,fun _ hx => hx.elim (fun ha => hBD (mem_sup_left ha))
      (fun ha => hBD (mem_sup_right ha))⟩,hDI.le.trans hI.2.1,hout⟩
  let := hIs
  have hDs : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective
    (f := inclusion hDI.le) (inclusion_injective hDI.le)
  exact hDI.ne (hmin D ⟨hD,hDs⟩ hDI.le)

/-- The actual outside-point cubic lift and original point parabolic generate
a proper subgroup of J, with the full two-core retained. -/
theorem local_solvable_nine_cubic_join_proper
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (X : Subgroup (pCore 3 (HStar J)))
    (hX : Nat.card X = 9)
    (hout : ¬ ((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) ≤
      X.map (pCore 3 (HStar J)).subtype)
    (W : Subgroup J)
    (hm : W.map (QuotientGroup.mk' (pCore 2 J)) =
      X.map (pCore 3 (HStar J)).subtype ⊓
        centralizer (((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) : Set (HStar J)))
    (hWN : ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf J) ≤ normalizer (W : Set J))
    (hk : ((QuotientGroup.mk' (pCore 2 J)).comp W.subtype).ker = pCore 2 W)
    (hc : Nat.card (W ⧸ pCore 2 W) = 3) :
    W.map J.subtype ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) < J := by
  let q := QuotientGroup.mk' (pCore 2 J)
  let P := pCore 3 (HStar J)
  let B := (F.Li L 1).subgroupOf J
  let S := T.subtype (F.sylow_le_of_mem_Hz hJ)
  have hBN : (S : Subgroup J) ≤ normalizer (B : Set J) := by
    rw [←subgroupOf_normalizer_eq (F.Li_one_le_of_mem_Hz hJ)]
    intro x hx
    exact T_normalizes_L₁_at h structural hx
  have hCW : Nat.card (W.map q) = 3 := by
    let f := q.comp W.subtype
    have hr : f.range = W.map q := by rw [MonoidHom.range_comp,range_subtype]
    rw [←hr,←Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,hk]
    exact hc
  have hnorm : (S : Subgroup J) ≤ normalizer (W : Set J) :=
    (show (S : Subgroup J) ≤ (F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf J from
      fun x hx => mem_sup_right hx).trans hWN
  have hne := cubic_fixed_line_join_ne_top (X.map P.subtype) (B.map q) (W.map q)
    ((S : Subgroup J).map q)
    ((card_map_of_injective P.subtype_injective).trans hX) (map_subtype_le X)
    (local_solvable_point_kernel h hab structural previous faithful J hJ hs).2 hCW
    ((le_centralizer_iff.mp (hm ▸ inf_le_right)).trans (Subgroup.centralizer_le_normalizer _)) hout
    (S.isPGroup'.map q) ((map_mono hBN).trans (le_normalizer_map q))
    ((map_mono hnorm).trans (le_normalizer_map q))
  let D := W ⊔ B ⊔ (S : Subgroup J)
  have hDne : D ≠ ⊤ := by
    intro he
    apply hne
    rw [←Subgroup.map_sup,←Subgroup.map_sup,show W ⊔ B ⊔ (S : Subgroup J) = D from rfl,he,
      map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  have hmap : D.map J.subtype = W.map J.subtype ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) := by
    rw [show D = W ⊔ B ⊔ (S : Subgroup J) from rfl,Subgroup.map_sup,Subgroup.map_sup,
      map_subgroupOf_eq_of_le (F.Li_one_le_of_mem_Hz hJ),Sylow.coe_subtype,
      map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hJ),sup_assoc]
  rw [←hmap]
  exact lt_of_le_of_ne (map_subtype_le D) (fun he => hDne
    (map_injective J.subtype_injective (by simpa only [←MonoidHom.range_eq_map,range_subtype] using he)))

/-- Minimality places the actual outside-point cubic lift in M. This is the
proper-centralizer step of 14.7.27 on the original local and quotient map. -/
theorem local_minimal_solvable_nine_outside_point_lift
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (hmin : ∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < J →
      D ≤ normalizer (L : Set G))
    (X : Subgroup (pCore 3 (HStar J))) (hX : IsSupercriticalPSubgroup 3 X)
    (e : X ≃* (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)))
    (Y : Subgroup J) [Y.Normal]
    (hm : Y.map (QuotientGroup.mk' (pCore 2 J)) = X.map (pCore 3 (HStar J)).subtype)
    (hout : ¬ ((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) ≤
      X.map (pCore 3 (HStar J)).subtype) :
    ∃ W : Subgroup J, W < Y ∧ IsPPerfect 2 W ∧
      W.map (QuotientGroup.mk' (pCore 2 J)) =
        X.map (pCore 3 (HStar J)).subtype ⊓
          centralizer (((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) : Set (HStar J)) ∧
      ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf J) ≤ normalizer (W : Set J) ∧
      pCore 2 J ≤ normalizer (W : Set J) ∧
      ((QuotientGroup.mk' (pCore 2 J)).comp W.subtype).ker = pCore 2 W ∧
      Nat.card (W ⧸ pCore 2 W) = 3 ∧
      ⁅W,(F.Li L 1).subgroupOf J⁆ ≤ pCore 2 J ∧
      W.map J.subtype ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) < J ∧
      W.map J.subtype ≤ normalizer (L : Set G) := by
  obtain ⟨W,hWY,hWp,hWm,hWA,hWQ,hWk,hWc,hWB⟩ := local_solvable_nine_outside_point_lift
    h hab structural previous faithful J hJ hs X hX e Y hm hout
  have hcX : Nat.card X = 9 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_prod]
    norm_num [Nat.card_zmod]
  have hproper := local_solvable_nine_cubic_join_proper h hab structural previous faithful
    J hJ hs X hcX hout W hWm hWA hWk hWc
  exact ⟨W,hWY,hWp,hWm,hWA,hWQ,hWk,hWc,hWB,hproper,
    le_sup_left.trans (hmin _ le_sup_right hproper)⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- A cubic sublift lying in M makes the original normal lift meet M beyond
its own two-core. The kernel used to detect nontriviality is the whole O₂(J). -/
theorem local_lift_intersection_of_cubic_sublift
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (Y : Subgroup J) [Y.Normal] (W : Subgroup J) (hWY : W ≤ Y)
    (hWM : W.map J.subtype ≤ normalizer (L : Set G))
    (hk : ((QuotientGroup.mk' (pCore 2 J)).comp W.subtype).ker = pCore 2 W)
    (hc : Nat.card (W ⧸ pCore 2 W) = 3) :
    (Y.map J.subtype).pCoreIn 2 < Y.map J.subtype ⊓ normalizer (L : Set G) := by
  have hcore : Y.pCoreIn 2 ≤ pCore 2 J :=
    le_sSup ⟨inferInstanceAs (((pCore 2 Y).map Y.subtype).Normal),pCore_isPGroup.map Y.subtype⟩
  have hQJ : J.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow J (T.subtype (F.sylow_le_of_mem_Hz hJ))
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hJ)] at hh
  have hQM : (Y.map J.subtype).pCoreIn 2 ≤ normalizer (L : Set G) := by
    rw [←map_pCoreIn_of_injective 2 Y J.subtype J.subtype_injective]
    exact (map_mono hcore).trans (hQJ.trans (h.sylow_normalizes_at structural))
  refine lt_of_le_of_ne (le_inf (pCoreIn_le 2 _) hQM) ?_
  intro he
  have hWcore : W.map J.subtype ≤ (Y.map J.subtype).pCoreIn 2 :=
    (le_inf (map_mono hWY) hWM).trans_eq he.symm
  rw [←map_pCoreIn_of_injective 2 Y J.subtype J.subtype_injective] at hWcore
  have hWQ : W ≤ pCore 2 J :=
    ((map_le_map_iff_of_injective J.subtype_injective).mp hWcore).trans hcore
  have hktop : ((QuotientGroup.mk' (pCore 2 J)).comp W.subtype).ker = ⊤ := by
    apply top_unique
    intro w _
    change QuotientGroup.mk' (pCore 2 J) (w : J) = 1
    exact (QuotientGroup.eq_one_iff _).mpr (hWQ w.property)
  rw [←hk,hktop] at hc
  have hone : Nat.card (W ⧸ (⊤ : Subgroup W)) = 1 := by
    rw [←index_eq_card,index_top]
  omega

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Original solvable locals supply a minimal witness with the ambient
normalizer obstruction and the proper-lift minimality step discharged.
The contained-point and normal-center exclusions remain to be proved. -/
theorem local_minimal_solvable_threeCore_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ∃ (I : Subgroup G), I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      Group.IsSolvable I ∧
      (∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < I →
        D ≤ normalizer (L : Set G)) ∧
    ∃ (X : Subgroup (pCore 3 (HStar I))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup I),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 I ∧
      Y.map (QuotientGroup.mk' (pCore 2 I)) = X.map (pCore 3 (HStar I)).subtype ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
      (¬ ⁅L,Y.map I.subtype⁆ ≤ L.pCoreIn 2) ∧
      (Y.map I.subtype).pCoreIn 2 < Y.map I.subtype ⊓ normalizer (L : Set G) ∧
      ((Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∧
          pResidual 2 (HStar I) = pCore 3 (HStar I)) ∨
        (Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3) ∧
          (F.Li L 1).subgroupOf I ≤ Y ∧
          ∃ Z : Subgroup I, Z < Y ∧ Z.Normal ∧ IsPPerfect 2 Z ∧
            Z.map (QuotientGroup.mk' (pCore 2 I)) =
              ((center X).map X.subtype).map (pCore 3 (HStar I)).subtype ∧
            ((QuotientGroup.mk' (pCore 2 I)).comp Z.subtype).ker = pCore 2 Z ∧
            Nat.card (Z ⧸ pCore 2 Z) = 3 ∧ Nonempty ((Z ⧸ pCore 2 Z) ≃* center X) ∧
            pCore 2 Z ≠ ⊥ ∧ ¬ ⁅L,Z.map I.subtype⁆ ≤ L.pCoreIn 2)) := by
  obtain ⟨I,hIJ,hI,hIs,hmin⟩ := exists_minimal_solvable_local h J hJ hs
  obtain ⟨X,hX,Y,hYn,hYp,hYr,hm,hk,he⟩ :=
    local_solvable_threeCore_source h hab structural previous faithful I hI hIs
  let := hYn
  let eX : (Y ⧸ pCore 2 Y) ≃* X := (coreQuotientEquivImage 2 Y).trans
    ((MulEquiv.subgroupCongr hm).trans
      (equivMapOfInjective X (pCore 3 (HStar I)).subtype
        (pCore 3 (HStar I)).subtype_injective).symm)
  have hYne : Y ≠ ⊥ := by
    intro hz
    have hone : Nat.card (Y ⧸ pCore 2 Y) = 1 := by
      have hd := card_quotient_dvd_card (pCore 2 Y)
      have hcardY : Nat.card Y = 1 := by rw [hz,card_bot]
      rw [hcardY] at hd
      exact Nat.dvd_one.mp hd
    rcases he with he | he
    · rw [Nat.card_congr he.some.toEquiv,Nat.card_prod] at hone
      norm_num [Nat.card_zmod] at hone
    · rw [Nat.card_congr he.some.toEquiv,HeisenbergPrime.card] at hone
      norm_num at hone
  refine ⟨I,hIJ,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,
    local_normal_twoPerfect_not_core_commutator h structural I hI Y hYp hYne,?_⟩
  rcases he with he | he
  · let e := eX.symm.trans he.some
    have hr := local_solvable_nine_residual_eq_threeCore h hab structural previous faithful
      I hI hIs X hX e
    by_cases hpoint : (F.Li L 1).subgroupOf I ≤ Y
    · exact ⟨local_solvable_lift_point_intersection
        h hab structural previous faithful I hI hIs Y hpoint,Or.inl ⟨he,hr⟩⟩
    · have hout : ¬ ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) ≤
          X.map (pCore 3 (HStar I)).subtype := by
        intro hh
        apply hpoint
        have hp : IsPPerfect 2 ((F.Li L 1).subgroupOf I) := by
          have hp₀ : IsPPerfect 2 (F.Li L 1) := by
            simp only [InvariantFlag.Li]
            exact isPPerfect_embedded_pResidual 2 _
          let e₀ := (subgroupOfEquivOfLe (F.Li_one_le_of_mem_Hz hI)).symm
          exact hp₀.of_surjective e₀.toMonoidHom e₀.surjective
        apply twoPerfect_le_of_le_sup_twoGroup Y _ (pCore 2 I) hp pCore_isPGroup
        rw [←QuotientGroup.ker_mk' (pCore 2 I),←comap_map_eq]
        exact map_le_iff_le_comap.mp (hm.symm ▸ hh)
      obtain ⟨W,hWY,_,_,_,_,hWk,hWc,_,_,hWM⟩ :=
        local_minimal_solvable_nine_outside_point_lift h hab structural previous faithful
          I hI hIs hmin X hX e Y hm hout
      exact ⟨local_lift_intersection_of_cubic_sublift h structural I hI Y W hWY.le hWM hWk hWc,Or.inl ⟨he,hr⟩⟩
  · let e := eX.symm.trans he.some
    have hpoint := local_solvable_heisenberg_point_le_lift h hab structural previous faithful
      I hI hIs X hX e Y hm
    exact ⟨local_solvable_lift_point_intersection h hab structural previous faithful I hI hIs Y hpoint,
      Or.inr ⟨he,hpoint,local_solvable_heisenberg_center_lift h structural I hI X hX e Y hm⟩⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end
end
end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Nontrivial action of the actual normalizer intersection

Let Y be a normal lift in an original local J, with three-group quotient
and O₂(Y) < Y ∩ M, where M = N_G(L). The two-residual R of this intersection
acts nontrivially on L/O₂(L). Otherwise ambient uniqueness puts N_G(R)
in M. A nontrivial normal lift Z of the center of the star image normalizes
R, hence lies in M and therefore in R. This contradicts the established
ambient obstruction for normal two-perfect subgroups.

The final theorem applies this to the original minimal solvable witness.
It retains both actual quotient models, the entire star-map kernels, and
the proper Heisenberg-center lift. It constructs a nontrivial actor in the
literal normalizer quotient action. The subsequent point containment,
terminal solvable exclusions, component reductions and four Data inputs
remain required.

Source: Aschbacher–Smith, 14.5.20 assertion (*), printed p.1019;
14.7.9 and 14.7.27–29, printed pp.1045,1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The intersection residual in the ambient restriction acts nontrivially
on L/O₂(L), using an actual normal central lift in Y. -/
private theorem ThreeCoreIntersection_local_three_lift_intersection_moves
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (Y Z : Subgroup J) [Y.Normal] [Z.Normal]
    (hZY : Z ≤ Y) (hZp : IsPPerfect 2 Z) (hZn : Z ≠ ⊥)
    (h3 : IsPGroup 3 (Y ⧸ pCore 2 Y))
    (hc : ⁅Z.map (QuotientGroup.mk' (pCore 2 J)),
      Y.map (QuotientGroup.mk' (pCore 2 J))⁆ = ⊥)
    (hi : (Y.map J.subtype).pCoreIn 2 < Y.map J.subtype ⊓ normalizer (L : Set G)) :
    ¬ ⁅L,(pResidual 2 (Y.map J.subtype ⊓ normalizer (L : Set G) : Subgroup G)).map
      (Y.map J.subtype ⊓ normalizer (L : Set G)).subtype⁆ ≤ L.pCoreIn 2 := by
  let A := Y.map J.subtype
  let C := Z.map J.subtype
  let M := normalizer (L : Set G)
  let I := A ⊓ M
  let R := (pResidual 2 I).map I.subtype
  let e := equivMapOfInjective Y J.subtype J.subtype_injective
  have hA3 : IsPGroup 3 (A ⧸ pCore 2 A) := h3.of_equiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  have hRn : R ≠ ⊥ := intersection_twoResidual_ne_bot A M hA3 hi
  have hJY : J ≤ normalizer (A : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      Y.le_normalizer_map J.subtype
  have hTJ : (T : Subgroup G) ≤ J := F.sylow_le_of_mem_Hz hJ
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (((le_inf (hTJ.trans hJY) ((h.sylow_normalizes_at structural).trans M.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf).trans
        (normalizer_le_normalizer_characteristic_image I (pResidual 2 I)))
  intro hcomm
  have hbound : normalizer (R : Set G) ≤ M :=
    local_twoPerfect_core_commutator_normalizer h structural J hJ R
      ((map_subtype_le _).trans (inf_le_left.trans (map_subtype_le Y)))
      (isPPerfect_embedded_pResidual 2 I) hRn hTR hcomm
  have hCA : ⁅C,A⁆ ≤ A.pCoreIn 2 := by
    have hh := map_mono (f := J.subtype) (commutator_le_core_of_quotient_centralizes Y Z hc)
    rwa [map_commutator,map_pCoreIn_of_injective 2 Y J.subtype J.subtype_injective] at hh
  have hCM : C ≤ M :=
    (normalizes_intersection_twoResidual A M C (hi.le.trans inf_le_right) hCA).trans hbound
  have hCI : C ≤ I := le_inf (map_mono hZY) hCM
  have hCp : IsPPerfect 2 C := hZp.of_surjective (J.subtype.subgroupMap Z)
    (J.subtype.subgroupMap_surjective Z)
  have hCR : C ≤ R := by
    have hm := embedded_pResidual_mono 2 hCI
    rwa [(pResidual_eq_top_iff 2 C).mpr hCp,←MonoidHom.range_eq_map,range_subtype] at hm
  exact local_normal_twoPerfect_not_core_commutator h structural J hJ Z hZp hZn
    ((commutator_mono le_rfl hCR).trans hcomm)

/-- Source 14.5.20's strict-action assertion for the actual intersection
in 14.7.9. No central lift or local recognition is assumed. -/
theorem local_three_intersection_residual_moves
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (Y : Subgroup J) [Y.Normal]
    (h3 : IsPGroup 3 (Y ⧸ pCore 2 Y))
    (hi : (Y.map J.subtype).pCoreIn 2 < Y.map J.subtype ⊓ normalizer (L : Set G)) :
    ¬ ⁅L,(pResidual 2 (Y.map J.subtype ⊓ normalizer (L : Set G) : Subgroup G)).map
      (Y.map J.subtype ⊓ normalizer (L : Set G)).subtype⁆ ≤ L.pCoreIn 2 := by
  let q := QuotientGroup.mk' (pCore 2 J)
  have hn : Y.map q ≠ ⊥ := by
    intro he
    have hYQ : Y ≤ pCore 2 J := by
      simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff Y).mp he
    have hYY : Y ≤ Y.pCoreIn 2 := le_pCoreIn_of_normalizes
      (pCore_isPGroup.to_le hYQ) le_rfl Y.le_normalizer
    have hm := map_mono (f := J.subtype) hYY
    rw [map_pCoreIn_of_injective 2 Y J.subtype J.subtype_injective] at hm
    exact hi.not_ge (inf_le_left.trans hm)
  obtain ⟨Z,hZY,hZn,hZp,hZne,_,_,_,hc⟩ := exists_normal_central_three_lift q
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
    Y (h3.of_equiv (coreQuotientEquivImage 2 Y)) hn
  let := hZn
  exact ThreeCoreIntersection_local_three_lift_intersection_moves h structural J hJ Y Z hZY hZp hZne h3 hc hi

/-- The intersection residual has a nontrivial literal quotient action;
this is (*) in 14.5.20 on the original ambient normalizer. -/
theorem local_three_intersection_quotient_action
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (Y : Subgroup J) [Y.Normal]
    (h3 : IsPGroup 3 (Y ⧸ pCore 2 Y))
    (hi : (Y.map J.subtype).pCoreIn 2 < Y.map J.subtype ⊓ normalizer (L : Set G)) :
    ∃ x : (pResidual 2 (Y.map J.subtype ⊓ normalizer (L : Set G) : Subgroup G)).map
      (Y.map J.subtype ⊓ normalizer (L : Set G)).subtype,
      normalizerQuotientAction L (pCore 2 L)
        (inclusion ((map_subtype_le _).trans inf_le_right) x) ≠ 1 := by
  by_contra hn
  push Not at hn
  exact local_three_intersection_residual_moves h structural J hJ Y h3 hi
    (commutator_le_of_normalizerQuotientAction_eq_one L _ (pCore 2 L)
      ((map_subtype_le _).trans inf_le_right) hn)

open Chapter14.Section04.LargerDimension.LocalAction.Components in
/-- Apply the ambient strict-action restriction to the selected lifts on the
original minimal solvable witness. Both model alternatives, all normalities,
and the exact star kernels are retained. -/
theorem local_minimal_solvable_threeCore_intersection_action
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ∃ (I : Subgroup G), I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      Group.IsSolvable I ∧
      (∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < I →
        D ≤ normalizer (L : Set G)) ∧
    ∃ (X : Subgroup (pCore 3 (HStar I))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup I),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 I ∧
      Y.map (QuotientGroup.mk' (pCore 2 I)) = X.map (pCore 3 (HStar I)).subtype ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
      (¬ ⁅L,Y.map I.subtype⁆ ≤ L.pCoreIn 2) ∧
      (Y.map I.subtype).pCoreIn 2 < Y.map I.subtype ⊓ normalizer (L : Set G) ∧
      (∃ x : (pResidual 2 (Y.map I.subtype ⊓ normalizer (L : Set G) : Subgroup G)).map
          (Y.map I.subtype ⊓ normalizer (L : Set G)).subtype,
        normalizerQuotientAction L (pCore 2 L)
          (inclusion ((map_subtype_le _).trans inf_le_right) x) ≠ 1) ∧
      ((Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∧
          pResidual 2 (HStar I) = pCore 3 (HStar I)) ∨
        (Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3) ∧
          (F.Li L 1).subgroupOf I ≤ Y ∧
          ∃ Z : Subgroup I, Z < Y ∧ Z.Normal ∧ IsPPerfect 2 Z ∧
            Z.map (QuotientGroup.mk' (pCore 2 I)) =
              ((center X).map X.subtype).map (pCore 3 (HStar I)).subtype ∧
            ((QuotientGroup.mk' (pCore 2 I)).comp Z.subtype).ker = pCore 2 Z ∧
            Nat.card (Z ⧸ pCore 2 Z) = 3 ∧ Nonempty ((Z ⧸ pCore 2 Z) ≃* center X) ∧
            pCore 2 Z ≠ ⊥ ∧ ¬ ⁅L,Z.map I.subtype⁆ ≤ L.pCoreIn 2)) := by
  obtain ⟨I,hIJ,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,hmove,hi,he⟩ :=
    local_minimal_solvable_threeCore_reduction h hab structural previous faithful J hJ hs
  let := hYn
  let eX : (Y ⧸ pCore 2 Y) ≃* X := (coreQuotientEquivImage 2 Y).trans
    ((MulEquiv.subgroupCongr hm).trans
      (equivMapOfInjective X (pCore 3 (HStar I)).subtype
        (pCore 3 (HStar I)).subtype_injective).symm)
  have h3 : IsPGroup 3 (Y ⧸ pCore 2 Y) :=
    ((pCore_isPGroup (p := 3) (G := HStar I)).to_subgroup X).of_equiv eX.symm
  exact ⟨I,hIJ,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,hmove,hi,
    local_three_intersection_quotient_action h structural I hI Y h3 hi,he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Point containment in the actual normal three-lift

Let Y be normal in an original local J and suppose Y/O₂(Y) is a three-group
and O₂(Y) < Y ∩ N_G(L). The two-residual of this intersection has a nontrivial
literal action on L/O₂(L). The original natural marking identifies its
image with the inner A₄ of the point parabolic. Commutators with T ∩ L recover
that same image inside Y ∩ L. Two-perfectness then lifts the containment
through O₂(L), which normalizes Y, proving L₁ ≤ Y.

The private marking and quotient-action transports refine the established
argument in ExtraspecialNormalizerEquality, retaining the Sylow mark as well.
No Data, point normality, or local recognition premise is used. This proves
assertion (!!) of 14.5.20 in the original three-lift situation; the remaining
solvable exclusions and residual classification are separate obligations.

Source: Aschbacher–Smith, 14.5.20, printed p.1019; 14.7.9 and 14.7.27,
printed pp.1045,1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open BinaryLinear.OuterCyclic
universe u
section Model
variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)
private noncomputable def ThreeCoreContainment_modelMap (e : (L ⧸ pCore 2 L) ≃* SL) : L →* SL :=
  e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

private noncomputable def ThreeCoreContainment_modelAction (e : (L ⧸ pCore 2 L) ≃* SL) :
    normalizer (L : Set G) →* MulAut SL :=
  (MulAut.congr e).toMonoidHom.comp ((quotientAut (pCore 2 L)).comp L.normalizerMonoidHom)

omit [Finite G] in
private theorem ThreeCoreContainment_modelAction_apply (e : (L ⧸ pCore 2 L) ≃* SL)
    (g : normalizer (L : Set G)) (l : L) :
    ThreeCoreContainment_modelAction L e g (ThreeCoreContainment_modelMap L e l) = ThreeCoreContainment_modelMap L e (L.normalizerMonoidHom g l) := by
  change e (quotientAut (pCore 2 L) (L.normalizerMonoidHom g)
    (e.symm (e (QuotientGroup.mk' (pCore 2 L) l)))) = _
  rw [e.symm_apply_apply, quotientAut_apply_mk]
  rfl

omit [Finite G] in
private theorem ThreeCoreContainment_modelAction_inner (e : (L ⧸ pCore 2 L) ≃* SL) (l : L) :
    ThreeCoreContainment_modelAction L e ⟨l,L.le_normalizer l.property⟩ = MulAut.conj (ThreeCoreContainment_modelMap L e l) := by
  apply MulEquiv.ext
  intro y
  obtain ⟨a,rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) y
  change ThreeCoreContainment_modelAction L e ⟨l,L.le_normalizer l.property⟩ (ThreeCoreContainment_modelMap L e a) =
    MulAut.conj (ThreeCoreContainment_modelMap L e l) (ThreeCoreContainment_modelMap L e a)
  rw [ThreeCoreContainment_modelAction_apply]
  change ThreeCoreContainment_modelMap L e (l * a * l⁻¹) = ThreeCoreContainment_modelMap L e l * ThreeCoreContainment_modelMap L e a * (ThreeCoreContainment_modelMap L e l)⁻¹
  rw [map_mul,map_mul,map_inv]

omit [Finite G] in
private theorem ThreeCoreContainment_modelAction_image (e : (L ⧸ pCore 2 L) ≃* SL)
    (A : Subgroup G) (hAL : A ≤ L) :
    (A.subgroupOf (normalizer (L : Set G))).map (ThreeCoreContainment_modelAction L e) =
      ((A.subgroupOf L).map (ThreeCoreContainment_modelMap L e)).map MulAut.conj := by
  ext α
  constructor
  · rintro ⟨a,ha,rfl⟩
    refine ⟨ThreeCoreContainment_modelMap L e ⟨a,hAL ha⟩, ⟨⟨a,hAL ha⟩,ha,rfl⟩, ?_⟩
    exact (ThreeCoreContainment_modelAction_inner L e ⟨a,hAL ha⟩).symm
  · rintro ⟨_,⟨a,ha,rfl⟩,rfl⟩
    exact ⟨⟨a,L.le_normalizer a.property⟩,ha,ThreeCoreContainment_modelAction_inner L e a⟩

omit [Finite G] in
private theorem ThreeCoreContainment_modelAction_preserves (e : (L ⧸ pCore 2 L) ≃* SL)
    (A : Subgroup G) (g : normalizer (L : Set G))
    (hA : (g : G) ∈ normalizer (A : Set G)) :
    ((A.subgroupOf L).map (ThreeCoreContainment_modelMap L e)).map (ThreeCoreContainment_modelAction L e g).toMonoidHom =
      (A.subgroupOf L).map (ThreeCoreContainment_modelMap L e) := by
  have hle : ((A.subgroupOf L).map (ThreeCoreContainment_modelMap L e)).map
      (ThreeCoreContainment_modelAction L e g).toMonoidHom ≤ (A.subgroupOf L).map (ThreeCoreContainment_modelMap L e) := by
    rintro _ ⟨_,⟨a,ha,rfl⟩,rfl⟩
    exact ⟨L.normalizerMonoidHom g a, (mem_normalizer_iff.mp hA a).mp ha,
      (ThreeCoreContainment_modelAction_apply L e g a).symm⟩
  apply eq_of_le_of_card_ge hle
  exact le_of_eq (card_map_of_injective (ThreeCoreContainment_modelAction L e g).injective).symm

end Model
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem ThreeCoreContainment_exists_L_sylow (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : CFSG.Quasithin.Chapter12.Section02.Structural1222At CFSG.KnownSimple.IsKnownSimple T) :
    ∃ S : Sylow 2 L, (S : Subgroup L) = (T : Subgroup G).subgroupOf L := by
  obtain ⟨S,hS⟩ := (T.subtype (le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G))).exists_map_subtype_eq_inf_of_normalizes
    (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
    (sup_le L.le_normalizer (h.sylow_normalizes_at structural))
  refine ⟨S, map_injective L.subtype_injective ?_⟩
  rw [hS,Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right,subgroupOf_map_subtype]

private theorem ThreeCoreContainment_point_residual_marking (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : CFSG.Quasithin.Chapter12.Section02.Structural1222At CFSG.KnownSimple.IsKnownSimple T) :
    ∃ (e : (L ⧸ pCore 2 L) ≃* SL) (P : Subgroup SL),
        (P = pointParabolicSL ∨ P = lineParabolicSL) ∧
        ((F.Li L 1).subgroupOf L).map (ThreeCoreContainment_modelMap L e) = residual P ∧
        ((T : Subgroup G).subgroupOf L).map (ThreeCoreContainment_modelMap L e) = borelSL := by
  let := h.chosen.elementary
  let e₀ := h.naturalMarking.quotientEquiv.trans (slEquivLinear 3).symm
  let f := ThreeCoreContainment_modelMap L e₀
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker = pCore 2 L :=
      (MonoidHom.ker_comp_of_injective _ _ e₀.injective).trans (QuotientGroup.ker_mk' _)
    rw [he]
    exact pCore_isPGroup
  let A₀ := (F.Li L 1).subgroupOf L
  let A := A₀.map f
  have hAL : F.Li L 1 ≤ L := (F.Li_le L 1).trans inf_le_left
  have hp₀ : IsPPerfect 2 A₀ := (show IsPPerfect 2 (F.Li L 1) from isPPerfect_embedded_pResidual 2 _).of_surjective
    (subgroupOfEquivOfLe hAL).symm.toMonoidHom (subgroupOfEquivOfLe hAL).symm.surjective
  have hp : IsPPerfect 2 A := hp₀.of_surjective (f.subgroupMap A₀) (f.subgroupMap_surjective A₀)
  have hqker : IsPGroup 2 (f.subgroupMap A₀).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  let eA := subgroupOfEquivOfLe hAL
  let eQ := QuotientGroup.congr (pCore 2 A₀) (pCore 2 (F.Li L 1)) eA (pCore_map_iso 2 eA)
  let eImage := MonoidHom.quotientPCoreEquivOfSurjective (f.subgroupMap A₀)
    (f.subgroupMap_surjective A₀) hqker
  have hc : Nat.card (A ⧸ pCore 2 A) = 3 :=
    (Nat.card_congr eImage.toEquiv).symm.trans
      ((Nat.card_congr eQ.toEquiv).trans (pointResidual_core_quotient_card h structural))
  obtain ⟨S,hS⟩ := ThreeCoreContainment_exists_L_sylow h structural
  let R := S.mapSurjective (f := f) (e₀.surjective.comp (QuotientGroup.mk'_surjective _))
  have hn₀ : (S : Subgroup L) ≤ normalizer (A₀ : Set L) := by
    rw [hS]
    intro x hx
    apply mem_normalizer_iff.mpr
    intro a
    exact (mem_normalizer_iff.mp (ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes_at structural) hx) a)
  have hn : (R : Subgroup SL) ≤ normalizer (A : Set SL) :=
    (map_mono hn₀).trans (le_normalizer_map f)
  obtain ⟨_,_,_,_,g,P,hP,_,hmark,hborel,_⟩ := ResidualRecognition.recognize A R hp hc hn
  refine ⟨e₀.trans (MulAut.conj g),P,hP,?_⟩
  constructor
  · change A₀.map ((MulAut.conj g).toMonoidHom.comp f) = residual P
    rw [← map_map]
    exact hmark
  · change ((T : Subgroup G).subgroupOf L).map
      ((MulAut.conj g).toMonoidHom.comp f) = borelSL
    rw [← map_map,← hS]
    exact hborel


/-- A strict normalizer intersection in a normal three-lift forces the
original point residual into that lift. -/
theorem local_three_lift_contains_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (Y : Subgroup J) [Y.Normal]
    (h3 : IsPGroup 3 (Y ⧸ pCore 2 Y))
    (hi : (Y.map J.subtype).pCoreIn 2 < Y.map J.subtype ⊓ normalizer (L : Set G)) :
    (F.Li L 1).subgroupOf J ≤ Y := by
  let M := normalizer (L : Set G)
  let A := F.Li L 1
  let B := Y.map J.subtype
  let I := B ⊓ M
  let R := (pResidual 2 I).map I.subtype
  let S := (T : Subgroup G) ⊓ L
  have hAL : A ≤ L := (F.Li_le L 1).trans inf_le_left
  have hAM : A ≤ M := hAL.trans L.le_normalizer
  have hAJ : A ≤ J := F.Li_one_le_of_mem_Hz hJ
  have hTJ : (T : Subgroup G) ≤ J := F.sylow_le_of_mem_Hz hJ
  have hTM : (T : Subgroup G) ≤ M := h.sylow_normalizes_at structural
  have hRM : R ≤ M := (map_subtype_le _).trans inf_le_right
  have hRB : R ≤ B := (map_subtype_le _).trans inf_le_left
  have hRH : R ≤ F.H := hRB.trans ((map_subtype_le Y).trans hJ.2.1)
  have hJY : J ≤ normalizer (B : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      Y.le_normalizer_map J.subtype
  have hNR : J ⊓ M ≤ normalizer (R : Set G) :=
    ((le_inf (inf_le_left.trans hJY) (inf_le_right.trans M.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf).trans
        (normalizer_le_normalizer_characteristic_image I (pResidual 2 I))
  have hRA : R ≤ normalizer (A : Set G) := by
    have hh := ((le_inf hRM (hRH.trans F.H.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf).trans
        (normalizer_le_normalizer_characteristic_image (L ⊓ F.H)
          (pResidual 2 (L ⊓ F.H : Subgroup G)))
    have he : A = (pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype := by
      simp only [A,InvariantFlag.Li,show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) by decide,if_false]
      rfl
    rw [he]
    exact hh
  obtain ⟨e,P,hP,hm,hs⟩ := ThreeCoreContainment_point_residual_marking (F := F) h structural
  let q := ThreeCoreContainment_modelMap L e
  let f := ThreeCoreContainment_modelAction L e
  let R₀ := R.subgroupOf M
  let A₀ := A.subgroupOf M
  let S₀ := S.subgroupOf M
  let X := R₀.map f
  have hpR : IsPPerfect 2 R₀ := (isPPerfect_embedded_pResidual 2 I).of_surjective
    (subgroupOfEquivOfLe hRM).symm.toMonoidHom (subgroupOfEquivOfLe hRM).symm.surjective
  have hpX : IsPPerfect 2 X := hpR.of_surjective (f.subgroupMap R₀)
    (f.subgroupMap_surjective R₀)
  have hXne : X ≠ ⊥ := by
    intro hz
    obtain ⟨x,hx⟩ := local_three_intersection_quotient_action h structural J hJ Y h3 hi
    have hh : f (inclusion hRM x) = 1 := mem_bot.mp (hz ▸
      mem_map_of_mem f (show inclusion hRM x ∈ R₀ from x.property))
    apply hx
    apply (MulAut.congr e).injective
    exact hh.trans (map_one (MulAut.congr e)).symm
  have hXP : X ≤ P.map MulAut.conj := by
    rintro _ ⟨x,hx,rfl⟩
    have hh := ThreeCoreContainment_modelAction_preserves L e A x (hRA hx)
    change ((A.subgroupOf L).map q).map (f x).toMonoidHom = _ at hh
    rw [hm] at hh
    obtain ⟨g,hg,he⟩ := preserving_residual_is_conj P hP (f x) hh
    exact ⟨g,hg,he.symm⟩
  have hAim : A₀.map f = (residual P).map MulAut.conj := by
    rw [ThreeCoreContainment_modelAction_image L e A hAL,hm]
  have hn₀ : A₀ ≤ normalizer (R₀ : Set M) := by
    rw [←subgroupOf_normalizer_eq hRM]
    intro x hx
    exact hNR ⟨hAJ hx,hAM hx⟩
  have hXeq : X = (residual P).map MulAut.conj :=
    twoPerfect_normalized_parabolic_image P hP X hpX hXne hXP
      (hAim ▸ (map_mono hn₀).trans (le_normalizer_map f))
  have hSL : S ≤ L := inf_le_right
  have hSM : S ≤ M := hSL.trans L.le_normalizer
  have hSim : S₀.map f = borelSL.map MulAut.conj := by
    rw [ThreeCoreContainment_modelAction_image L e S hSL]
    have hS : S.subgroupOf L = (T : Subgroup G).subgroupOf L := by
      ext x
      exact and_iff_left x.property
    rw [hS,hs]
  have hc : ⁅residual P,borelSL⁆ = residual P := by
    let B₂ : Sylow 2 SL := Sylow.ofCard borelSL (by rw [card_borelSL,card_SL]; decide +kernel)
    have hcard : Nat.card (residual P ⧸ pCore 2 (residual P)) = 3 := by
      rcases hP with rfl | rfl
      · rw [MarkedAutomorphisms.point_residual]
        exact card_point_core_quotient
      · rw [MarkedAutomorphisms.line_residual]
        exact card_line_core_quotient
    have hBP : borelSL ≤ P := by
      rcases hP with rfl | rfl
      · exact inf_le_left
      · exact inf_le_right
    exact ResidualRecognition.commutator_sylow_eq (residual P) B₂
      (isPPerfect_embedded_pResidual 2 P) hcard
      ((hBP.trans P.le_normalizer).trans
        (normalizer_le_normalizer_characteristic_image P (pResidual 2 P)))
  have hcomm : (⁅R₀,S₀⁆).map f = A₀.map f := by
    rw [map_commutator]
    change ⁅X,S₀.map f⁆ = A₀.map f
    rw [hXeq,hSim,←map_commutator,hc,hAim]
  let C₀ := ⁅R₀,S₀⁆
  let C := C₀.map M.subtype
  have hC : C = ⁅R,S⁆ := by
    change (⁅R.subgroupOf M,S.subgroupOf M⁆).map M.subtype = _
    rw [map_commutator,map_subgroupOf_eq_of_le hRM,map_subgroupOf_eq_of_le hSM]
  have hCL : C ≤ L := by
    rw [hC]
    exact (commutator_mono le_rfl hSL).trans
      (le_normalizer_iff_commutator_le_right.mp hRM)
  have hCB : C ≤ B := by
    rw [hC]
    exact (commutator_mono hRB le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp ((inf_le_left : S ≤ (T : Subgroup G)).trans
        (hTJ.trans hJY)))
  have hCim : (C.subgroupOf L).map q = (A.subgroupOf L).map q := by
    apply Subgroup.map_injective (f := MulAut.conj) conj_injective
    rw [←ThreeCoreContainment_modelAction_image L e C hCL,←ThreeCoreContainment_modelAction_image L e A hAL]
    have hC₀ : C.subgroupOf M = C₀ :=
      comap_map_eq_self_of_injective M.subtype_injective C₀
    rw [hC₀]
    exact hcomm
  have hpA : IsPPerfect 2 (A.subgroupOf L) :=
    (show IsPPerfect 2 A from isPPerfect_embedded_pResidual 2 (L ⊓ F.H)).of_surjective
      (subgroupOfEquivOfLe hAL).symm.toMonoidHom (subgroupOfEquivOfLe hAL).symm.surjective
  have hqker : q.ker = pCore 2 L :=
    (MonoidHom.ker_comp_of_injective _ _ e.injective).trans (QuotientGroup.ker_mk' _)
  have hkn : q.ker ≤ normalizer (B.subgroupOf L : Set L) := by
    apply le_normalizer_iff.mpr
    intro k hk b hb
    have hkJ : (k : G) ∈ J := hTJ (InvariantFlag.localKernel_L_core_le_T L hTM
      (mem_map_of_mem L.subtype (hqker ▸ hk)))
    exact (mem_normalizer_iff.mp (hJY hkJ) b).mp hb
  have hAB : A.subgroupOf L ≤ B.subgroupOf L :=
    isPPerfect_le_of_map_le_of_kernel_normalizes q _ _ hpA
      (hqker ▸ pCore_isPGroup) hkn
      (hCim ▸ map_mono (subgroupOf_mono L hCB))
  intro a ha
  have hb : (a : G) ∈ B := hAB (show (⟨a,hAL ha⟩ : L) ∈ A.subgroupOf L from ha)
  exact (mem_map_iff_mem J.subtype_injective).mp hb

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The original point in the selected normal three-core lifts

A normal two-perfect cubic lift with strict normalizer intersection is
exactly L₁: point containment gives one inclusion, and the identical cubic
star images give the other through the full two-core, which normalizes L₁.

For a minimal solvable local J, the marked Heisenberg center lift Z and
L₁T generate a proper subgroup. Their two cubic images and a two-group
cannot generate a group whose three-core contains the marked order-27
subgroup. Minimality therefore places Z in N_G(L). Applying the cubic
result identifies Z with L₁, proving relative normality in J and the exact
center-image identity. Both quotient kernels are retained.

The final theorem applies the containment and center arguments to the
original selected minimal witness. The elementary-nine and Heisenberg
terminal exclusions, component reductions, and full 14.7.52 alternatives
remain required; these statements do not assert their completion.

Source: Aschbacher–Smith, 14.5.20 assertions (!!) and the center-lift step,
printed p.1019; 14.7.9 and 14.7.27, printed pp.1045,1054–1055,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- A normal two-perfect cubic lift with strict normalizer intersection is
exactly the original point residual, with the whole star kernel retained. -/
theorem local_solvable_normal_cubic_lift_eq_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (Y : Subgroup J) [Y.Normal] (hp : IsPPerfect 2 Y)
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 3)
    (hi : (Y.map J.subtype).pCoreIn 2 < Y.map J.subtype ⊓ normalizer (L : Set G)) :
    Y = (F.Li L 1).subgroupOf J := by
  let q := QuotientGroup.mk' (pCore 2 J)
  let A := (F.Li L 1).subgroupOf J
  have hAY := local_three_lift_contains_point h structural J hJ Y
    (IsPGroup.of_card (n := 1) (by simpa using hc)) hi
  have hY : Nat.card (Y.map q) = 3 :=
    (Nat.card_congr (coreQuotientEquivImage 2 Y).toEquiv).symm.trans hc
  have hA : Nat.card (A.map q) = 3 :=
    (local_solvable_point_kernel h hab structural previous faithful J hJ hs).2
  have he : A.map q = Y.map q := eq_of_le_of_card_ge (map_mono hAY) (by rw [hA,hY])
  have hn : q.ker ≤ normalizer (A : Set J) := by
    rw [QuotientGroup.ker_mk']
    let S := T.subtype (F.sylow_le_of_mem_Hz hJ)
    apply (pCore_isPGroup.le_sylow_of_normal S).trans
    rw [←subgroupOf_normalizer_eq (F.Li_one_le_of_mem_Hz hJ)]
    intro x hx
    exact T_normalizes_L₁_at h structural hx
  exact le_antisymm
    (isPPerfect_le_of_map_le_of_kernel_normalizes q Y A hp
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) hn he.ge) hAY

private theorem ThreeCoreCenter_cubic_pair_join_ne_top
    {D : Type*} [Group D] [Finite D]
    (X B C S : Subgroup D) (hX : 9 < Nat.card X) (hXP : X ≤ pCore 3 D)
    (hB : Nat.card B = 3) (hC : Nat.card C = 3)
    (hBC : B ≤ normalizer (C : Set D)) (hS : IsPGroup 2 S)
    (hSB : S ≤ normalizer (B : Set D)) (hSC : S ≤ normalizer (C : Set D)) :
    C ⊔ B ⊔ S ≠ ⊤ := by
  intro he
  let A := C ⊔ B
  have hSA : S ≤ normalizer (A : Set D) :=
    (le_inf hSC hSB).trans (normalizer_inf_normalizer_le_normalizer_sup C B)
  let : A.Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [←he]
    exact sup_le A.le_normalizer hSA))
  have hquot : IsPGroup 2 (D ⧸ A) := isPGroup_quotient_of_sup_eq_top A S hS he
  have hPA : pCore 3 D ≤ A := by
    let q := QuotientGroup.mk' A
    have hz : (pCore 3 D).map q = ⊥ := by
      have hd := ((pCore_isPGroup (p := 3) (G := D)).map q).disjoint_of_coprime
        (hquot.to_subgroup ⊤) (by decide : Nat.Coprime 3 2)
      simpa using hd.eq_bot
    simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hz
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes C B hBC
  have hpos := Nat.card_pos (α := (C ⊓ B : Subgroup D))
  have hle : Nat.card A ≤ 9 := by
    change Nat.card (C ⊔ B : Subgroup D) ≤ 9
    rw [hC,hB] at hc
    nlinarith
  exact (not_le_of_gt hX) ((card_le_of_le (hXP.trans hPA)).trans hle)

/-- In a minimal original solvable local, the selected Heisenberg center
lift equals L₁. In particular its actual star image is the center and L₁
is normal in the whole original local, without a point-normality premise. -/
theorem local_minimal_solvable_heisenberg_center_eq_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (hmin : ∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < J →
      D ≤ normalizer (L : Set G))
    (X : Subgroup (pCore 3 (HStar J))) (hX : IsSupercriticalPSubgroup 3 X)
    (e : X ≃* HeisenbergPrime 3) (Y : Subgroup J) [Y.Normal]
    (hm : Y.map (QuotientGroup.mk' (pCore 2 J)) = X.map (pCore 3 (HStar J)).subtype) :
    ((F.Li L 1).subgroupOf J).Normal ∧
    ((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) =
      ((center X).map X.subtype).map (pCore 3 (HStar J)).subtype ∧
    ∃ Z : Subgroup J, Z = (F.Li L 1).subgroupOf J ∧ Z < Y ∧
      Z.Normal ∧ IsPPerfect 2 Z ∧
      ((QuotientGroup.mk' (pCore 2 J)).comp Z.subtype).ker = pCore 2 Z ∧
      Nat.card (Z ⧸ pCore 2 Z) = 3 ∧ Nonempty ((Z ⧸ pCore 2 Z) ≃* center X) ∧
      pCore 2 Z ≠ ⊥ := by
  obtain ⟨Z,hZY,hZn,hZp,hZm,hZk,hZc,hZe,hZQ,_⟩ :=
    local_solvable_heisenberg_center_lift h structural J hJ X hX e Y hm
  let := hZn
  let q := QuotientGroup.mk' (pCore 2 J)
  let A := (F.Li L 1).subgroupOf J
  let S := T.subtype (F.sylow_le_of_mem_Hz hJ)
  have hSA : (S : Subgroup J) ≤ normalizer (A : Set J) := by
    rw [←subgroupOf_normalizer_eq (F.Li_one_le_of_mem_Hz hJ)]
    intro x hx
    exact T_normalizes_L₁_at h structural hx
  have hXc : 9 < Nat.card (X.map (pCore 3 (HStar J)).subtype) := by
    rw [card_map_of_injective (pCore 3 (HStar J)).subtype_injective,
      Nat.card_congr e.toEquiv,HeisenbergPrime.card]
    decide
  have hZim : Nat.card (Z.map q) = 3 :=
    (Nat.card_congr (coreQuotientEquivImage 2 Z).toEquiv).symm.trans hZc
  let : (Z.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hne := ThreeCoreCenter_cubic_pair_join_ne_top (X.map (pCore 3 (HStar J)).subtype)
    (A.map q) (Z.map q) ((S : Subgroup J).map q) hXc (map_subtype_le X)
    (local_solvable_point_kernel h hab structural previous faithful J hJ hs).2 hZim
    le_normalizer_of_normal (S.isPGroup'.map q)
    ((map_mono hSA).trans (le_normalizer_map q)) le_normalizer_of_normal
  let D := Z ⊔ A ⊔ (S : Subgroup J)
  have hDne : D ≠ ⊤ := by
    intro he
    apply hne
    rw [←Subgroup.map_sup,←Subgroup.map_sup,show Z ⊔ A ⊔ (S : Subgroup J) = D from rfl,he,
      map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  have hDlt : D.map J.subtype < J :=
    lt_of_le_of_ne (map_subtype_le D) (fun he => hDne
      (map_injective J.subtype_injective (by
        simpa only [←MonoidHom.range_eq_map,range_subtype] using he)))
  have hDmap : D.map J.subtype = Z.map J.subtype ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) := by
    rw [show D = Z ⊔ A ⊔ (S : Subgroup J) from rfl,Subgroup.map_sup,Subgroup.map_sup,
      map_subgroupOf_eq_of_le (F.Li_one_le_of_mem_Hz hJ),Sylow.coe_subtype,
      map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hJ),sup_assoc]
  have hZM : Z.map J.subtype ≤ normalizer (L : Set G) :=
    (hDmap ▸ le_sup_left).trans (hmin _ (hDmap ▸ le_sup_right) hDlt)
  have hi := local_lift_intersection_of_cubic_sublift h structural J hJ Z Z le_rfl hZM hZk hZc
  have heq := local_solvable_normal_cubic_lift_eq_point h hab structural previous faithful
    J hJ hs Z hZp hZc hi
  exact ⟨heq ▸ hZn,heq ▸ hZm,Z,heq,hZY,hZn,hZp,hZk,hZc,hZe,hZQ⟩

/-- The original solvable witness now has point containment in every
selected normal lift. In the Heisenberg branch the same point is normal
in the whole minimal local and is exactly the marked residual center. -/
theorem local_minimal_solvable_threeCore_point_and_center
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ∃ (I : Subgroup G), I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      Group.IsSolvable I ∧
      (∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < I →
        D ≤ normalizer (L : Set G)) ∧
    ∃ (X : Subgroup (pCore 3 (HStar I))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup I),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 I ∧
      Y.map (QuotientGroup.mk' (pCore 2 I)) = X.map (pCore 3 (HStar I)).subtype ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
      (F.Li L 1).subgroupOf I ≤ Y ∧
      (Y.map I.subtype).pCoreIn 2 < Y.map I.subtype ⊓ normalizer (L : Set G) ∧
      ((Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∧
          pResidual 2 (HStar I) = pCore 3 (HStar I)) ∨
        (Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3) ∧
          ((F.Li L 1).subgroupOf I).Normal ∧
          ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) =
            ((center X).map X.subtype).map (pCore 3 (HStar I)).subtype)) := by
  obtain ⟨I,hIJ,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,_,hi,he⟩ :=
    local_minimal_solvable_threeCore_reduction h hab structural previous faithful J hJ hs
  let := hYn
  let eX : (Y ⧸ pCore 2 Y) ≃* X := (coreQuotientEquivImage 2 Y).trans
    ((MulEquiv.subgroupCongr hm).trans
      (equivMapOfInjective X (pCore 3 (HStar I)).subtype
        (pCore 3 (HStar I)).subtype_injective).symm)
  have h3 : IsPGroup 3 (Y ⧸ pCore 2 Y) :=
    ((pCore_isPGroup (p := 3) (G := HStar I)).to_subgroup X).of_equiv eX.symm
  refine ⟨I,hIJ,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,
    local_three_lift_contains_point h structural I hI Y h3 hi,hi,?_⟩
  rcases he with he | ⟨he,_,_⟩
  · exact Or.inl he
  · obtain ⟨hn,hcenter,_⟩ := local_minimal_solvable_heisenberg_center_eq_point
      h hab structural previous faithful I hI hIs hmin X hX (eX.symm.trans he.some) Y hm
    exact Or.inr ⟨he,hn,hcenter⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Plane geometry in the original solvable locals

The normal elementary-nine lift normalizes the original point residual:
its abelian star image centralizes the point image, and two-perfectness
reflects normalization through the whole two-core kernel, which lies in T.
This gives relative normalization by the selected lift, without imposing
point normality in the full point normalizer.

For every original solvable J in H_z, its established cubic point image
has trivial two-core. If O₂(J) fixed V₂, reductions 13.3.14(a,c) would
force that image to have a nontrivial two-core, since the original point
parabolic core moves V. Hence O₂(J) moves V₂. The plane-parabolic core
fixes V₂ and has index two in T, so the two literal cores generate T.
An actor normalizing both L₁ and V₂ preserves V and therefore lies in M.

The final theorem applies these arguments to the original minimal solvable
witness, preserving the supercritical models, exact kernels, point containment
and Heisenberg center marking. The terminal solvable exclusions and the
classification through 14.7.52 remain to be proved.

Source: Aschbacher–Smith, 13.3.14(a,c), printed pp.891–892;
14.5.3(2) and 14.5.20, pp.1013,1019; 14.7.27–29, pp.1054–1055,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- A normal elementary-nine lift containing L₁ normalizes L₁ through the
full two-core kernel. No normality in the whole point normalizer is assumed. -/
theorem local_nine_lift_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (Y : Subgroup J) [Y.Normal]
    (hAY : (F.Li L 1).subgroupOf J ≤ Y)
    (e : (Y ⧸ pCore 2 Y) ≃*
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) :
    Y.map J.subtype ≤ normalizer (F.Li L 1 : Set G) := by
  let A := (F.Li L 1).subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  let E := (coreQuotientEquivImage 2 Y).symm.trans e
  let : IsMulCommutative (Y.map q) := IsMulCommutative.of_comm fun a b =>
    E.injective (by simp only [map_mul,mul_comm])
  have hp : IsPPerfect 2 A := by
    exact (show IsPPerfect 2 (F.Li L 1) from isPPerfect_embedded_pResidual 2 _).of_surjective
      (subgroupOfEquivOfLe (F.Li_one_le_of_mem_Hz hJ)).symm.toMonoidHom
      (subgroupOfEquivOfLe (F.Li_one_le_of_mem_Hz hJ)).symm.surjective
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hkn : q.ker ≤ normalizer (A : Set J) := by
    rw [QuotientGroup.ker_mk']
    apply (pCore_isPGroup.le_sylow_of_normal (T.subtype (F.sylow_le_of_mem_Hz hJ))).trans
    rw [←subgroupOf_normalizer_eq (F.Li_one_le_of_mem_Hz hJ)]
    exact fun _ hx => T_normalizes_L₁_at h structural hx
  have hn : Y ≤ normalizer (A : Set J) :=
    (map_le_normalizer_map_iff_of_pPerfect q A Y hp hk hkn).mp
      ((le_centralizer (Y.map q)).trans
        ((centralizer_le (map_mono hAY)).trans (Subgroup.centralizer_le_normalizer _)))
  rw [←subgroupOf_normalizer_eq (F.Li_one_le_of_mem_Hz hJ)] at hn
  rintro _ ⟨y,hy,rfl⟩
  exact hn hy

/-- The literal core of every original solvable local moves the flag plane,
using its cubic point image and the earlier natural point-core movement. -/
theorem local_solvable_core_moves_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ¬ J.pCoreIn 2 ≤ centralizer (F.Vi 2 : Set G) := by
  intro hc
  let := h.chosen.elementary
  let := IsElementaryAbelian.of_le (p := 2) (F.le_seed 2)
  let := F.localKernel_tilde_seed_elementary
  have hVJ : V ≤ J := h.chosen.le_sylow.trans (F.sylow_le_of_mem_Hz hJ)
  have hLJ := F.Li_one_le_of_mem_Hz hJ
  have hspan : V = conjugateSpanBy (F.Vi 2) (F.Li L 1) :=
    (F.seed_eq_plane_span L (by decide) h.chosen.normalizes
      (F.invariant_subgroup_of_ambient_natural h.naturalMarking (by decide))).symm
  have ha := Chapter13.Section03.Noncentrality.reduction_a
    (F.Vi 2) V (F.Li L 1) J ((F.le_seed 2).trans hVJ) hLJ hspan
    (Chapter1.mem_He_iff.mpr
      (F.localKernel_characteristicTwo h.source.simpleQTKE L _ J hJ))
    (by rw [commutator_comm]; exact commutator_eq_bot_iff_le_centralizer.mpr hc)
  have hne := Chapter13.Section03.Noncentrality.reduction_c_of_reduction_a
    J (F.Li L 1) V hLJ ha.2 (F.point_core_moves_seed_of_natural h.naturalMarking)
  have he : Chapter13.Section03.Noncentrality.star J (F.Li L 1) hLJ =
      ((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) := by
    simp only [Chapter13.Section03.Noncentrality.star,
      Chapter13.Section03.Noncentrality.starMap,MonoidHom.range_comp,inclusion_range]
  rw [he] at hne
  have hp : IsPGroup 3 (((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) :=
    IsPGroup.of_card (n := 1)
      (by simpa using (local_solvable_point_kernel h hab structural previous faithful J hJ hs).2)
  apply hne
  exact le_bot_iff.mp ((le_inf le_rfl le_top).trans
    (pCore_isPGroup.disjoint_of_coprime (hp.to_subgroup ⊤)
      (by decide : Nat.Coprime 2 3)).le_bot)

private theorem SolvableGeometry_local_plane_core_sylow_index
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    ((F.P L).pCoreIn 2).relIndex (T : Subgroup G) = 2 := by
  let P := F.P L
  let S := T.subtype (F.binary_sylow_le_P L)
  let e := planeParabolicQuotientEquiv (F := F) h structural
  have hi := relIndex_mul_index (pCore_isPGroup.le_sylow_of_normal S)
  rw [SymmetricThreeTwoCore.core_index e,SymmetricThreeTwoCore.sylow_index_three e S] at hi
  have hi2 : (pCore 2 P).relIndex (S : Subgroup P) = 2 := by
    dsimp only [P]
    omega
  have he := relIndex_map_map_of_injective (pCore 2 P) (S : Subgroup P) P.subtype_injective
  rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le (F.binary_sylow_le_P L)] at he
  exact he.trans hi2

/-- The core of an original solvable local and the plane-parabolic core
generate the original Sylow subgroup. -/
theorem local_solvable_core_plane_core_generate_sylow
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    J.pCoreIn 2 ⊔ (F.P L).pCoreIn 2 = (T : Subgroup G) := by
  let := h.chosen.elementary
  let A := J.pCoreIn 2
  let B := (F.P L).pCoreIn 2
  have hAT : A ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow J (T.subtype (F.sylow_le_of_mem_Hz hJ))
    exact hh.trans_eq (map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hJ))
  have hBT : B ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow (F.P L) (T.subtype (F.binary_sylow_le_P L))
    exact hh.trans_eq (map_subgroupOf_eq_of_le (F.binary_sylow_le_P L))
  have hBC : B ≤ centralizer (F.Vi 2 : Set G) := by
    change (F.P L).pCoreIn 2 ≤ centralizer (F.Vi 2 : Set G)
    rw [←(F.binary_parabolic_core (by decide) L h.chosen.normalizes
      (h.full_LT_action_at structural) (h.centralizer_LT_at structural)).1]
    exact inf_le_right
  have hnot : ¬ A ≤ B := fun hh =>
    local_solvable_core_moves_plane h hab structural previous faithful J hJ hs (hh.trans hBC)
  have hi : B.relIndex (T : Subgroup G) = 2 := SolvableGeometry_local_plane_core_sylow_index h structural
  have hjoin := sup_le hAT hBT
  have hd : (A ⊔ B).relIndex (T : Subgroup G) ∣ 2 := by
    have hd := relIndex_dvd_of_le_left (T : Subgroup G) (show B ≤ A ⊔ B from le_sup_right)
    rwa [hi] at hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · exact le_antisymm hjoin (relIndex_eq_one.mp h1)
  · have hh := relIndex_mul_relIndex B (A ⊔ B) (T : Subgroup G) le_sup_right hjoin
    rw [hi,h2] at hh
    have h1 : B.relIndex (A ⊔ B) = 1 := by omega
    exact (hnot (le_sup_left.trans (relIndex_eq_one.mp h1))).elim

/-- Preserving the original point residual and plane forces preservation of
the original natural seed, hence containment in its maximal local M. -/
theorem local_point_plane_normalizer_le
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (A : Subgroup G) (hn : A ≤ normalizer (F.Li L 1 : Set G))
    (hc : A ≤ normalizer (F.Vi 2 : Set G)) :
    A ≤ normalizer (L : Set G) :=
  point_plane_normalizer_le h structural A hn hc

/-- The original minimal solvable witness has lift normalization and
plane-core generation with both actual models and full kernels retained. -/
theorem local_minimal_solvable_threeCore_geometry
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ∃ (I : Subgroup G), I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      Group.IsSolvable I ∧
      (∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < I →
        D ≤ normalizer (L : Set G)) ∧
      ¬ I.pCoreIn 2 ≤ centralizer (F.Vi 2 : Set G) ∧
      I.pCoreIn 2 ⊔ (F.P L).pCoreIn 2 = (T : Subgroup G) ∧
    ∃ (X : Subgroup (pCore 3 (HStar I))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup I),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 I ∧
      Y.map (QuotientGroup.mk' (pCore 2 I)) = X.map (pCore 3 (HStar I)).subtype ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
      (F.Li L 1).subgroupOf I ≤ Y ∧
      (Y.map I.subtype).pCoreIn 2 < Y.map I.subtype ⊓ normalizer (L : Set G) ∧
      Y.map I.subtype ≤ normalizer (F.Li L 1 : Set G) ∧
      Y.map I.subtype ⊓ normalizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G) ∧
      ((Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∧
          pResidual 2 (HStar I) = pCore 3 (HStar I)) ∨
        (Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3) ∧
          ((F.Li L 1).subgroupOf I).Normal ∧
          ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) =
            ((center X).map X.subtype).map (pCore 3 (HStar I)).subtype)) := by
  obtain ⟨I,hIJ,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,hAY,hi,he⟩ :=
    local_minimal_solvable_threeCore_point_and_center h hab structural previous faithful J hJ hs
  let := hYn
  have hn : Y.map I.subtype ≤ normalizer (F.Li L 1 : Set G) := by
    rcases he with ⟨he,_⟩ | ⟨_,hn,_⟩
    · exact local_nine_lift_normalizes_point h structural I hI Y hAY he.some
    · exact (map_subtype_le Y).trans ((normal_subgroupOf_iff_le_normalizer
        (F.Li_one_le_of_mem_Hz hI)).mp hn)
  exact ⟨I,hIJ,hI,hIs,hmin,
    local_solvable_core_moves_plane h hab structural previous faithful I hI hIs,
    local_solvable_core_plane_core_generate_sylow h hab structural previous faithful I hI hIs,
    X,hX,Y,hYn,hYp,hYr,hm,hk,hAY,hi,hn,
    local_point_plane_normalizer_le h structural _ (inf_le_left.trans hn) inf_le_right,he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Cubic containment inside the original solvable locals

The cubic completion and Heisenberg norm argument require only that the
selected subgroup normalize L₁. In a solvable J in H_z, the proved equality
O₂(J) O₂(P) = T replaces normality of L₁ in the full point normalizer.
The cubic actor normalizes both cores, hence T, contradicting its literal
S₃ quotient. Thus every such actor in J is contained in N_G(L).

The F.8 point-core obstruction supplies the S₃ quotient of every escaping
cubic actor. The final application discharges relative normalization for
every cubic sublift of the actual normal elementary-nine or Heisenberg lift.
It retains the original models and exact quotient kernels. The terminal solvable exclusions remain required.

Source: Aschbacher–Smith, 14.5.3(2), pp.1013–1017, and 14.7.27–29,
pp.1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Inside the point normalizer, an actor preserving both L₁ and T lies
in the seed normalizer: otherwise R₁ would be normal in an escaping local,
contrary to the original F.8 core obstruction. -/
theorem local_point_sylow_normalizer_le
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G))
    (hYT : Y ≤ normalizer (T : Set G)) :
    Y ≤ normalizer (L : Set G) := by
  by_contra hout
  let B := F.Li L 1 ⊔ (T : Subgroup G)
  let J := B ⊔ Y
  have hBJ : B ≤ J := le_sup_left
  have hJH : J ≤ F.H := sup_le
    (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)) hYH
  have hc : Nat.card (F.Vi 1) = 2 := F.card 1 (by decide)
  have hpoint : F.Vi 1 ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsPGroup.of_card (n := 1) (by simpa using hc))
    ((F.le_seed 1).trans (h.chosen.le_sylow.trans (le_sup_right.trans hBJ))) hJH
  have hcore : J.pCoreIn 2 ≠ ⊥ := by
    intro he
    have hz := le_bot_iff.mp (he ▸ hpoint)
    rw [hz,card_bot] at hc
    omega
  have hJ : J ∈ F.Hz L (normalizer (L : Set G)) :=
    ⟨⟨hcore,fun _ hx => hx.elim (fun ha => hBJ (mem_sup_left ha))
      (fun ha => hBJ (mem_sup_right ha))⟩,hJH,fun hh => hout (le_sup_right.trans hh)⟩
  have hYB : Y ≤ normalizer (B : Set G) :=
    (le_inf hYL hYT).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hJR : J ≤ normalizer (F.Ri L 1 : Set G) :=
    (sup_le B.le_normalizer hYB).trans
      (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  exact point_core_not_le_local_core_at h hab structural J hJ
    (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 B)
      ((pCoreIn_le 2 B).trans hBJ) hJR)

/-- An escaping cubic lift normalizing the point has the required literal S₃
Sylow quotient. The original core obstruction rules out trivial Sylow action. -/
theorem local_point_normalized_cubic_sylow_quotient
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G))
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 3)
    (hout : ¬ Y ≤ normalizer (L : Set G)) :
    Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) := by
  apply cubic_sylow_join_symmetricThree T Y hYT hc
  intro hm
  have hcore : Y.pCoreIn 2 ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 Y).le_sylow_of_normalized T
      (hYT.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y)))
  exact hout (local_point_sylow_normalizer_le h hab structural Y hYH hYL
    (le_normalizer_iff_commutator_le_right.mpr (hm.trans hcore)))

/-- Source cubic containment with normalization only by the selected actor
and the original solvable-local hypotheses. -/
private theorem SolvableCubicContainment_local_solvable_symmetricThree_containment
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (Y : Subgroup G) (hYJ : Y ≤ J)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    Y ≤ normalizer (L : Set G) := by
  by_contra hout
  have hYH : Y ≤ F.H := hYJ.trans hJ.2.1
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  have hYP : Y ≤ normalizer ((F.P L).pCoreIn 2 : Set G) := by
    rw [(cubic_generated_equal_two_cores_of_normalizes_point h hab structural previous faithful
      Y hYH hYL hYp hYT hout he).1]
    exact (show Y ≤ D from le_sup_left.trans le_sup_right).trans
      (D.le_normalizer.trans (normalizer_le_normalizer_characteristic_image D (pCore 2 D)))
  have hYJcore : Y ≤ normalizer (J.pCoreIn 2 : Set G) :=
    hYJ.trans (J.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))
  have hYTnorm : Y ≤ normalizer (T : Set G) := by
    change Y ≤ normalizer ((T : Subgroup G) : Set G)
    rw [←local_solvable_core_plane_core_generate_sylow h hab structural previous faithful J hJ hs]
    exact (le_inf hYJcore hYP).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  let B := Y ⊔ (T : Subgroup G)
  let S := T.subtype (show (T : Subgroup G) ≤ B from le_sup_right)
  have hBnorm : B ≤ normalizer (T : Set G) := sup_le hYTnorm (T : Subgroup G).le_normalizer
  have hSnorm : (S : Subgroup B).Normal := normal_subgroupOf_of_le_normalizer hBnorm
  have htop : (S : Subgroup B) = ⊤ := by
    rw [←SymmetricThreeTwoCore.sylow_self_normalizing he.some S]
    exact normalizer_eq_top_iff.mpr hSnorm
  have hi := SymmetricThreeTwoCore.sylow_index_three he.some S
  rw [htop,index_top] at hi
  omega

/-- Every T-invariant two-perfect cubic lift in a solvable local normalizing
L₁ lies in M. Its S₃ overgroup quotient is proved, not assumed. -/
theorem local_solvable_cubic_containment
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (Y : Subgroup G) (hYJ : Y ≤ J)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 3) :
    Y ≤ normalizer (L : Set G) := by
  by_contra hout
  have he := local_point_normalized_cubic_sylow_quotient h hab structural Y
    (hYJ.trans hJ.2.1) hYL hYT hc hout
  exact hout (SolvableCubicContainment_local_solvable_symmetricThree_containment h hab structural previous faithful
    J hJ hs Y hYJ hYL hYp hYT he)

/-- Every normalized cubic sublift of the original selected normal three-lift
is contained in the seed normalizer. The actor's
point normalization is derived from the actual lift and its marked models. -/
theorem local_minimal_solvable_threeCore_cubic_containment
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ∃ (I : Subgroup G), I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      Group.IsSolvable I ∧
      (∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < I →
        D ≤ normalizer (L : Set G)) ∧
    ∃ (X : Subgroup (pCore 3 (HStar I))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup I),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 I ∧
      Y.map (QuotientGroup.mk' (pCore 2 I)) = X.map (pCore 3 (HStar I)).subtype ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
      (F.Li L 1).subgroupOf I ≤ Y ∧
      (Y.map I.subtype).pCoreIn 2 < Y.map I.subtype ⊓ normalizer (L : Set G) ∧
      (∀ A : Subgroup G, A ≤ Y.map I.subtype → IsPPerfect 2 A →
        (T : Subgroup G) ≤ normalizer (A : Set G) →
        Nat.card (A ⧸ pCore 2 A) = 3 →
        A ≤ normalizer (L : Set G)) ∧
      ((Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∧
          pResidual 2 (HStar I) = pCore 3 (HStar I)) ∨
        (Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3) ∧
          ((F.Li L 1).subgroupOf I).Normal ∧
          ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) =
            ((center X).map X.subtype).map (pCore 3 (HStar I)).subtype)) := by
  obtain ⟨I,hIJ,hI,hIs,hmin,_,_,X,hX,Y,hYn,hYp,hYr,hm,hk,hAY,hi,hn,_,he⟩ :=
    local_minimal_solvable_threeCore_geometry h hab structural previous faithful J hJ hs
  refine ⟨I,hIJ,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,hAY,hi,?_,he⟩
  intro A hA hAp hAT hAe
  exact local_solvable_cubic_containment h hab structural previous faithful I hI hIs A
    (hA.trans (map_subtype_le Y)) (hA.trans hn) hAp hAT hAe

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Containment of the elementary-nine lift in the original solvable witness

The original point image is a Sylow-invariant cubic line of the normal
nine-group. A coprime complement and normalized residual lifts give two
cubic generators, each contained in the seed normalizer by the relative
cubic argument. Hence the entire normal lift lies there.

The application retains the original minimal witness, both quotient models,
the exact two-core kernels and the Heisenberg center marking. Containment
of the nine-lift is the intermediate step in 14.5.20; the subsequent
cyclic-nine enlargement and terminal solvable exclusion remain required.

Source: Aschbacher–Smith, 14.5.20, printed p.1019, and 14.7.27–29,
pp.1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- A normal elementary-nine two-perfect lift containing the actual point
residual is contained in the seed normalizer. -/
theorem local_solvable_nine_lift_containment
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) (Y : Subgroup J) [Y.Normal]
    (hYp : IsPPerfect 2 Y) (hAY : (F.Li L 1).subgroupOf J ≤ Y)
    (e : (Y ⧸ pCore 2 Y) ≃*
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) :
    Y.map J.subtype ≤ normalizer (L : Set G) := by
  let q := QuotientGroup.mk' (pCore 2 J)
  let eP := (coreQuotientEquivImage 2 Y).symm.trans e
  let : IsElementaryAbelian 3 (Y.map q) :=
    IsElementaryAbelian.of_injective eP.toMonoidHom eP.injective
  have hP : Nat.card (Y.map q) = 9 := by
    rw [Nat.card_congr eP.toEquiv,Nat.card_prod]
    norm_num [Nat.card_zmod]
  let S := T.subtype (F.sylow_le_of_mem_Hz hJ)
  let C := ((F.Li L 1).subgroupOf J).map q
  have hC : Nat.card C = 3 :=
    (local_solvable_point_kernel h hab structural previous faithful J hJ hs).2
  have hSC : (S : Subgroup J).map q ≤ normalizer (C : Set (HStar J)) := by
    apply (map_mono ?_).trans (le_normalizer_map q)
    rw [←subgroupOf_normalizer_eq (F.Li_one_le_of_mem_Hz hJ)]
    exact fun _ hx => T_normalizes_L₁_at h structural hx
  obtain ⟨A,B,hAB,⟨hAp,hAT,_,_,hAc⟩,⟨hBp,hBT,_,hBc⟩⟩ :=
    exists_cubic_lifts_of_normal_elementary_nine q (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
      Y hYp hP S S.isPGroup' C (map_mono hAY) hC hSC
  have hn := local_nine_lift_normalizes_point h structural J hJ Y hAY e
  have hcontain (A : Subgroup J) (hA : A ≤ Y) (hp : IsPPerfect 2 A)
      (hAT : (S : Subgroup J) ≤ normalizer (A : Set J))
      (hc : Nat.card (A ⧸ pCore 2 A) = 3) :
      A.map J.subtype ≤ normalizer (L : Set G) := by
    have hmap : IsPPerfect 2 (A.map J.subtype) := hp.of_surjective
      (J.subtype.subgroupMap A) (J.subtype.subgroupMap_surjective A)
    have hnorm : (T : Subgroup G) ≤ normalizer (A.map J.subtype : Set G) := by
      have hh := (map_mono hAT).trans (le_normalizer_map J.subtype)
      rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hJ)] at hh
    let eA := equivMapOfInjective A J.subtype J.subtype_injective
    have hcard : Nat.card ((A.map J.subtype) ⧸ pCore 2 (A.map J.subtype)) = 3 := by
      rw [←Nat.card_congr (QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).toEquiv]
      exact hc
    exact local_solvable_cubic_containment h hab structural previous faithful J hJ hs
      (A.map J.subtype) (map_subtype_le A) ((map_mono hA).trans hn) hmap hnorm hcard
  rw [←hAB,Subgroup.map_sup]
  exact sup_le (hcontain A (le_sup_left.trans_eq hAB) hAp hAT hAc)
    (hcontain B (le_sup_right.trans_eq hAB) hBp hBT hBc)

/-- On the original minimal solvable witness, the normal nine-lift is
contained in M; the Heisenberg branch retains its exact center marking. -/
theorem local_minimal_solvable_threeCore_nine_containment
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ∃ (I : Subgroup G), I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      Group.IsSolvable I ∧
      (∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < I →
        D ≤ normalizer (L : Set G)) ∧
    ∃ (X : Subgroup (pCore 3 (HStar I))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup I),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 I ∧
      Y.map (QuotientGroup.mk' (pCore 2 I)) = X.map (pCore 3 (HStar I)).subtype ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
      (F.Li L 1).subgroupOf I ≤ Y ∧
      (Y.map I.subtype).pCoreIn 2 < Y.map I.subtype ⊓ normalizer (L : Set G) ∧
      (∀ A : Subgroup G, A ≤ Y.map I.subtype → IsPPerfect 2 A →
        (T : Subgroup G) ≤ normalizer (A : Set G) →
        Nat.card (A ⧸ pCore 2 A) = 3 →
        A ≤ normalizer (L : Set G)) ∧
      ((Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∧
          pResidual 2 (HStar I) = pCore 3 (HStar I) ∧
          Y.map I.subtype ≤ normalizer (L : Set G)) ∨
        (Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3) ∧
          ((F.Li L 1).subgroupOf I).Normal ∧
          ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) =
            ((center X).map X.subtype).map (pCore 3 (HStar I)).subtype)) := by
  obtain ⟨I,hIJ,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,hAY,hi,hc,he⟩ :=
    local_minimal_solvable_threeCore_cubic_containment h hab structural previous faithful J hJ hs
  let := hYn
  refine ⟨I,hIJ,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,hAY,hi,hc,?_⟩
  rcases he with ⟨he,hr⟩ | he
  · exact Or.inl ⟨he,hr,local_solvable_nine_lift_containment h hab structural previous faithful
      I hI hIs Y hYp hAY he.some⟩
  · exact Or.inr he

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The moved cubic kernel line in the original normal nine-lift

The selected normal nine-lift lies in M = N_G(L). Its literal action on
L/O₂(L) is nontrivial by ambient normalizer control. Since Aut(L₃(2)) has
order 336, the action kernel has cubic image modulo the entire two-core.
Its two-residual C is T-invariant and centralizes L modulo O₂(L), so
N_G(C) lies in M and the escaping local J cannot normalize C.

The star map has kernel exactly O₂(C) on this lift. If the three-core
normalized its cubic image, the Sylow supplement and normalization by the
whole star-map kernel would lift normality to J, a contradiction. Hence
the actual three-core moves this cubic line, and in particular is nonabelian.
The last theorem applies this to the original minimal solvable witness,
preserving its normal nine-lift or Heisenberg center marking.

This supplies the moving-line input in the elementary-nine branch of
14.5.20. The cyclic-nine enlargement, terminal solvable exclusions and the
four final inputs through 14.7.52 remain to be proved.
Source: Aschbacher–Smith, 14.5.20, printed p.1019; 14.7.9 and
14.7.27–29, pp.1045,1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The actual quotient-centralizer residual of the normal nine-lift is
cubic and T-invariant, and its full ambient normalizer lies in M. -/
theorem local_solvable_nine_centralizing_lift
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) (Y : Subgroup J) [Y.Normal]
    (hYp : IsPPerfect 2 Y) (hAY : (F.Li L 1).subgroupOf J ≤ Y)
    (e : (Y ⧸ pCore 2 Y) ≃*
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) :
    let B := Y.map J.subtype
    let D := pCoreActionKernelIn 2 L B
    let C := (pResidual 2 D).map D.subtype
    C ≤ B ∧ IsPPerfect 2 C ∧ (T : Subgroup G) ≤ normalizer (C : Set G) ∧
      Nat.card (C ⧸ pCore 2 C) = 3 ∧
      ⁅L,C⁆ ≤ L.pCoreIn 2 ∧
      normalizer (C : Set G) ≤ normalizer (L : Set G) ∧
      ¬ J ≤ normalizer (C : Set G) := by
  let M := normalizer (L : Set G)
  let B := Y.map J.subtype
  let D := pCoreActionKernelIn 2 L B
  let C := (pResidual 2 D).map D.subtype
  have hBM : B ≤ M := local_solvable_nine_lift_containment
    h hab structural previous faithful J hJ hs Y hYp hAY e
  have hBp : IsPPerfect 2 B := hYp.of_surjective (J.subtype.subgroupMap Y)
    (J.subtype.subgroupMap_surjective Y)
  let eB := equivMapOfInjective Y J.subtype J.subtype_injective
  let eQ := QuotientGroup.congr (pCore 2 Y) (pCore 2 B) eB (pCore_map_iso 2 eB)
  have h9 : Nat.card (B ⧸ pCore 2 B) = 9 := by
    rw [←Nat.card_congr eQ.toEquiv,Nat.card_congr e.toEquiv,Nat.card_prod]
    norm_num [Nat.card_zmod]
  have hYn : Y ≠ ⊥ := by
    intro hz
    have hc : Nat.card (Y ⧸ pCore 2 Y) = 9 := by
      rw [Nat.card_congr e.toEquiv,Nat.card_prod]
      norm_num [Nat.card_zmod]
    rw [hz] at hc
    have ho : Nat.card ((⊥ : Subgroup J) ⧸ pCore 2 (⊥ : Subgroup J)) = 1 :=
      Nat.card_eq_one_iff_exists.mpr ⟨1,fun _ => Subsingleton.elim _ _⟩
    omega
  let f : B →* MulAut (L ⧸ pCore 2 L) :=
    (pCoreNormalizerAction 2 L).comp (inclusion hBM)
  have hfn : f ≠ 1 := by
    intro hf
    obtain ⟨x,hx⟩ := local_normal_twoPerfect_quotient_action_nontrivial
      h structural J hJ Y hYp hYn hBM
    exact hx (DFunLike.congr_fun hf x)
  let := h.chosen.elementary
  let eL := h.naturalMarking.quotientEquiv.trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm
  have hcAut : Nat.card (MulAut (L ⧸ pCore 2 L)) = 336 := by
    rw [Nat.card_congr (MulAut.congr (eL.trans Matrix.PSL3Two.equiv)).toEquiv]
    exact Matrix.PSL3Two.Automorphisms.card_aut
  obtain ⟨hCn,hCp,hCf,hm,hc⟩ := f.cubic_kernel_residual hBp hfn h9
    (by rw [hcAut]; decide)
  let C₀ := (pResidual 2 f.ker).map f.ker.subtype
  let : C₀.Normal := hCn
  have hD : D = f.ker.map B.subtype := pCoreActionKernelIn_eq_map_ker 2 L B hBM
  have hC : C₀.map B.subtype = C := by
    rw [show C₀ = (pResidual 2 f.ker).map f.ker.subtype from rfl,map_embedded_pResidual,←hD]
  have hcC : Nat.card (C ⧸ pCore 2 C) = 3 := by
    let ee := (equivMapOfInjective C₀ B.subtype B.subtype_injective).trans
      (MulEquiv.subgroupCongr hC)
    exact (Nat.card_congr (QuotientGroup.congr _ _ ee (pCore_map_iso 2 ee)).toEquiv).symm.trans hc
  have hCB : C ≤ B := (map_subtype_le _).trans inf_le_left
  have hJB : J ≤ normalizer (B : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      Y.le_normalizer_map J.subtype
  have hMD : M ≤ normalizer
      (((pCoreNormalizerAction 2 L).ker).map M.subtype : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      (pCoreNormalizerAction 2 L).ker.le_normalizer_map M.subtype
  have hTD : (T : Subgroup G) ≤ normalizer (D : Set G) :=
    (le_inf ((F.sylow_le_of_mem_Hz hJ).trans hJB)
      ((h.sylow_normalizes_at structural).trans hMD)).trans inf_normalizer_le_normalizer_inf
  have hTC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    hTD.trans (normalizer_le_normalizer_characteristic_image D (pResidual 2 D))
  have hcomm : ⁅L,C⁆ ≤ L.pCoreIn 2 :=
    (commutator_mono le_rfl (map_subtype_le _)).trans (pCoreActionKernelIn_commutator 2 L B)
  have hCne : C ≠ ⊥ := by
    intro hz
    rw [hz] at hcC
    have ho : Nat.card ((⊥ : Subgroup G) ⧸ pCore 2 (⊥ : Subgroup G)) = 1 :=
      Nat.card_eq_one_iff_exists.mpr ⟨1,fun _ => Subsingleton.elim _ _⟩
    omega
  have hbound := local_twoPerfect_core_commutator_normalizer h structural J hJ C
    (hCB.trans (map_subtype_le Y)) (isPPerfect_embedded_pResidual 2 D) hCne hTC hcomm
  exact ⟨hCB,isPPerfect_embedded_pResidual 2 D,hTC,hcC,hcomm,hbound,
    fun hj => hJ.2.2 (hj.trans hbound)⟩


/-- The cubic kernel lift has its intrinsic two-core as the exact star-map
kernel, and the actual three-core moves its cubic image. -/
theorem local_solvable_nine_centralizing_line_moved
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) (Y : Subgroup J) [Y.Normal]
    (hYp : IsPPerfect 2 Y) (hAY : (F.Li L 1).subgroupOf J ≤ Y)
    (e : (Y ⧸ pCore 2 Y) ≃*
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)))
    (hr : pResidual 2 (HStar J) = pCore 3 (HStar J)) :
    ∃ C : Subgroup J, C ≤ Y ∧ IsPPerfect 2 C ∧
      (T : Subgroup G) ≤ normalizer (C.map J.subtype : Set G) ∧
      ((QuotientGroup.mk' (pCore 2 J)).comp C.subtype).ker = pCore 2 C ∧
      Nat.card (C.map (QuotientGroup.mk' (pCore 2 J))) = 3 ∧
      ⁅L,C.map J.subtype⁆ ≤ L.pCoreIn 2 ∧
      normalizer (C.map J.subtype : Set G) ≤ normalizer (L : Set G) ∧
      ¬ pCore 3 (HStar J) ≤ normalizer
        (C.map (QuotientGroup.mk' (pCore 2 J)) : Set (HStar J)) := by
  let D := pCoreActionKernelIn 2 L (Y.map J.subtype)
  let C₀ := (pResidual 2 D).map D.subtype
  obtain ⟨hCB,hCp,hTC,hc,hcomm,hbound,hout⟩ :=
    local_solvable_nine_centralizing_lift h hab structural previous faithful J hJ hs Y hYp hAY e
  have hCJ : C₀ ≤ J := hCB.trans (map_subtype_le Y)
  let C := C₀.subgroupOf J
  have hmap : C.map J.subtype = C₀ := map_subgroupOf_eq_of_le hCJ
  have hCY : C ≤ Y := by
    apply (map_le_map_iff_of_injective J.subtype_injective).mp
    rw [hmap]
    exact hCB
  let eC := subgroupOfEquivOfLe hCJ
  have hp : IsPPerfect 2 C := hCp.of_surjective eC.symm.toMonoidHom eC.symm.surjective
  have hcC : Nat.card (C ⧸ pCore 2 C) = 3 :=
    (Nat.card_congr (QuotientGroup.congr _ _ eC (pCore_map_iso 2 eC)).toEquiv).trans hc
  let q := QuotientGroup.mk' (pCore 2 J)
  let f := q.comp C.subtype
  have hkq : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hkf : IsPGroup 2 f.ker := hkq.comap_of_injective _ C.subtype_injective
  have h3Y : IsPGroup 3 (Y.map q) := by
    let eY := (coreQuotientEquivImage 2 Y).symm.trans e
    apply IsPGroup.of_card (n := 2)
    rw [Nat.card_congr eY.toEquiv,Nat.card_prod]
    norm_num [Nat.card_zmod]
  have hfr : f.range = C.map q := by rw [MonoidHom.range_comp,range_subtype]
  have h3 : IsPGroup 3 f.range := hfr.symm ▸ h3Y.to_le (map_mono hCY)
  have h2 : pCore 2 f.range = ⊥ :=
    bot_unique ((le_inf le_rfl le_top).trans
      (pCore_isPGroup.disjoint_of_coprime (h3.to_subgroup ⊤)
        (by decide : Nat.Coprime 2 3)).le_bot)
  have hk : f.ker = pCore 2 C := f.ker_eq_pCore_of_range_core_eq_bot 2 hkf h2
  have hcc : Nat.card (C.map q) = 3 := by
    rw [←hfr,←Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,hk]
    exact hcC
  have hTC' : (T : Subgroup G) ≤ normalizer (C.map J.subtype : Set G) := hmap.symm ▸ hTC
  refine ⟨C,hCY,hp,hTC',hk,hcc,hmap.symm ▸ hcomm,hmap.symm ▸ hbound,?_⟩
  intro hP
  let S := T.subtype (F.sylow_le_of_mem_Hz hJ)
  have hSC : (S : Subgroup J) ≤ normalizer (C : Set J) := by
    rw [←subgroupOf_normalizer_eq hCJ]
    exact fun _ hx => hTC hx
  have hSN : (S : Subgroup J).map q ≤ normalizer (C.map q : Set (HStar J)) :=
    (map_mono hSC).trans (le_normalizer_map q)
  have hall : (⊤ : Subgroup (HStar J)) ≤ normalizer (C.map q : Set (HStar J)) := by
    have ht := pResidual_sup_sylow_eq_top (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J)))
    rw [hr] at ht
    rw [←ht]
    exact sup_le hP hSN
  have hQC : q.ker ≤ normalizer (C : Set J) := by
    rw [QuotientGroup.ker_mk']
    exact (pCore_isPGroup.le_sylow_of_normal S).trans hSC
  have hJC : (⊤ : Subgroup J) ≤ normalizer (C : Set J) :=
    (map_le_normalizer_map_iff_of_pPerfect q C ⊤ hp hkq hQC).mp
      (le_top.trans hall)
  apply hout
  have hh := (map_mono (f := J.subtype) hJC).trans (le_normalizer_map J.subtype)
  simpa only [←MonoidHom.range_eq_map,range_subtype,hmap] using hh


/-- The normal nine branch cannot have abelian three-core: that core would
fix the cubic action-kernel line, contrary to its proved movement. -/
theorem local_solvable_nine_threeCore_not_abelian
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) (Y : Subgroup J) [Y.Normal]
    (hYp : IsPPerfect 2 Y) (hAY : (F.Li L 1).subgroupOf J ≤ Y)
    (e : (Y ⧸ pCore 2 Y) ≃*
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)))
    (hr : pResidual 2 (HStar J) = pCore 3 (HStar J)) :
    ¬ IsMulCommutative (pCore 3 (HStar J)) := by
  intro habP
  let := habP
  obtain ⟨C,hCY,_,_,_,_,_,_,hout⟩ := local_solvable_nine_centralizing_line_moved
    h hab structural previous faithful J hJ hs Y hYp hAY e hr
  let q := QuotientGroup.mk' (pCore 2 J)
  let eY := (coreQuotientEquivImage 2 Y).symm.trans e
  have h3 : IsPGroup 3 (Y.map q) := by
    apply IsPGroup.of_card (n := 2)
    rw [Nat.card_congr eY.toEquiv,Nat.card_prod]
    norm_num [Nat.card_zmod]
  let : (Y.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hYP : Y.map q ≤ pCore 3 (HStar J) := le_sSup ⟨inferInstance,h3⟩
  exact hout ((le_centralizer (pCore 3 (HStar J))).trans
    ((centralizer_le ((map_mono hCY).trans hYP)).trans
      (Subgroup.centralizer_le_normalizer _)))

/-- The original minimal witness supplies a moving cubic kernel line in the
nine branch; the Heisenberg center marking is preserved. -/
theorem local_minimal_solvable_threeCore_kernel_movement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ∃ (I : Subgroup G), I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      Group.IsSolvable I ∧
      (∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < I →
        D ≤ normalizer (L : Set G)) ∧
    ∃ (X : Subgroup (pCore 3 (HStar I))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup I),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 I ∧
      Y.map (QuotientGroup.mk' (pCore 2 I)) = X.map (pCore 3 (HStar I)).subtype ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
      (F.Li L 1).subgroupOf I ≤ Y ∧
      (Y.map I.subtype).pCoreIn 2 < Y.map I.subtype ⊓ normalizer (L : Set G) ∧
      ((Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∧
          pResidual 2 (HStar I) = pCore 3 (HStar I) ∧
          Y.map I.subtype ≤ normalizer (L : Set G) ∧
          ¬ IsMulCommutative (pCore 3 (HStar I)) ∧
          ∃ C : Subgroup I, C ≤ Y ∧ IsPPerfect 2 C ∧
            (T : Subgroup G) ≤ normalizer (C.map I.subtype : Set G) ∧
            ((QuotientGroup.mk' (pCore 2 I)).comp C.subtype).ker = pCore 2 C ∧
            Nat.card (C.map (QuotientGroup.mk' (pCore 2 I))) = 3 ∧
            ⁅L,C.map I.subtype⁆ ≤ L.pCoreIn 2 ∧
            normalizer (C.map I.subtype : Set G) ≤ normalizer (L : Set G) ∧
            ¬ pCore 3 (HStar I) ≤ normalizer
              (C.map (QuotientGroup.mk' (pCore 2 I)) : Set (HStar I))) ∨
        (Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3) ∧
          ((F.Li L 1).subgroupOf I).Normal ∧
          ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) =
            ((center X).map X.subtype).map (pCore 3 (HStar I)).subtype)) := by
  obtain ⟨I,hIJ,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,hAY,hi,_,he⟩ :=
    local_minimal_solvable_threeCore_nine_containment h hab structural previous faithful J hJ hs
  let := hYn
  refine ⟨I,hIJ,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,hAY,hi,?_⟩
  rcases he with ⟨he,hr,hM⟩ | he
  · exact Or.inl ⟨he,hr,hM,local_solvable_nine_threeCore_not_abelian
      h hab structural previous faithful I hI hIs Y hYp hAY he.some hr,
      local_solvable_nine_centralizing_line_moved
      h hab structural previous faithful I hI hIs Y hYp hAY he.some hr⟩
  · exact Or.inr he

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The fixed point line in the original normal nine-lift

The three-core moves the quotient-centralizing cubic line in the normal
nine-image. Its fixed subgroup in that image is therefore cubic. Lift this
fixed subgroup normally inside the original two-perfect Y, retaining the
whole star-map kernel. Since Y lies in N_G(L), so does the lift. The checked
normal-cubic identification makes this lift exactly L₁. Hence L₁ is normal
in J and its actual star image is the fixed line of the three-core.

This line and the moved quotient-centralizing cubic are disjoint and generate
the original nine-image. A three-core element outside that image centralizes
the point and moves the other line. Selecting an actor whose enlarged group
is T-invariant, and handling its possible order nine, remain required.

The minimal solvable witness now has normal point residual in both the
elementary-nine and Heisenberg branches. The final application retains the
original G, T, L, V and flag, together with the exact point two-core kernel.
No solvable exclusion or final 14.7.52 classification is asserted here.

Source: Aschbacher–Smith, 14.5.20, printed p.1019, and 14.7.27–29,
printed pp.1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The three-core fixed line in the normal nine-image is precisely the
original point image, and its normal lift is the original point residual. -/
theorem local_solvable_nine_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) (Y : Subgroup J) [Y.Normal]
    (hYp : IsPPerfect 2 Y) (hAY : (F.Li L 1).subgroupOf J ≤ Y)
    (e : (Y ⧸ pCore 2 Y) ≃*
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)))
    (hr : pResidual 2 (HStar J) = pCore 3 (HStar J)) :
    ((F.Li L 1).subgroupOf J).Normal ∧
      ((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) =
        Y.map (QuotientGroup.mk' (pCore 2 J)) ⊓
          centralizer (pCore 3 (HStar J) : Set (HStar J)) := by
  let q := QuotientGroup.mk' (pCore 2 J)
  let P := pCore 3 (HStar J)
  let N := Y.map q
  let Z := N ⊓ centralizer (P : Set (HStar J))
  let : N.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : Z.Normal := inferInstance
  have hkq : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have h9 : Nat.card N = 9 := by
    rw [←Nat.card_congr (coreQuotientEquivImage 2 Y).toEquiv,
      Nat.card_congr e.toEquiv,Nat.card_prod]
    norm_num [Nat.card_zmod]
  have hN : IsPGroup 3 N := IsPGroup.of_card (n := 2) h9
  have hmove : ¬ P ≤ centralizer (N : Set (HStar J)) := by
    intro hc
    obtain ⟨C,hCY,_,_,_,_,_,_,hout⟩ := local_solvable_nine_centralizing_line_moved
      h hab structural previous faithful J hJ hs Y hYp hAY e hr
    exact hout (hc.trans ((centralizer_le (map_mono hCY)).trans
      (Subgroup.centralizer_le_normalizer _)))
  have hZ : Nat.card Z = 3 := normal_nine_fixed_line_card P N pCore_isPGroup hN h9 hmove
  obtain ⟨W,hWY,hWp,hWm,hWN,hWK,hWk,hWe⟩ := exists_three_lift_within_normal
    q hkq Y Z ⊤ inf_le_left le_normalizer_of_normal (hN.to_le inf_le_left)
  let : W.Normal := normalizer_eq_top_iff.mp (top_unique (by simpa using hWN))
  have hcW : Nat.card (W ⧸ pCore 2 W) = 3 := (Nat.card_congr hWe.some.toEquiv).trans hZ
  have hWM : W.map J.subtype ≤ normalizer (L : Set G) :=
    (map_mono hWY).trans (local_solvable_nine_lift_containment
      h hab structural previous faithful J hJ hs Y hYp hAY e)
  have hi := local_lift_intersection_of_cubic_sublift h structural J hJ W W le_rfl hWM hWk hcW
  have heq := local_solvable_normal_cubic_lift_eq_point
    h hab structural previous faithful J hJ hs W hWp hcW hi
  exact ⟨heq ▸ inferInstanceAs W.Normal,heq ▸ hWm⟩

/-- The literal nine-image splits into the point and quotient-centralizing
cubics. A three-core actor outside that image fixes the point and moves the
other line. This does not assert an order-three lift or T-stability of its join. -/
theorem local_solvable_nine_split_and_actor
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) (Y : Subgroup J) [Y.Normal]
    (hYp : IsPPerfect 2 Y) (hAY : (F.Li L 1).subgroupOf J ≤ Y)
    (e : (Y ⧸ pCore 2 Y) ≃*
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)))
    (hr : pResidual 2 (HStar J) = pCore 3 (HStar J)) :
    let q := QuotientGroup.mk' (pCore 2 J)
    let A := ((F.Li L 1).subgroupOf J).map q
    ∃ C : Subgroup J, C ≤ Y ∧ IsPPerfect 2 C ∧
      (T : Subgroup G) ≤ normalizer (C.map J.subtype : Set G) ∧
      (q.comp C.subtype).ker = pCore 2 C ∧ Nat.card (C.map q) = 3 ∧
      ⁅L,C.map J.subtype⁆ ≤ L.pCoreIn 2 ∧
      normalizer (C.map J.subtype : Set G) ≤ normalizer (L : Set G) ∧
      Disjoint A (C.map q) ∧ A ⊔ C.map q = Y.map q ∧
      ∃ y : HStar J, y ∈ pCore 3 (HStar J) ∧ y ∉ Y.map q ∧
        y ∈ centralizer (A : Set (HStar J)) ∧
        y ∉ normalizer (C.map q : Set (HStar J)) := by
  classical
  let q := QuotientGroup.mk' (pCore 2 J)
  let A := ((F.Li L 1).subgroupOf J).map q
  let N := Y.map q
  obtain ⟨hn,hfixed⟩ := local_solvable_nine_point_normal
    h hab structural previous faithful J hJ hs Y hYp hAY e hr
  let := hn
  let : A.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  obtain ⟨C,hCY,hCp,hTC,hCk,h3C,hcomm,hbound,hout⟩ :=
    local_solvable_nine_centralizing_line_moved
      h hab structural previous faithful J hJ hs Y hYp hAY e hr
  have h3A : Nat.card A = 3 :=
    (local_solvable_point_kernel h hab structural previous faithful J hJ hs).2
  have hne : A ≠ C.map q := by
    intro he
    apply hout
    rw [←he]
    exact le_normalizer_of_normal
  have hdis : Disjoint A (C.map q) := by
    have hd : Nat.card (A ⊓ C.map q : Subgroup (HStar J)) ∣ 3 :=
      h3A ▸ card_dvd_of_le (inf_le_left : A ⊓ C.map q ≤ A)
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ hd with h1 | h3
    · exact disjoint_iff.mpr (card_eq_one.mp h1)
    · have hAeq : A ⊓ C.map q = A := eq_of_le_of_card_ge inf_le_left (by rw [h3,h3A])
      have hCeq : A ⊓ C.map q = C.map q := eq_of_le_of_card_ge inf_le_right (by rw [h3,h3C])
      exact (hne (hAeq.symm.trans hCeq)).elim
  let eN := (coreQuotientEquivImage 2 Y).symm.trans e
  let : IsMulCommutative N := IsMulCommutative.of_comm fun a b =>
    eN.injective (by simp only [map_mul,mul_comm])
  have h9 : Nat.card N = 9 := by
    rw [Nat.card_congr eN.toEquiv,Nat.card_prod]
    norm_num [Nat.card_zmod]
  have hgen : A ⊔ C.map q = N := by
    apply eq_of_le_of_card_ge (sup_le (map_mono hAY) (map_mono hCY))
    rw [card_sup_eq_mul_of_normalizes_of_disjoint A (C.map q)
      le_normalizer_of_normal hdis,h3A,h3C,h9]
  obtain ⟨y,hyP,hyC⟩ := Set.not_subset.mp hout
  have hyN : y ∉ N := by
    intro hy
    exact hyC (((le_centralizer N).trans
      ((centralizer_le (map_mono hCY)).trans (Subgroup.centralizer_le_normalizer _))) hy)
  have hAP : A ≤ centralizer (pCore 3 (HStar J) : Set (HStar J)) := by
    rw [show A = N ⊓ centralizer (pCore 3 (HStar J) : Set (HStar J)) from hfixed]
    exact inf_le_right
  exact ⟨C,hCY,hCp,hTC,hCk,h3C,hcomm,hbound,hdis,hgen,y,hyP,hyN,
    le_centralizer_iff.mp hAP hyP,hyC⟩

/-- The selected original minimal solvable local has normal point residual in either model branch. -/
theorem local_minimal_solvable_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ∃ I : Subgroup G, I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      Group.IsSolvable I ∧
      (∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < I →
        D ≤ normalizer (L : Set G)) ∧
      ((F.Li L 1).subgroupOf I).Normal := by
  obtain ⟨I,hIJ,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,hAY,hi,he⟩ :=
    local_minimal_solvable_threeCore_point_and_center h hab structural previous faithful J hJ hs
  let := hYn
  refine ⟨I,hIJ,hI,hIs,hmin,?_⟩
  rcases he with ⟨he,hr⟩ | ⟨he,hn,_⟩
  · exact (local_solvable_nine_point_normal h hab structural previous faithful
      I hI hIs Y hYp hAY he.some hr).1
  · exact hn

/-- Apply the split to the actual selected minimal witness. The alternative
retains its Heisenberg marking; neither model is assumed at this consumer. -/
theorem original_solvable_nine_split_or_heisenberg
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hs : Group.IsSolvable F.H) :
    ∃ I : Subgroup G, I ≤ F.H ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      Group.IsSolvable I ∧
      (∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < I →
        D ≤ normalizer (L : Set G)) ∧
      ((F.Li L 1).subgroupOf I).Normal ∧
      ∃ Y : Subgroup I, Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 I ∧
        (F.Li L 1).subgroupOf I ≤ Y ∧
        ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
        ((Nonempty ((Y ⧸ pCore 2 Y) ≃*
            (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∧
          pResidual 2 (HStar I) = pCore 3 (HStar I) ∧
          let q := QuotientGroup.mk' (pCore 2 I)
          let A := ((F.Li L 1).subgroupOf I).map q
          ∃ C : Subgroup I, C ≤ Y ∧ IsPPerfect 2 C ∧
            (T : Subgroup G) ≤ normalizer (C.map I.subtype : Set G) ∧
            (q.comp C.subtype).ker = pCore 2 C ∧ Nat.card (C.map q) = 3 ∧
            ⁅L,C.map I.subtype⁆ ≤ L.pCoreIn 2 ∧
            normalizer (C.map I.subtype : Set G) ≤ normalizer (L : Set G) ∧
            Disjoint A (C.map q) ∧ A ⊔ C.map q = Y.map q ∧
            ∃ y : HStar I, y ∈ pCore 3 (HStar I) ∧ y ∉ Y.map q ∧
              y ∈ centralizer (A : Set (HStar I)) ∧
              y ∉ normalizer (C.map q : Set (HStar I))) ∨
          Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3)) := by
  obtain ⟨I,hIH,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,hAY,hi,he⟩ :=
    local_minimal_solvable_threeCore_point_and_center h hab structural previous faithful
      F.H (F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)) hs
  let := hYn
  rcases he with ⟨he,hr⟩ | ⟨he,hn,_⟩
  · exact ⟨I,hIH,hI,hIs,hmin,
      (local_solvable_nine_point_normal h hab structural previous faithful
        I hI hIs Y hYp hAY he.some hr).1,Y,hYn,hYp,hYr,hAY,hk,
      Or.inl ⟨he,hr,local_solvable_nine_split_and_actor h hab structural previous faithful
        I hI hIs Y hYp hAY he.some hr⟩⟩
  · exact ⟨I,hIH,hI,hIs,hmin,hn,Y,hYn,hYp,hYr,hAY,hk,Or.inr he⟩

/-- At the original point normalizer, a solvable witness yields a minimal
escaping local which normalizes L₁, with the literal cubic image and full
two-core kernel. No local normality or marking is an additional premise. -/
theorem original_solvable_minimal_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hs : Group.IsSolvable F.H) :
    ∃ I : Subgroup G, I ≤ F.H ∧ ∃ hI : I ∈ F.Hz L (normalizer (L : Set G)),
      Group.IsSolvable I ∧
      (∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < I →
        D ≤ normalizer (L : Set G)) ∧
      ((F.Li L 1).subgroupOf I).Normal ∧
      I ≤ normalizer (F.Li L 1 : Set G) ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp
        (inclusion (F.Li_one_le_of_mem_Hz hI))).ker =
        pCore 2 (F.Li L 1) ∧
      Nat.card (((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))) = 3 := by
  obtain ⟨I,hIH,hI,hIs,hmin,hn⟩ := local_minimal_solvable_point_normal
    h hab structural previous faithful F.H
      (F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)) hs
  let := hn
  have hnorm : I ≤ normalizer (F.Li L 1 : Set G) := by
    have hh := ((F.Li L 1).subgroupOf I).le_normalizer_map I.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,
      map_subgroupOf_eq_of_le (F.Li_one_le_of_mem_Hz hI)] using hh
  exact ⟨I,hIH,hI,hIs,hmin,hn,hnorm,
    local_solvable_point_kernel h hab structural previous faithful I hI hIs⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# T-invariant cyclic enlargement of the original normal nine-lift

In an original solvable J in H_z, the three-core acts nontrivially on the
normal elementary-nine image and fixes precisely the original point line.
Select a three-core actor whose cyclic subgroup is normalized by the actual
Sylow image. The canonical quotient-centralizing cubic residual is normalized
by J intersect N_G(L). An actor in that intersection would centralize both
cubic lines, so the selected actor escapes the literal normalizer image.

Lift its cyclic subgroup to a two-perfect T-invariant subgroup, retaining the
full two-core kernel. If the actor has order three, the proved cubic-containment
argument gives a contradiction. For higher three-power order, supercriticality
puts the fixed point line in its cyclic subgroup. Two-perfectness then lifts
point containment through the exact kernel. Adjoining T gives an escaping
local with cyclic three-residual, contrary to the original Sylow bound.

This excludes the elementary-nine supercritical branch in the original minimal
solvable witness. The final application constructs its remaining Heisenberg
branch directly from the original solvability assumption, preserving relative
point normality, its center marking and the literal quotient kernel. Terminal
Heisenberg exclusion and the component reductions through 14.7.52 remain.

Source: Aschbacher–Smith, 14.5.20, printed pp.1018–1019, and
14.7.27–29, printed pp.1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Select a three-core actor escaping the actual seed-normalizer image,
centralizing the point line and generating a T-invariant cyclic subgroup. -/
theorem local_solvable_nine_invariant_actor
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) (Y : Subgroup J) [Y.Normal]
    (hYp : IsPPerfect 2 Y) (hAY : (F.Li L 1).subgroupOf J ≤ Y)
    (e : (Y ⧸ pCore 2 Y) ≃*
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)))
    (hr : pResidual 2 (HStar J) = pCore 3 (HStar J)) :
    let q := QuotientGroup.mk' (pCore 2 J)
    let S := T.subtype (F.sylow_le_of_mem_Hz hJ)
    let A := ((F.Li L 1).subgroupOf J).map q
    ∃ y : HStar J, y ∈ pCore 3 (HStar J) ∧
      y ∉ centralizer (Y.map q : Set (HStar J)) ∧ y ∉ Y.map q ∧
      y ∈ centralizer (A : Set (HStar J)) ∧
      (S : Subgroup J).map q ≤ normalizer (zpowers y : Set (HStar J)) ∧
      y ∉ ((normalizer (L : Set G)).subgroupOf J).map q := by
  classical
  let q := QuotientGroup.mk' (pCore 2 J)
  let S := T.subtype (F.sylow_le_of_mem_Hz hJ)
  let P := pCore 3 (HStar J)
  let N := Y.map q
  let A := ((F.Li L 1).subgroupOf J).map q
  let M := normalizer (L : Set G)
  obtain ⟨hAn,hfixed⟩ := local_solvable_nine_point_normal
    h hab structural previous faithful J hJ hs Y hYp hAY e hr
  let := hAn
  let : A.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : N.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let eN := (coreQuotientEquivImage 2 Y).symm.trans e
  let : IsElementaryAbelian 3 N := IsElementaryAbelian.of_injective eN.toMonoidHom eN.injective
  have h9 : Nat.card N = 9 := by
    rw [Nat.card_congr eN.toEquiv,Nat.card_prod]
    norm_num [Nat.card_zmod]
  have hmove : ¬ P ≤ centralizer (N : Set (HStar J)) := by
    intro hc
    obtain ⟨C,hCY,_,_,_,_,_,_,hout⟩ := local_solvable_nine_centralizing_line_moved
      h hab structural previous faithful J hJ hs Y hYp hAY e hr
    exact hout (hc.trans ((centralizer_le (map_mono hCY)).trans
      (Subgroup.centralizer_le_normalizer _)))
  obtain ⟨y,hyP,hyN,hSy⟩ := normal_nine_normalized_actor P N ((S : Subgroup J).map q)
    pCore_isPGroup (S.isPGroup'.map q) h9 hmove
  have hyout : y ∉ N := fun hy => hyN (le_centralizer N hy)
  have hAP : A ≤ centralizer (P : Set (HStar J)) := by
    rw [show A = N ⊓ centralizer (P : Set (HStar J)) from hfixed]
    exact inf_le_right
  have hyA : y ∈ centralizer (A : Set (HStar J)) := le_centralizer_iff.mp hAP hyP
  refine ⟨y,hyP,hyN,hyout,hyA,hSy,?_⟩
  let D := pCoreActionKernelIn 2 L (Y.map J.subtype)
  let C₀ := (pResidual 2 D).map D.subtype
  obtain ⟨hCB,hCp,hTC,hc,hcomm,hbound,hout⟩ :=
    local_solvable_nine_centralizing_lift h hab structural previous faithful J hJ hs Y hYp hAY e
  have hCJ : C₀ ≤ J := hCB.trans (map_subtype_le Y)
  let C := C₀.subgroupOf J
  have hCm : C.map J.subtype = C₀ := map_subgroupOf_eq_of_le hCJ
  have hCY : C ≤ Y := by
    apply (map_le_map_iff_of_injective J.subtype_injective).mp
    rw [hCm]
    exact hCB
  let eC := subgroupOfEquivOfLe hCJ
  have hpC : IsPPerfect 2 C := hCp.of_surjective eC.symm.toMonoidHom eC.symm.surjective
  have hcC : Nat.card (C ⧸ pCore 2 C) = 3 :=
    (Nat.card_congr (QuotientGroup.congr _ _ eC (pCore_map_iso 2 eC)).toEquiv).trans hc
  let f := q.comp C.subtype
  have hkq : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hkf : IsPGroup 2 f.ker := hkq.comap_of_injective _ C.subtype_injective
  have h3N : IsPGroup 3 N := IsPGroup.of_card (n := 2) (by simpa using h9)
  have hfr : f.range = C.map q := by rw [MonoidHom.range_comp,range_subtype]
  have h3f : IsPGroup 3 f.range := hfr.symm ▸ h3N.to_le (map_mono hCY)
  have h2f : pCore 2 f.range = ⊥ :=
    bot_unique ((le_inf le_rfl le_top).trans
      (pCore_isPGroup.disjoint_of_coprime (h3f.to_subgroup ⊤)
        (by decide : Nat.Coprime 2 3)).le_bot)
  have hkf' : f.ker = pCore 2 C := f.ker_eq_pCore_of_range_core_eq_bot 2 hkf h2f
  have h3C : Nat.card (C.map q) = 3 := by
    rw [←hfr,←Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,hkf']
    exact hcC
  have hSC : (S : Subgroup J) ≤ normalizer (C : Set J) := by
    rw [←subgroupOf_normalizer_eq hCJ]
    exact fun _ hx => hTC hx
  have hkC : q.ker ≤ normalizer (C : Set J) := by
    rw [QuotientGroup.ker_mk']
    exact (pCore_isPGroup.le_sylow_of_normal S).trans hSC
  have hne : A ≠ C.map q := by
    intro he
    have hnorm : (⊤ : Subgroup J) ≤ normalizer (C : Set J) :=
      (map_le_normalizer_map_iff_of_pPerfect q C ⊤ hpC hkq hkC).mp (by
        rw [←he]
        exact le_normalizer_of_normal)
    apply hout
    have hh := (map_mono (f := J.subtype) hnorm).trans (le_normalizer_map J.subtype)
    simpa only [←MonoidHom.range_eq_map,range_subtype,hCm] using hh
  have h3A : Nat.card A = 3 :=
    (local_solvable_point_kernel h hab structural previous faithful J hJ hs).2
  have hdis : Disjoint A (C.map q) := by
    have hd : Nat.card (A ⊓ C.map q : Subgroup (HStar J)) ∣ 3 :=
      h3A ▸ card_dvd_of_le (inf_le_left : A ⊓ C.map q ≤ A)
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ hd with h1 | h3
    · exact disjoint_iff.mpr (card_eq_one.mp h1)
    · have hAe : A ⊓ C.map q = A := eq_of_le_of_card_ge inf_le_left (by rw [h3,h3A])
      have hCe : A ⊓ C.map q = C.map q := eq_of_le_of_card_ge inf_le_right (by rw [h3,h3C])
      exact (hne (hAe.symm.trans hCe)).elim
  have hgen : A ⊔ C.map q = N := by
    apply eq_of_le_of_card_ge (sup_le (map_mono hAY) (map_mono hCY))
    rw [card_sup_eq_mul_of_normalizes_of_disjoint A (C.map q)
      le_normalizer_of_normal hdis,h3A,h3C,h9]
  have hJB : J ≤ normalizer (Y.map J.subtype : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      Y.le_normalizer_map J.subtype
  have hMD : M ≤ normalizer
      (((pCoreNormalizerAction 2 L).ker).map M.subtype : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      (pCoreNormalizerAction 2 L).ker.le_normalizer_map M.subtype
  have hJMC : J ⊓ M ≤ normalizer (C₀ : Set G) :=
    ((le_inf (inf_le_left.trans hJB) (inf_le_right.trans hMD)).trans
      inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image D (pResidual 2 D))
  intro hym
  obtain ⟨x,hx,hxy⟩ := hym
  have hxC : x ∈ normalizer (C : Set J) := by
    rw [←subgroupOf_normalizer_eq hCJ]
    exact hJMC ⟨x.property,hx⟩
  have hyC : y ∈ normalizer (C.map q : Set (HStar J)) :=
    hxy ▸ le_normalizer_map q (mem_map_of_mem q hxC)
  let : Normalizes (zpowers y) (C.map q) := ⟨zpowers_le.mpr hyC⟩
  have hyCp : IsPGroup 3 (zpowers y) :=
    (pCore_isPGroup (p := 3) (G := HStar J)).to_le (zpowers_le.mpr hyP)
  have htriv := actsTrivially_of_isPGroup_on_cyclic_prime_order
    (A := zpowers y) (G := C.map q) Nat.prime_three hyCp
    (isCyclic_of_prime_card h3C) h3C
  have hyCC : y ∈ centralizer (C.map q : Set (HStar J)) := by
    intro c hc
    have hh := congrArg Subtype.val (htriv ⟨y,mem_zpowers y⟩ ⟨c,hc⟩)
    change y * c * y⁻¹ = c at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  apply hyN
  rw [←hgen]
  exact le_centralizer_iff.mp
    (sup_le (le_centralizer_iff.mpr (zpowers_le.mpr hyA))
      (le_centralizer_iff.mpr (zpowers_le.mpr hyCC))) (mem_zpowers y)

/-- A two-perfect T-invariant cyclic three-lift containing the original
point residual lies in the seed normalizer. -/
theorem local_cyclic_three_lift_containment
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (W : Subgroup J) (hWp : IsPPerfect 2 W)
    (hTW : (T : Subgroup G) ≤ normalizer (W.map J.subtype : Set G))
    (hAW : (F.Li L 1).subgroupOf J ≤ W)
    (hcyc : IsCyclic (W ⧸ pCore 2 W))
    (h3 : IsPGroup 3 (W ⧸ pCore 2 W)) :
    W.map J.subtype ≤ normalizer (L : Set G) := by
  classical
  by_contra hout
  let E := W.map J.subtype
  let D := E ⊔ (T : Subgroup G)
  have hEJ : E ≤ J := map_subtype_le W
  have hDJ : D ≤ J := sup_le hEJ (F.sylow_le_of_mem_Hz hJ)
  have hED : E ≤ D := le_sup_left
  have hTD : (T : Subgroup G) ≤ D := le_sup_right
  have hAE : F.Li L 1 ≤ E := by
    have hh := map_mono (f := J.subtype) hAW
    rwa [map_subgroupOf_eq_of_le (F.Li_one_le_of_mem_Hz hJ)] at hh
  have hAD : F.Li L 1 ≤ D := hAE.trans hED
  have hDH : D ≤ F.H := hDJ.trans hJ.2.1
  have hpoint : F.Vi 1 ≤ D.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsPGroup.of_card (n := 1) (by simpa using F.card 1 (by decide)))
    ((F.le_seed 1).trans (h.chosen.le_sylow.trans hTD)) hDH
  have hcore : D.pCoreIn 2 ≠ ⊥ := by
    intro hz
    have hh := le_bot_iff.mp (hz ▸ hpoint)
    have hc := F.card 1 (by decide)
    rw [hh,card_bot] at hc
    norm_num at hc
  have hD : D ∈ F.Hz L (normalizer (L : Set G)) :=
    ⟨⟨hcore,fun _ hx => hx.elim (fun ha => hAD ha) (fun ht => hTD ht)⟩,
      hDH,fun hh => hout (hED.trans hh)⟩
  have hEp : IsPPerfect 2 E := hWp.of_surjective (J.subtype.subgroupMap W)
    (J.subtype.subgroupMap_surjective W)
  let Z := E.subgroupOf D
  let : Z.Normal := normal_subgroupOf_of_le_normalizer (sup_le E.le_normalizer hTW)
  have hres : pResidual 2 D = Z := by
    apply map_injective D.subtype_injective
    rw [embedded_pResidual_join_pGroup E (T : Subgroup G) hEp T.isPGroup' hTW,
      map_subgroupOf_eq_of_le hED]
  let eZ : Z ≃* W := (subgroupOfEquivOfLe hED).trans
    (equivMapOfInjective W J.subtype J.subtype_injective).symm
  let eQ := QuotientGroup.congr _ _ eZ (pCore_map_iso 2 eZ)
  let qD := QuotientGroup.mk' (pCore 2 D)
  let eim : Z.map qD ≃* (W ⧸ pCore 2 W) :=
    (coreQuotientEquivImage 2 Z).symm.trans eQ
  let := hcyc
  have hcycim : IsCyclic (Z.map qD) := isCyclic_of_surjective eim.symm eim.symm.surjective
  have h3im : IsPGroup 3 (Z.map qD) := h3.of_equiv eim.symm
  have hrim : pResidual 2 (HStar D) = Z.map qD := by
    rw [←map_pResidual_of_surjective 2 qD (QuotientGroup.mk'_surjective _),hres]
  exact no_cyclic_three_local_star_residual_at h hab structural D hD
    ⟨hrim ▸ hcycim,hrim ▸ h3im⟩

/-- Exclude the marked elementary-nine supercritical branch in an original
solvable local, with the full star-map kernel retained. -/
theorem local_solvable_supercritical_nine_exclusion
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (X : Subgroup (pCore 3 (HStar J))) (hX : IsSupercriticalPSubgroup 3 X)
    (Y : Subgroup J) [Y.Normal]
    (hYp : IsPPerfect 2 Y) (hAY : (F.Li L 1).subgroupOf J ≤ Y)
    (e : (Y ⧸ pCore 2 Y) ≃*
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)))
    (hm : Y.map (QuotientGroup.mk' (pCore 2 J)) =
      X.map (pCore 3 (HStar J)).subtype)
    (hr : pResidual 2 (HStar J) = pCore 3 (HStar J)) : False := by
  classical
  let q := QuotientGroup.mk' (pCore 2 J)
  let S := T.subtype (F.sylow_le_of_mem_Hz hJ)
  let P := pCore 3 (HStar J)
  let N := Y.map q
  let A₀ := (F.Li L 1).subgroupOf J
  let A := A₀.map q
  obtain ⟨hAn,hfixed⟩ := local_solvable_nine_point_normal
    h hab structural previous faithful J hJ hs Y hYp hAY e hr
  let := hAn
  obtain ⟨y,hyP,hyN,hyout,hyA,hSy,hyM⟩ := local_solvable_nine_invariant_actor
    h hab structural previous faithful J hJ hs Y hYp hAY e hr
  have hkq : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hcy : IsPGroup 3 (zpowers y) :=
    (pCore_isPGroup (p := 3) (G := HStar J)).to_le (zpowers_le.mpr hyP)
  obtain ⟨W,_,hWp,hWm,hWA,hWK,hWk,⟨eW⟩⟩ := exists_three_lift_within_normal
    q hkq ⊤ (zpowers y) ((S : Subgroup J).map q)
    (by rw [map_top_of_surjective q (QuotientGroup.mk'_surjective _)]; exact le_top)
    hSy hcy
  have hSW : (S : Subgroup J) ≤ normalizer (W : Set J) :=
    (le_comap_map q _).trans hWA
  have hTW : (T : Subgroup G) ≤ normalizer (W.map J.subtype : Set G) := by
    intro t ht
    let tJ : J := ⟨t,F.sylow_le_of_mem_Hz hJ ht⟩
    exact le_normalizer_map J.subtype (mem_map_of_mem J.subtype
      (hSW (show tJ ∈ (S : Subgroup J) from ht)))
  have hWout : ¬ W.map J.subtype ≤ normalizer (L : Set G) := by
    intro hh
    have hWM : W ≤ (normalizer (L : Set G)).subgroupOf J :=
      fun w hw => hh (mem_map_of_mem J.subtype hw)
    exact hyM ((map_mono hWM) (hWm.symm ▸ mem_zpowers y))
  have hWpG : IsPPerfect 2 (W.map J.subtype) := hWp.of_surjective
    (J.subtype.subgroupMap W) (J.subtype.subgroupMap_surjective W)
  by_cases ho : orderOf y = 3
  · apply hWout
    apply local_solvable_cubic_containment h hab structural previous faithful J hJ hs
      (W.map J.subtype) (map_subtype_le W)
      ((map_subtype_le W).trans (F.normalizes_Li_one_of_relative_normal hJ)) hWpG hTW
    let eG := (equivMapOfInjective W J.subtype J.subtype_injective).symm
    let eGQ := QuotientGroup.congr _ _ eG (pCore_map_iso 2 eG)
    rw [Nat.card_congr eGQ.toEquiv,Nat.card_congr eW.toEquiv,Nat.card_zpowers,ho]
  · let eN := (coreQuotientEquivImage 2 Y).symm.trans e
    let eX := ((equivMapOfInjective X P.subtype P.subtype_injective).trans
      (MulEquiv.subgroupCongr hm.symm)).trans eN
    let : IsElementaryAbelian 3 X :=
      IsElementaryAbelian.of_injective eX.toMonoidHom eX.injective
    have h9X : Nat.card X = 9 := by
      rw [Nat.card_congr eX.toEquiv,Nat.card_prod]
      norm_num [Nat.card_zmod]
    let yP : P := ⟨y,hyP⟩
    have hyn : yP ∉ centralizer (X : Set P) := by
      intro hh
      apply hyN
      intro x hx
      rw [hm] at hx
      obtain ⟨a,ha,rfl⟩ := hx
      exact congrArg Subtype.val (hh a ha)
    have hoP : orderOf yP ≠ 3 := fun hh => ho ((Subgroup.orderOf_coe yP).trans hh)
    have hAX := supercritical_nine_fixed_line_le_zpowers pCore_isPGroup X hX h9X yP hyn hoP
    have hAZ : A ≤ zpowers y := by
      intro a ha
      have ha' : a ∈ N ⊓ centralizer (P : Set (HStar J)) := hfixed ▸ ha
      have haN : a ∈ X.map P.subtype := hm ▸ ha'.1
      obtain ⟨x,hx,hxa⟩ := haN
      have hxC : x ∈ centralizer (⊤ : Set P) := by
        intro b hb
        apply Subtype.ext
        change (b : HStar J) * P.subtype x = P.subtype x * (b : HStar J)
        rw [hxa]
        exact ha'.2 b b.property
      have hxZ := hAX ⟨hx,hxC⟩
      have hh : a ∈ (zpowers yP).map P.subtype := ⟨x,hxZ,hxa⟩
      rw [MonoidHom.map_zpowers] at hh
      change a ∈ zpowers y at hh
      exact hh
    have hAp : IsPPerfect 2 A₀ :=
      (show IsPPerfect 2 (F.Li L 1) from isPPerfect_embedded_pResidual 2 _).of_surjective
        (subgroupOfEquivOfLe (F.Li_one_le_of_mem_Hz hJ)).symm.toMonoidHom
        (subgroupOfEquivOfLe (F.Li_one_le_of_mem_Hz hJ)).symm.surjective
    have hAW : A₀ ≤ W := isPPerfect_le_of_map_le_of_kernel_normalizes q A₀ W
      hAp hkq hWK (by rw [hWm]; exact hAZ)
    have hcyW : IsCyclic (W ⧸ pCore 2 W) :=
      isCyclic_of_surjective eW.symm eW.symm.surjective
    have h3W : IsPGroup 3 (W ⧸ pCore 2 W) := hcy.of_equiv eW.symm
    exact hWout (local_cyclic_three_lift_containment h hab structural J hJ W hWp hTW hAW hcyW h3W)

/-- A minimal solvable escaping local has only the marked Heisenberg
supercritical branch: the elementary-nine branch has been excluded. -/
theorem local_minimal_solvable_threeCore_heisenberg
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ∃ (I : Subgroup G), I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      Group.IsSolvable I ∧
      (∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < I →
        D ≤ normalizer (L : Set G)) ∧
    ∃ (X : Subgroup (pCore 3 (HStar I))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup I),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 I ∧
      Y.map (QuotientGroup.mk' (pCore 2 I)) = X.map (pCore 3 (HStar I)).subtype ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
      (F.Li L 1).subgroupOf I ≤ Y ∧
      (Y.map I.subtype).pCoreIn 2 < Y.map I.subtype ⊓ normalizer (L : Set G) ∧
      Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3) ∧
      ((F.Li L 1).subgroupOf I).Normal ∧
      ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) =
        ((center X).map X.subtype).map (pCore 3 (HStar I)).subtype := by
  obtain ⟨I,hIJ,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,hAY,hi,he⟩ :=
    local_minimal_solvable_threeCore_point_and_center h hab structural previous faithful J hJ hs
  let := hYn
  rcases he with ⟨he,hr⟩ | ⟨he,hn,hcenter⟩
  · exact (local_solvable_supercritical_nine_exclusion h hab structural previous faithful
      I hI hIs X hX Y hYp hAY he.some hm hr).elim
  · exact ⟨I,hIJ,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,hAY,hi,he,hn,hcenter⟩

/-- The actual original point normalizer supplies a marked Heisenberg
witness under a solvability assumption, without an added local-model input. -/
theorem original_solvable_minimal_heisenberg
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hs : Group.IsSolvable F.H) :
    ∃ I : Subgroup G, I ≤ F.H ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      Group.IsSolvable I ∧
      (∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < I →
        D ≤ normalizer (L : Set G)) ∧
      ((F.Li L 1).subgroupOf I).Normal ∧
      ∃ Y : Subgroup I, Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 I ∧
        (F.Li L 1).subgroupOf I ≤ Y ∧
        ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
        Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3) := by
  obtain ⟨I,hIH,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,hAY,hi,he,hn,hcenter⟩ :=
    local_minimal_solvable_threeCore_heisenberg h hab structural previous faithful F.H
      (F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)) hs
  exact ⟨I,hIH,hI,hIs,hmin,hn,Y,hYn,hYp,hYr,hAY,hk,he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end
