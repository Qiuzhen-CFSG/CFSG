module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeExclusion
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Noncontained.Extraspecial.Rank
public import Theory.GroupTheory.PGroup.SelfCentralizingSupercritical
public import CFSG.Quasithin.ChapterA.Section01.RankActions.ThreeAutomorphisms
public import Theory.SpecificGroups.GL2.PrimeThreeFiveResidual.Coordinates

/-!
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
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem local_three_rank
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

private theorem point_perfect : IsPPerfect 2 (F.Li L 1) := by
  simp only [InvariantFlag.Li]
  exact isPPerfect_embedded_pResidual 2 _

/-- The two-core of the original L₁ centralizes every actual normal Heisenberg subgroup of J/O₂(J). -/
theorem local_normal_heisenberg_pointResidual_core_action_eq_bot
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
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
      Z ⊤ hc hexp le_top point_perfect
      (pointResidual_core_quotient_card h structural)
      ((QuotientGroup.mk' (pCore 2 J)).comp (inclusion (F.Li_one_le_of_mem_Hz hJ)))
      (fun _ => mem_top _) hne
  have hb := (primeRank_le_iff_elementary_card_le (HStar J)).mp
    (local_three_rank h J hJ) A hA
  rw [hcard] at hb
  norm_num at hb

/-- The actual three-core is self-centralizing in each solvable local quotient. -/
theorem local_solvable_threeCore_selfCentralizing
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
  have hr : primeRank 3 P ≤ 2 := (primeRank_subgroup_le 3 P).trans (local_three_rank h J hJ)
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
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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

private def liftModelEquiv
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
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
  let e := (liftModelEquiv J X Y hYm hYk).symm.trans he.some
  have hp := local_solvable_heisenberg_point_kernel h hab structural previous faithful
    J hJ hs X hX e
  exact Or.inr ⟨he,hp.1,hp.2,
    local_solvable_heisenberg_frattini_kernel h hab structural previous faithful J hJ hs X hX e⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
end

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
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
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    Nat.card (((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) = 3 ∨
      Nat.card (((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) = 24 := by
  obtain ⟨X,hX,Y,hYn,hYp,hYle,hYm,hYk,he⟩ :=
    local_solvable_threeCore_source h hab structural previous faithful J hJ hs
  let e := liftModelEquiv J X Y hYm hYk
  rcases he with he | he
  · have hh := local_solvable_nine_point_action h hab structural previous faithful J hJ hs
      X hX (e.symm.trans he.some)
    rcases hh with hh | ⟨c,e,he,hr,hk,hc⟩
    · exact Or.inl (by simpa only [MonoidHom.range_comp,inclusion_range] using hh.2)
    · exact Or.inr (by simpa only [MonoidHom.range_comp,inclusion_range] using hc)
  · exact Or.inl (local_solvable_heisenberg_point_kernel h hab structural previous faithful
      J hJ hs X hX (e.symm.trans he.some)).2

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
end
