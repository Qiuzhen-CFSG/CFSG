module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LocalOvergroups
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialExclusion
public import Theory.GroupTheory.Fitting.CyclicThreeSylow
public import Theory.GroupTheory.PResidual.NormalThreeLift
public import CFSG.Quasithin.ChapterA.Section01.RankActions.Supercritical
public import Theory.GroupTheory.PGroup.SupercriticalExistence

/-!
# The noncyclic three-core branch for the actual local family

Let J be any actual member of H_z. If J is solvable and every prime core
above three of J/O₂(J) vanishes, Fitting self-centralization and the local
Sylow order bound force its three-core to be noncyclic. Strong quasithinness
bounds its rank by two. A supercritical subgroup therefore has an actual
E₉ or order-27 Heisenberg marking. Taking the two-residual of its full
preimage constructs a subgroup normal in J, with precisely its intrinsic
two-core as quotient-action kernel and with the same model quotient.

The exhaustive solvable-local application leaves either a large-prime
core or these two normal lifts. At the original J = G₁, the completed
extraspecial exclusion forces a Heisenberg lift to be proper in O²(J).
It does not exclude proper Heisenberg lifts or identify them with K.
The large-prime exclusion, remaining ambient three-core analysis and
nonsolvability of every J remain to be proved before 14.7.27–29 close.

Source: Aschbacher–Smith, 14.7.6, 14.7.27–29, printed pp.1044–1045,
1054–1055; A.1.21 and A.1.25, printed pp.24–25, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- A solvable member of H_z with no large-prime core must have noncyclic three-core. -/
theorem local_solvable_threeCore_not_cyclic
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (hlarge : ∀ p : ℕ, p.Prime → 3 < p → pCore p (HStar J) = ⊥) :
    ¬ IsCyclic (pCore 3 (HStar J)) := by
  intro hc
  let := hs
  let := hc
  let S : Sylow 2 (HStar J) := Classical.choice inferInstance
  have hb := sylow_card_le_two_of_solvable_cyclic_threeCore
    (D := HStar J) inferInstance (pCore_quotient_pCore_eq_bot 2) hlarge S
  have hd := four_dvd_local_star_sylow_card h hab structural J hJ S
  have := Nat.le_of_dvd (Nat.card_pos (α := S)) hd
  omega

/-- The literal supercritical three-core has rank two, and its two-perfect
preimage has elementary-nine or Heisenberg quotient with the exact two-core kernel. -/
theorem local_noncyclic_threeCore_models
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hnc : ¬ IsCyclic (pCore 3 (HStar J))) :
    ∃ (X : Subgroup (pCore 3 (HStar J))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup J),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 J ∧
      Y.map (QuotientGroup.mk' (pCore 2 J)) = X.map (pCore 3 (HStar J)).subtype ∧
      ((QuotientGroup.mk' (pCore 2 J)).comp Y.subtype).ker = pCore 2 Y ∧
      (Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∨
        Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3)) := by
  let P := pCore 3 (HStar J)
  have hP : IsPGroup 3 P := pCore_isPGroup
  have hne : F.Vi 1 ≠ ⊥ := by
    intro he
    have hc := F.card 1 (by decide)
    rw [he,card_bot] at hc
    norm_num at hc
  have hH : IsTwoLocal F.H := ⟨F.Vi 1,hne,IsPGroup.of_card (p := 2) (n := 1) (F.card 1 (by decide)),rfl⟩
  have hJrank : primeRank 3 J ≤ 2 :=
    (Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion hJ.2.1) (inclusion_injective hJ.2.1)).trans
      ((h.source.simpleQTKE.twoLocal_sqtk hH).stronglyQuasithin 3 (by decide) (by decide))
  have hr : primeRank 3 P ≤ 2 := (primeRank_subgroup_le 3 P).trans
    ((primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 J) pCore_isPGroup).trans hJrank)
  let : Nontrivial P := by
    cases subsingleton_or_nontrivial P with
    | inl hs => let := hs; exact (hnc inferInstance).elim
    | inr ht => exact ht
  obtain ⟨X,hX⟩ := hP.exists_supercriticalPSubgroup (by decide : 3 ≠ 2)
  let : X.Characteristic := hX.characteristic
  let X₀ := X.map P.subtype
  let : X₀.Characteristic := inferInstance
  obtain ⟨Y,hYn,hYp,hYle,hYm,hYk,⟨e⟩⟩ := Subgroup.exists_normal_three_residual_lift
    (QuotientGroup.mk' (pCore 2 J)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) X₀ (hP.to_subgroup X |>.map P.subtype)
  let eX : X ≃* X₀ := equivMapOfInjective X P.subtype P.subtype_injective
  refine ⟨X,hX,Y,hYn,hYp,hYle,hYm,hYk,?_⟩
  rcases (ChapterA.lemma_A_1_25_1 (by decide) hP hr X hX).2 with hc | hm | hm
  · have hrX : primeRank 3 X ≤ 1 := (primeRank_le_iff_elementary_card_le X).mpr
      (fun E _ => by simpa only [pow_one,hc.1] using (card_le_card_group E))
    have hrP := hX.primeRank_le_one_of_rank_le_one hP (by decide) hrX
    exact (hnc (hP.isCyclic_of_odd_of_elementary_card_le (by decide)
      (fun E hE => by
        let := hE
        exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hrP E))).elim
  · exact Or.inl ⟨e.trans (eX.symm.trans hm.2.some)⟩
  · exact Or.inr ⟨e.trans (eX.symm.trans hm.2.2.some)⟩

/-- The source solvable-local branch has an actual normal residual lift of one
of the two noncyclic supercritical models; no model-recognition premise is assumed. -/
theorem local_solvable_threeCore_models
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (hlarge : ∀ p : ℕ, p.Prime → 3 < p → pCore p (HStar J) = ⊥) :
    ∃ (X : Subgroup (pCore 3 (HStar J))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup J),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 J ∧
      Y.map (QuotientGroup.mk' (pCore 2 J)) = X.map (pCore 3 (HStar J)).subtype ∧
      ((QuotientGroup.mk' (pCore 2 J)).comp Y.subtype).ker = pCore 2 Y ∧
      (Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∨
        Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3)) := by
  exact local_noncyclic_threeCore_models h J hJ
    (local_solvable_threeCore_not_cyclic h hab structural J hJ hs hlarge)

/-- An exhaustive reduction for any actual solvable overgroup: either a
large-prime core survives, or one of the two noncyclic three-core models has
an actual normal two-perfect lift. The large-prime exclusion and the ambient
exclusion of these lifts remain the subsequent source obligations. -/
theorem local_solvable_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    (∃ p : ℕ, p.Prime ∧ 3 < p ∧ pCore p (HStar J) ≠ ⊥) ∨
    ∃ (X : Subgroup (pCore 3 (HStar J))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup J),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 J ∧
      Y.map (QuotientGroup.mk' (pCore 2 J)) = X.map (pCore 3 (HStar J)).subtype ∧
      ((QuotientGroup.mk' (pCore 2 J)).comp Y.subtype).ker = pCore 2 Y ∧
      (Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∨
        Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3)) := by
  by_cases hp : ∃ p : ℕ, p.Prime ∧ 3 < p ∧ pCore p (HStar J) ≠ ⊥
  · exact Or.inl hp
  have hlarge : ∀ p : ℕ, p.Prime → 3 < p → pCore p (HStar J) = ⊥ := by
    intro p hprime hgt
    by_contra hn
    exact hp ⟨p,hprime,hgt,hn⟩
  exact Or.inr (local_solvable_threeCore_models h hab structural J hJ hs hlarge)

/-- At the original point normalizer the completed extraspecial exclusion
makes every Heisenberg lift proper in O²(H). The other alternatives retain
their literal normal lift and quotient kernel. -/
theorem original_solvable_reduction
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : Chapter14.Section04.LargerDimension.LocalAction.Components.EarlierFaithfulClassification
      G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (hs : Group.IsSolvable F.H) :
    (∃ p : ℕ, p.Prime ∧ 3 < p ∧ pCore p (HStar F.H) ≠ ⊥) ∨
    ∃ (X : Subgroup (pCore 3 (HStar F.H))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup F.H),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 F.H ∧
      Y.map (starMap F) = X.map (pCore 3 (HStar F.H)).subtype ∧
      ((starMap F).comp Y.subtype).ker = pCore 2 Y ∧
      (Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∨
        (Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3) ∧ Y < pResidual 2 F.H)) := by
  rcases local_solvable_reduction h hab structural F.H
    (F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)) hs with hp | hm
  · exact Or.inl hp
  obtain ⟨X,hX,Y,hYn,hYp,hYle,hYm,hYk,hm⟩ := hm
  refine Or.inr ⟨X,hX,Y,hYn,hYp,hYle,hYm,hYk,?_⟩
  rcases hm with hm | hm
  · exact Or.inl hm
  refine Or.inr ⟨hm,lt_of_le_of_ne hYle ?_⟩
  intro heq
  have hh : Nonempty (((pResidual 2 F.H) ⧸ pCore 2 (pResidual 2 F.H)) ≃*
      HeisenbergPrime 3) := heq ▸ hm
  let e : pResidual 2 F.H ≃* K F :=
    equivMapOfInjective (pResidual 2 F.H) F.H.subtype F.H.subtype_injective
  let eQ := QuotientGroup.congr (pCore 2 (pResidual 2 F.H)) (pCore 2 (K F)) e
    (pCore_map_iso 2 e)
  exact extraspecial_residual_impossible d h hab structural previous faithful earlier
    ⟨eQ.symm.trans hh.some⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
