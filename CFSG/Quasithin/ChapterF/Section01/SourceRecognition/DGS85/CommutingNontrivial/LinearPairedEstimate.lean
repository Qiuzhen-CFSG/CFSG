module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ResidualNaturalExclusion

/-!
# The first paired square estimate in the linear ending branch

For the original counterexample configuration in DGS (8.3), the natural
residual alternative has been excluded on a large-field linear ending
quotient. If the full opposite actor has order at least four, its fixed
space agrees with that of the nontrivial image of Z_alpha. Since Q_alpha
centralizes Z_alpha, the residual fixed-space index is at most the original
core index a₂ b₂. The paired core-index geometry bounds b₂ by the moving
unitary field size. Actors of order at most two satisfy the final inequality
directly, since that field has order at least four.

All subgroups, quotient maps and actions come from the reduced F1.11 graph.
The earlier local obstruction and actual source catalogue remain explicit.
The reverse paired estimate and nonlinear ending rows are not asserted.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
proof of (8.3), p.136, first inequality of (2).
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.NormalElementaryQuotient Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph CommutingTrivial
universe u
variable {G : Type u} [Group G] {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The first source comparison a₁² ≤ a₂ q_lambda, with the actual
large-field linear ending quotient and moving unitary field retained. -/
theorem reduced_counterexample_linear_first_paired_square
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (w : (graph (Reduction.reducedFamily J S₀)).neighborSet a')
    (hm : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      Z (Reduction.reducedFamily J S₀) w.val⁆ ≠ ⊥)
    (R : Sylow 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val))
    (hR : (R : Subgroup (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)).map
      (graphLocalGroup (Reduction.reducedFamily J S₀) w.val).subtype =
        (stabilizer (Reduction.reducedFamily J S₀) w.val ⊓ stabilizer (Reduction.reducedFamily J S₀) a').pCoreIn 2)
    (hbad : ¬ ⁅quotientSylowOmegaPreimage (graphLocalGroup (Reduction.reducedFamily J S₀) w.val) R,
      Z (Reduction.reducedFamily J S₀) w.val⁆ ≤
        ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
          V (Reduction.reducedFamily J S₀) a' 1⁆)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) ≃* SL(2,K))
    (m : ℕ) (hm2 : 2 ≤ m)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup (Reduction.reducedFamily J S₀) w.val ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)) 3 (2^m) ∨
      IsSU (graphLocalGroup (Reduction.reducedFamily J S₀) w.val ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)) 3 (2^m)) :
    let F := Reduction.reducedFamily J S₀
    Nat.pow ((Q F a').relIndex (V F beta 1)) 2 ≤ (Q F beta).relIndex (V F a' 1) * 2^m := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let L := graphLocalGroup F a'
  let U := (V F a' 1).subgroupOf L
  let E := (pResidual 2 L).map L.subtype
  let D := E ⊔ Q F w.val
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let : U.Normal := neighborhoodIn_normal F a' L (sylowGenerated_le _)
  obtain ⟨hb2,hDL,eD,σ,heD,hact,⟨c⟩,hlower,hupper⟩ :=
    reduced_counterexample_linear_residual_fixed_square h hob models hc hab hd hb hcomm w hm R hR hbad hn hK e
  let : IsElementaryAbelian 2 U := neighborhoodIn_elementary F ht.generate
    (fun v => (source_Z_Q_U ht v).1) (Reduction.reduced_kernel_sylow h) a' hb2 L
  let W := FixedQuotient U (pResidual 2 L)
  let : Finite L := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite D := Finite.of_injective (inclusion hDL) (inclusion_injective _)
  let : Finite (V F a' 1) := Finite.of_injective (inclusion c.section_le) (inclusion_injective _)
  let : Finite W := Finite.of_surjective (fun x : V F a' 1 => (c.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  let : Finite (graphLocalGroup F w.val) :=
    Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hrank : primeRank 2 (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≤ m := by
    change primeRank 2 (graphLocalGroup F w.val ⧸ pCore 2 (graphLocalGroup F w.val)) ≤ m
    rcases hu with hu | hu
    · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
      let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
        Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
      rw [primeRank_congr 2 e]
      exact (BenderSuzuki.MatrixGroups.HermitianForm.EvenTwoRank.two_rank J (by omega) hK hconj).le
    · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
      let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
        Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
      rw [primeRank_congr 2 e,primeRank_eq_of_surjective_of_coprime 2 J.specialToProjective
        J.specialToProjective_surjective J.odd_card_specialToProjective_ker.coprime_two_left]
      exact (BenderSuzuki.MatrixGroups.HermitianForm.EvenTwoRank.two_rank J (by omega) hK hconj).le
  obtain ⟨_,hprod,_,hb2bound⟩ := source_paired_core_indices ht
    (Reduction.reduced_borel_core_sylow h) d hc hab hd hb hcomm models w hm m hrank
  let a₁ := (Q F a').relIndex (V F beta 1)
  let a₂ := (Q F beta).relIndex (V F a' 1)
  have ha₂ : 0 < a₂ := Nat.pos_of_ne_zero (((Q F beta).subgroupOf (V F a' 1)).index_ne_zero_of_finite)
  by_cases hsmall : a₁ ≤ 2
  · have hq4 : 4 ≤ 2^m := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hm2
    change a₁^2 ≤ a₂ * 2^m
    nlinarith
  obtain ⟨_,hDL',eD',τ,T,heD',hact',hAD,hAT,hcardA,hquad,hfaith,hgen,_,_,_⟩ :=
    reduced_counterexample_linear_residual_recognition h hob models hc hab hd hb hcomm w hm R hR hbad hn hK e
  have heq : eD = eD' := by
    apply MulEquiv.ext
    intro x
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 D) x
    exact (heD g).trans (heD' g).symm
  have hσ : σ = τ := by
    apply MonoidHom.ext
    intro x
    apply LinearMap.ext
    intro z
    obtain ⟨g,rfl⟩ := (eD.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 D))) x
    change σ (eD (QuotientGroup.mk' (pCore 2 D) g)) z = τ (eD (QuotientGroup.mk' (pCore 2 D) g)) z
    exact (congrArg (fun f => f z) (hact g)).trans
      ((congrArg (fun f => f z) (hact' g)).symm.trans
        (congrArg (fun x => τ x z)
          (congrArg (fun E => E (QuotientGroup.mk' (pCore 2 D) g)) heq.symm)))
  rw [←heq] at hAT hcardA hquad
  rw [←hσ] at hquad hgen
  let π := eD.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D))
  let A := ((V F beta 1).subgroupOf D).map π
  let A₀ := ((Z F a).subgroupOf D).map π
  have hZV : Z F a ≤ V F beta 1 := Z_neighbor_le_V F hab.symm
  have hZD : Z F a ≤ D := hZV.trans hAD
  have hA₀A : A₀ ≤ A := map_mono (comap_mono hZV)
  have hA4 : 4 ≤ Nat.card A := by
    obtain ⟨r,hr⟩ := (T.isPGroup'.to_le hAT).exists_card_eq
    change Nat.card A = 2^r at hr
    have hbig : 2 < Nat.card A := by
      rw [hcardA]
      exact Nat.lt_of_not_ge hsmall
    have hr2 : 2 ≤ r := by
      by_contra! hh
      have hr' : r = 0 ∨ r = 1 := by omega
      rcases hr' with rfl | rfl
      · norm_num only [pow_zero] at hr
        omega
      · norm_num only [pow_one] at hr
        omega
    rw [hr]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hr2
  have hA₀ : A₀ ≠ ⊥ := by
    intro hz
    have hk := (Subgroup.map_eq_bot_iff _).mp hz
    apply hc.2
    apply le_trans ?_ (source_Z_Q_U ht a').2
    intro z hz
    have hzero : π ⟨z,hZD hz⟩ = 1 := hk hz
    have he := (heD ⟨z,hZD hz⟩).symm.trans hzero
    have hcore : inclusion hDL (⟨z,hZD hz⟩ : D) ∈ pCore 2 L :=
      (QuotientGroup.eq_one_iff _).mp (e.map_eq_one_iff.mp he)
    have heq : (pCore 2 L).map L.subtype = Q F a' := graphLocalGroup_core ht a'
    exact heq.le (mem_map_of_mem L.subtype hcore)
  obtain ⟨t,ht₀,ht1⟩ := A₀.bot_or_exists_ne_one.resolve_left hA₀
  have hgenA : GeneratedByFixedSpace σ A := by
    apply top_unique
    rw [←hgen]
    apply iSup_mono
    intro g
    exact Submodule.map_mono (fixedSpace_antitone σ hAT)
  have hfixed : fixedSpace σ A = fixedSpace σ A₀ := by
    apply le_antisymm (fixedSpace_antitone σ hA₀A)
    exact (fixedSpace_antitone σ (zpowers_le.mpr ht₀)).trans_eq
      (sl2_quadratic_fixedSpace_eq σ (by omega : 0 < n) hK T A hAT hA4 hquad hgenA t (hA₀A ht₀) ht1).symm
  have hcentral := BinaryConjugationSection.fixed_quotient_card_le_centralizer_index σ π c (Z F a)
  change Nat.card (W ⧸ fixedSpace σ A₀) ≤ _ at hcentral
  have hQa : Q F a ≤ centralizer (Z F a : Set (Reduction.G₀ J S₀)) :=
    le_centralizer_iff.mp (Z_centralizes_Q F a (source_Z_Q_U ht a).1)
  have hind := relIndex_le_of_le_left hQa (((Q F a).subgroupOf (V F a' 1)).index_ne_zero_of_finite)
  have htot : a₁^2 ≤ (Q F a).relIndex (V F a' 1) := by
    change a₁^2 ≤ Nat.card (W ⧸ fixedSpace σ A) at hlower
    rw [hfixed] at hlower
    exact hlower.trans (hcentral.trans hind)
  change (Q F beta).relIndex (V F a' 1) * (Q F a).relIndex (V F a' 1 ⊓ Q F beta) =
    (Q F a).relIndex (V F a' 1) at hprod
  rw [←hprod] at htot
  exact htot.trans (Nat.mul_le_mul_left _ hb2bound)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
