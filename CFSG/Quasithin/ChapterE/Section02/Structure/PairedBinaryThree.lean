module
public import CFSG.Quasithin.ChapterE.Section02.Structure.PairedCore
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.SpecificGroups.Classical.EvenDerivedThree
public import Theory.GroupTheory.TwoOrbitThree.Quotient
public import Theory.GroupTheory.PResidual.PrimeToTransport

/-!
# Cubic rank and three-generation of the original binary pair

The two-core-free quotient of the original exchanged minimal parabolic has
an actual direct product of two conjugate simple factors. A binary PSL₂
factor has order divisible by three, so additivity of rank gives cubic rank
at least two for the full two-residual. Two-group kernels preserve that rank.
The original index-two component normalizer and the binary outer calculation
also identify O²(H) with O^{3′}(H), and with its own prime-to-three residual.
These are the full paired inputs used after the binary row selection in
14.2.15; they do not assert cubic rank for the Suzuki alternative.

Source: Aschbacher--Smith E.2.2(1), 1.2.2(a), and 14.2.15,
printed pp.215--216, 504, and 985--986.
-/

public section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Structure
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

private noncomputable def quotientImageEquivOfEq (N D : Subgroup H) [N.Normal] [D.Normal]
    (he : N = D) (K : Subgroup H) :
    K.map (QuotientGroup.mk' N) ≃* K.map (QuotientGroup.mk' D) := by
  subst D
  exact MulEquiv.refl _

theorem source_paired_binary_residual_three_rank
    (hA : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremA κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable H)
    {K : Subgroup H} (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬ K.Normal)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (eK : (K ⧸ pCore 2 K) ≃* PSL(2,F)) :
    2 ≤ primeRank 3 (pResidual 2 H) := by
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let : Group.IsSolvable J := ChapterB.minimalParabolic_core_solvable T hP
  have hJ : J = pCore 2 H := PairedCore.source hA hH T hP hs hK hqK hgen hn
  have hi := source_component_simple_image T hP hs K hK hgen
  let B := K.map q
  have hB : B.IsCComponent := hK.map_quotient J
  have hnot : ¬ B.Normal := fun hh => hn (cComponent_normal_of_quotient_normal hK J hh)
  have eB : (K ⧸ pCore 2 K) ≃* B := by
    exact (cComponentTwoCoreQuotientEquiv hK).trans
      (quotientImageEquivOfEq J (pCore 2 H) hJ K).symm
  have hthree : 3 ∣ Nat.card B := by
    rw [← Nat.card_congr eB.toEquiv, Nat.card_congr eK.toEquiv]
    exact (Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_psl_commutator
      (F := F) (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)).trans
      (card_subgroup_dvd_card _)
  have hpos : 0 < primeRank 3 B :=
    Nat.pos_of_ne_zero (fun hh => PrimeRank.eq_zero_iff_not_dvd_card.mp hh hthree)
  obtain ⟨t,_,_,_,hR,⟨d,_⟩,_,_⟩ := source_pair_coordinates
    (source_star_sqtk (hA H) hH T hP hs).stronglyQuasithin S
    (source_star_minimal_core_free T hP).1
    (fun hh => hs ((Group.isSolvable_iff_subgroup_quotient J).mpr ⟨inferInstance,hh⟩))
    (source_star_minimal_core_free T hP).2 hi.2.1 hB hi.2.2.2 hnot
  let D := B.map (MulAut.conj (t : H ⧸ J)).toMonoidHom
  have he : primeRank 3 B = primeRank 3 D :=
    primeRank_equiv 3 ((MulAut.conj (t : H ⧸ J)).subgroupMap B)
  have hr : 2 ≤ primeRank 3 (pResidual 2 (H ⧸ J)) := by
    rw [hR, ← primeRank_equiv 3 d, primeRank_prod_eq_add]
    change 2 ≤ primeRank 3 B + primeRank 3 D
    omega
  have hupper : primeRank 3 (H ⧸ J) ≤ primeRank 3 H := by
    rw [primeRank_equiv 3 (QuotientGroup.quotientMulEquivOfEq hJ)]
    exact primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup
  rw [ResidualCentralizerRank.primeRank_residual (by decide : Nat.Coprime 2 3)] at hr ⊢
  exact hr.trans hupper

/-- The whole binary pair is also the prime-to-three residual. -/
theorem source_paired_binary_residual_eq_threeResidual
    (hA : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremA κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable H)
    {K : Subgroup H} (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬ K.Normal)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (eK : (K ⧸ pCore 2 K) ≃* PSL(2,F)) :
    pResidual 2 H = primeToResidual 3 H := by
  let J := ChapterB.minimalParabolicCore T hP
  let : Group.IsSolvable J := ChapterB.minimalParabolic_core_solvable T hP
  have hJ : J = pCore 2 H := PairedCore.source hA hH T hP hs hK hqK hgen hn
  have him := source_component_simple_image T hP hs K hK hgen
  let eB := (cComponentTwoCoreQuotientEquiv hK).trans
    (quotientImageEquivOfEq J (pCore 2 H) hJ K).symm
  let : IsSimpleGroup (K.map (QuotientGroup.mk' J)) := him.1
  let : IsSimpleGroup (K ⧸ pCore 2 K) := eB.isSimpleGroup
  let := hqK
  let : Group.IsPerfect K := hK.perfect
  have hp : IsPPerfect 2 K := by
    intro N hN hquot
    let := hN
    have hsub : Subsingleton (K ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (K ⧸ N) hquot.isNilpotent
    apply eq_top_iff.mpr
    intro k _
    exact (QuotientGroup.eq_one_iff k).mp (Subsingleton.elim _ _)
  have hd : 3 ∣ Nat.card (K ⧸ pCore 2 K) := by
    rw [Nat.card_congr eK.toEquiv]
    exact (Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_psl_commutator
      (F := F) (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)).trans
      (card_subgroup_dvd_card _)
  have hKR : K ≤ primeToResidual 3 H := le_primeToResidual_of_eq_top 3 K
    (primeToResidual_eq_top_of_simple_quotient 3 2 (pCore 2 K) pCore_isPGroup hp hd)
  have hKD : K ≤ pResidual 2 H := le_pResidual_of_isPPerfect K hp
  have hi : (normalizer (K : Set H)).index = 2 :=
    (cComponent_normalizer_index_quotient hK J).symm.trans
      ((him.2.1.normal_or_index_two_of_odd_rank_le_two
        (source_star_sqtk (hA H) hH T hP hs).stronglyQuasithin).resolve_left
        (fun hh => hn (cComponent_normal_of_quotient_normal hK J hh)))
  have hnt : ¬(T : Subgroup H) ≤ normalizer (K : Set H) := by
    intro hh
    exact hn (normalizer_eq_top_iff.mp
      (top_unique (hgen ▸ sup_le K.le_normalizer hh)))
  obtain ⟨t,_,ht⟩ := SetLike.not_le_iff_exists.mp hnt
  let P := K ⊔ K.conjBy t
  let : P.Normal := TwoOrbitThree.pair_normal_of_index_two K hi t ht
  have hPT : P ⊔ (T : Subgroup H) = ⊤ := top_unique (by
    rw [←hgen]
    exact sup_le_sup le_sup_left le_rfl)
  have hDP : pResidual 2 H ≤ P := sInf_le
    ⟨inferInstance,isPGroup_quotient_of_sup_eq_top P (T : Subgroup H) T.isPGroup' hPT⟩
  have hPD : P ≤ pResidual 2 H := by
    refine sup_le hKD ?_
    rintro x ⟨k,hk,rfl⟩
    exact (inferInstance : (pResidual 2 H).Normal).conj_mem k (hKD hk) t
  have hPR : P ≤ primeToResidual 3 H := by
    refine sup_le hKR ?_
    rintro x ⟨k,hk,rfl⟩
    exact (inferInstance : (primeToResidual 3 H).Normal).conj_mem k (hKR hk) t
  have hRP : primeToResidual 3 H ≤ P := primeToResidual_le P
    (TwoOrbitThree.binary_cComponent_pair_index_coprime_three hK hi t ht hd
      (hH.stronglyQuasithin 3 (by decide) (by decide)) F eK)
  exact (le_antisymm hDP hPD).trans (le_antisymm hPR hRP)

/-- The original full binary pair is generated by its elements of three-power order. -/
theorem source_paired_binary_residual_three_generated
    (hA : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremA κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable H)
    {K : Subgroup H} (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬ K.Normal)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (eK : (K ⧸ pCore 2 K) ≃* PSL(2,F)) :
    primeToResidual 3 (pResidual 2 H) = ⊤ := by
  have he := source_paired_binary_residual_eq_threeResidual hA hH T hP hs hK hqK hgen hn eK
  have hh := embedded_primeToResidual_eq_of_normal 3 (pResidual 2 H) he.symm.le
  apply Subgroup.map_injective (pResidual 2 H).subtype_injective
  simpa only [he.symm,←MonoidHom.range_eq_map,range_subtype] using hh

end CFSG.Quasithin.ChapterE.Structure
