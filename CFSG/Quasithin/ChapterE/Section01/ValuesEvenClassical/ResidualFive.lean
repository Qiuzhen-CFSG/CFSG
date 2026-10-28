module
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions.PSL2.ElementaryLift
public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.JankoTwo.FiveQuotients
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.QuotientFamily
public import Theory.SpecificGroups.Alternating.FiveTwoCoreExtension
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.PrimeRankFixedJoin
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels

/-!
# Generation in the original group with an A5 residual quotient

A Sylow two-subgroup supplements the actual two-residual. Its core quotient
is A5 or S5, so E-generation at two lifts through the whole two-core. The
positive parameter is therefore one or two. An elementary subgroup of the
residual whose image under the ambient core quotient has order four gives
the lower obstruction of `ElementaryLift`, hence parameter two upstairs.

Conversely, in the remaining parameter-one case every elementary subgroup
of that same residual has image of order at most two. All assertions use
the literal residual, intrinsic core and ambient quotient maps. The
existence of an elementary lift is not inferred from the quotient model.

Source: Aschbacher--Smith E.1.7, E.1.14(1) and the nonsolvable step of
13.2.8(1), printed pp.210,214,880. This supplies a sufficient lower-bound
argument, not the disputed general numerical equality across a core.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.ResidualFive
variable {G : Type*} [Group G] [Finite G]

theorem generation_two_of_residual_A5 (S : Sylow 2 G)
    (e : (pResidual 2 G ⧸ pCore 2 (pResidual 2 G)) ≃* alternatingGroup (Fin 5)) :
    IsEGenerated 2 G := by
  let R := pResidual 2 G
  have hn : (S : Subgroup G) ≤ normalizer (R : Set G) := by
    rw [R.normalizer_eq_top]
    exact le_top
  have hm := Theory.SpecificGroups.Alternating.FiveExtensionAction.core_quotient_of_two_supplement
    R (S : Subgroup G) hn S.isPGroup' e
  change Nonempty (((pResidual 2 G ⊔ (S : Subgroup G) : Subgroup G) ⧸
    pCore 2 (pResidual 2 G ⊔ (S : Subgroup G) : Subgroup G)) ≃* alternatingGroup (Fin 5)) ∨
    Nonempty (((pResidual 2 G ⊔ (S : Subgroup G) : Subgroup G) ⧸
    pCore 2 (pResidual 2 G ⊔ (S : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 5)) at hm
  rw [pResidual_sup_sylow_eq_top S] at hm
  let t : (⊤ : Subgroup G) ≃* G := topEquiv
  let tq := QuotientGroup.congr _ _ t (pCore_map_iso 2 t)
  apply IsEGenerated.of_normal_two_subgroup (pCore 2 G) pCore_isPGroup
  rcases hm with hm | hm
  · obtain ⟨a⟩ := hm
    exact JankoTwo.alternating_five_isEGenerated.map_equiv (tq.symm.trans a).symm
  · obtain ⟨a⟩ := hm
    exact JankoTwo.symmetric_five_isEGenerated.map_equiv (tq.symm.trans a).symm

/-- The lower obstruction uses an actual elementary subgroup of the residual,
with image order four under the ambient two-core quotient. -/
theorem not_generation_one_of_residual_A5_lift
    (e : (pResidual 2 G ⧸ pCore 2 (pResidual 2 G)) ≃* alternatingGroup (Fin 5))
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAR : A ≤ pResidual 2 G)
    (hcard : Nat.card (A.map (QuotientGroup.mk' (pCore 2 G))) = 4) :
    ¬ IsEGenerated 1 G := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let D := (pResidual 2 G).map q
  let ed : D ≃* alternatingGroup (Fin 5) := (coreQuotientEquivImage 2 (pResidual 2 G)).symm.trans e
  let : D.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : IsSimpleGroup D := ed.isSimpleGroup
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective
    (f := ed.symm.toMonoidHom) ed.symm.surjective
  have hAD : A.map q ≤ D := map_mono hAR
  let B := (A.map q).subgroupOf D
  let : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map q
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hAD
  have hcD : Nat.card D = 60 := (Nat.card_congr ed.toEquiv).trans (by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial])
  have hcB : Nat.card B = 4 := (Nat.card_congr (subgroupOfEquivOfLe hAD).toEquiv).trans hcard
  let P : Sylow 2 D := Sylow.ofCard B (by
    rw [hcB,hcD,show (60 : ℕ).factorization 2 = 2 from by
      rw [show 60 = 2 ^ 2 * 15 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),Nat.factorization_pow]
      simp [Nat.prime_two.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 15)]]
    norm_num)
  have hP : ChapterF.Source.RankOneSylowFacts P := by
    apply ChapterF.Source.IsRankOneModel.rankOneSylowFacts
    apply ChapterF.Source.IsRankOneModel.linear 2 (by decide)
    have hF : Nat.card (GaloisField 2 2) = 4 := GaloisField.card 2 2 (by decide)
    obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
    exact ⟨GaloisField 2 2,inferInstance,inferInstance,hF,⟨ed.trans a.symm⟩⟩
  apply ValuesEvenClassical.not_isEGenerated_of_rankOne_quotient_lift q
    (QuotientGroup.mk'_surjective _) D (Group.IsPerfect.not_isSolvable D) P
    (fun K hPK hK => hP.unique_maximal K hPK (lt_top_iff_ne_top.mpr hK)) hP.proper.ne A
  · exact (map_subgroupOf_eq_of_le hAD).symm
  · have hr : 2 ≤ Group.rank B := IsElementaryAbelian.rank_ge_of_card (p := 2) hcB
    change 1 < Group.rank B
    omega

/-- Positive attainment and the upper bound use the original group, not
its quotient parameter. -/
theorem parameter_bounds (S : Sylow 2 G)
    (e : (pResidual 2 G ⧸ pCore 2 (pResidual 2 G)) ≃* alternatingGroup (Fin 5)) :
    1 ≤ generationParameter G ∧ generationParameter G ≤ 2 := by
  have hg := generation_two_of_residual_A5 S e
  have hc : Nat.card (pResidual 2 G ⧸ pCore 2 (pResidual 2 G)) = 60 :=
    (Nat.card_congr e.toEquiv).trans (by rw [nat_card_alternatingGroup]; norm_num [Nat.factorial])
  have hd := (pCore 2 (pResidual 2 G)).index_dvd_card
  rw [index_eq_card,hc] at hd
  have heven : 2 ∣ Nat.card G :=
    ((show 2 ∣ 60 by decide).trans hd).trans (card_subgroup_dvd_card (pResidual 2 G))
  have hspec := generationParameter_spec (fun ho => ho.not_two_dvd_nat heven)
    ⟨2,by decide,hg⟩
  exact ⟨hspec.1,generationParameter_le (by decide) hg⟩

/-- For the original group the parameter is exactly two once its literal
elementary Sylow lift is supplied. -/
theorem parameter_two_of_residual_A5_lift (S : Sylow 2 G)
    (e : (pResidual 2 G ⧸ pCore 2 (pResidual 2 G)) ≃* alternatingGroup (Fin 5))
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAR : A ≤ pResidual 2 G)
    (hcard : Nat.card (A.map (QuotientGroup.mk' (pCore 2 G))) = 4) :
    generationParameter G = 2 := by
  obtain ⟨hl,hu⟩ := parameter_bounds S e
  have hn := not_generation_one_of_residual_A5_lift e A hAR hcard
  have hne : generationParameter G ≠ 1 := by
    intro he
    apply hn
    simpa only [he] using isEGenerated_generationParameter_of_pos (by omega :
      0 < generationParameter G)
  omega

/-- In the remaining parameter-one branch, every elementary subgroup of
the actual residual has at most two elements in its ambient core image. -/
theorem residual_elementary_image_card_le_two (S : Sylow 2 G)
    (e : (pResidual 2 G ⧸ pCore 2 (pResidual 2 G)) ≃* alternatingGroup (Fin 5))
    (hn : generationParameter G ≤ 1)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAR : A ≤ pResidual 2 G) :
    Nat.card (A.map (QuotientGroup.mk' (pCore 2 G))) ≤ 2 := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let D := (pResidual 2 G).map q
  let ed : D ≃* alternatingGroup (Fin 5) :=
    (coreQuotientEquivImage 2 (pResidual 2 G)).symm.trans e
  have hAD : A.map q ≤ D := map_mono hAR
  let B := (A.map q).subgroupOf D
  let : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map q
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hAD
  obtain ⟨P,hBP⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_le_sylow
  have hcD : Nat.card D = 60 := (Nat.card_congr ed.toEquiv).trans (by
    rw [nat_card_alternatingGroup]; norm_num [Nat.factorial])
  have hcP : Nat.card P = 4 := by
    have hh := P.card_eq_multiplicity
    rw [hcD,show (60 : ℕ).factorization 2 = 2 from by
      rw [show 60 = 2 ^ 2 * 15 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),Nat.factorization_pow]
      simp [Nat.prime_two.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 15)]] at hh
    exact hh
  have hcB : Nat.card B = Nat.card (A.map q) := Nat.card_congr (subgroupOfEquivOfLe hAD).toEquiv
  have hd := card_dvd_of_le hBP
  rw [hcP,hcB] at hd
  have hne : Nat.card (A.map q) ≠ 4 := by
    intro hc
    have hh := parameter_two_of_residual_A5_lift S e A hAR hc
    omega
  have hb := Nat.le_of_dvd (by decide : 0 < 4) hd
  change Nat.card (A.map q) ≤ 2
  generalize Nat.card (A.map q) = n at hd hne hb ⊢
  interval_cases n <;> simp_all

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.ResidualFive
