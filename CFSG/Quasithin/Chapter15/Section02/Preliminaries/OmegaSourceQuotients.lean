module

public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallMixedRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.SourceBound

/-!
# Omega H-star quotients without the global Thompson residual

The original Omega rank-one witness already gives residual uniqueness.
Applying that uniqueness directly identifies both noncentral chief kernels
with O₂(H), so the single S₅ row forces |T| ≥ 2048, contrary to the proved
mixed A₅/S₃ bound 1024. The single S₃ row is excluded by the original
sixteen-element chosen module and the centered cubic amalgam bound eight.
Thus every actual Omega H-star quotient is S₃ wreath C₂, without invoking
15.1.14. The generic numerical and cubic exclusions retain explicit
residual uniqueness or its actual rank-one witness for other small rows.

Source: Aschbacher--Smith 15.1.12 and 15.2.5--8, printed pp.1090,
1107--1110; the mixed bound uses refs/groups-and-graphs.pdf as documented
in ChapterF.Source.MixedDGS.SourceBound.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChapterF.Source
open NoncentralChiefRefinement

private theorem five_factor_card {D W : Type*} [Group D] [AddCommGroup W]
    [Module (ZMod 2) W] {ρ : Representation (ZMod 2) D W}
    (ha : ChapterB.ChiefSmallWholeAction ρ) (hc : Nat.card D = 120) :
    Nat.card W = 16 := by
  unfold ChapterB.ChiefSmallWholeAction at ha
  rcases ha with ⟨hs,_⟩ | ⟨e⟩ | ⟨e⟩
  · have hb := hs.card_le_seventy_two
    omega
  · rw [Nat.card_congr e.some.linearEquiv.toEquiv,
      Module.natCard_eq_pow_finrank (K := ZMod 2),
      BinaryPermutation.finrank_natural_odd (Fin 5) (by decide)]
    norm_num
  · have hh := Nat.card_congr e.some.groupEquiv.toEquiv
    rw [hc,RegularWreathProduct.card,Nat.card_perm,Nat.card_fin] at hh
    norm_num [Nat.card_eq_fintype_card] at hh

variable {G : Type*} [Group G] [Finite G]

/-- Both actual faithful natural chief factors contribute to the orbit span.
Only literal residual uniqueness is needed, with no global Thompson premise. -/
theorem ChosenSmallSource.symmetricFive_span_card_of_residual_unique
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) :
    256 ≤ Nat.card (conjugateSpan H V) := by
  classical
  let := h.prepared.elementary
  let U := (conjugateSpan H V).subgroupOf H
  have hUH : conjugateSpan H V ≤ H := by
    rw [UniqueFactor.conjugateSpan_eq]
    exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H))
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hUH
  obtain ⟨s⟩ := SeriesOn.exists_series U
  obtain ⟨i,j,hij,hi,hj⟩ := h.two_faithful_chief_factors_of_residual_unique hunique hH s
  have hcard (k : Fin s.series.length)
      (hk : ¬ s.Central k ∧
        (Representation.BinaryOffender.actionHom (s.factorRepresentation k)).ker = pCore 2 H ∧
        ChapterB.ChiefSmallWholeAction
          (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation k))) :
      Nat.card (s.Factor k) = 16 := by
    let ρ := s.factorRepresentation k
    let q := Representation.BinaryOffender.actionHom ρ
    let e := (QuotientGroup.quotientKerEquivOfSurjective q ρ.asGroupHom.rangeRestrict_surjective).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hk.2.1).trans he.some)
    have hc : Nat.card (actionImage ρ) = 120 :=
      (Nat.card_congr e.toEquiv).trans (by
        simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial])
    change Nat.card (Additive (s.Factor k)) = 16
    exact five_factor_card hk.2.2 hc
  have hb : (∏ k ∈ ({i,j} : Finset (Fin s.series.length)), Nat.card (s.Factor k)) ≤
      ∏ k : Fin s.series.length, Nat.card (s.Factor k) :=
    Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _) (fun _ _ => Nat.zero_le _)
      (fun _ _ _ => Nat.card_pos)
  have hc := s.series.prod_card_section_mul_head
  rw [s.head_eq,s.last_eq] at hc
  change (∏ k : Fin s.series.length, Nat.card (s.Factor k)) * Nat.card (⊥ : Subgroup H) = Nat.card U at hc
  rw [card_bot,mul_one] at hc
  rw [←Nat.card_congr (subgroupOfEquivOfLe hUH).toEquiv,←hc]
  simpa [Finset.prod_pair hij,hcard i hi,hcard j hj] using hb

private theorem five_sylow_core_ratio {D : Type*} [Group D] [Finite D]
    (e : (D ⧸ pCore 2 D) ≃* Equiv.Perm (Fin 5)) (P : Sylow 2 D) :
    Nat.card P = 8 * Nat.card (pCore 2 D) := by
  have hq : Nat.card (D ⧸ pCore 2 D) = 120 :=
    (Nat.card_congr e.toEquiv).trans (by
      simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial])
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := D)).exists_card_eq
  have hc : Nat.card D = 120 * 2 ^ n := by
    rw [(pCore 2 D).card_eq_card_quotient_mul_card_subgroup,hq,hn]
  rw [P.card_eq_multiplicity,hc,hn,
    Nat.factorization_mul (by decide) (pow_ne_zero _ (by decide)),
    Nat.factorization_pow]
  have hf : (120 : ℕ).factorization 2 = 3 := by decide +kernel
  simp only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul,hf,
    Nat.prime_two.factorization,Finsupp.single_eq_same,mul_one]
  rw [pow_add]
  rfl

/-- The two chief factors give the original Sylow bound from local uniqueness. -/
theorem ChosenSmallSource.symmetricFive_sylow_card_of_residual_unique
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) :
    2048 ≤ Nat.card T := by
  have hUH : conjugateSpan H V ≤ H := by
    rw [UniqueFactor.conjugateSpan_eq]
    exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H))
  have hb := card_le_of_le (h.HStar_span_le_core hH)
  rw [Nat.card_congr (subgroupOfEquivOfLe hUH).toEquiv] at hb
  have hl := (h.symmetricFive_span_card_of_residual_unique hunique hH he).trans hb
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hc := five_sylow_core_ratio he.some (T.subtype hTH)
  have hcard : Nat.card (T.subtype hTH) = Nat.card T := by
    change Nat.card ((T : Subgroup G).subgroupOf H) = Nat.card T
    exact Nat.card_congr (subgroupOfEquivOfLe hTH).toEquiv
  rw [hcard] at hc
  omega

/-- A cubic rank-one witness excludes the single S₃ row directly: the
original chosen four-space exceeds the centered exceptional-amalgam bound. -/
theorem SmallResidualWitness.not_symmetricThree_of_cubic_direct
    {T : Sylow 2 G} {M Mc V Y₁ H : Subgroup G} {h : ChosenSmallSource T M Mc V}
    (hw : SmallResidualWitness h Y₁)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hquot : Nonempty (((Y₁ ⊔ (M ⊓ Mc).pCoreIn 2 : Subgroup G) ⧸
      pCore 2 (Y₁ ⊔ (M ⊓ Mc).pCoreIn 2 : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    ¬ Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) := by
  intro hthree
  let := h.prepared.elementary
  let U := (conjugateSpan H V).subgroupOf H
  have hUH : conjugateSpan H V ≤ H := by
    rw [UniqueFactor.conjugateSpan_eq]
    exact conjugateSpanBy_le_self ((h.prepared.inside_core H hH).trans (twoCore_le H))
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hUH
  let : U.Normal := normal_subgroupOf_of_le_normalizer (conjugateSpan_normalized H V)
  have hb := ChapterF.SourceAssembly.exceptional_centered_normal_elementary_card_le_eight
    (hw.cubic_symmetricThree_amalgam hH hthree hquot) (h.HStar_central_involution hH) U
  rw [Nat.card_congr (subgroupOfEquivOfLe hUH).toEquiv] at hb
  have hl : 16 ≤ Nat.card (conjugateSpan H V) := by
    rw [← h.card_eq_sixteen]
    apply card_le_of_le
    rw [UniqueFactor.conjugateSpan_eq]
    exact le_conjugateSpanBy _ _
  omega

/-- A cubic rank-one witness gives local residual uniqueness, so the actual
mixed bound excludes S₅ without the earlier global Thompson residual. -/
theorem SmallResidualWitness.not_symmetricFive_of_cubic_direct
    {T : Sylow 2 G} {M Mc V Y₁ H : Subgroup G} {h : ChosenSmallSource T M Mc V}
    (hw : SmallResidualWitness h Y₁)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hquot : Nonempty (((Y₁ ⊔ (M ⊓ Mc).pCoreIn 2 : Subgroup G) ⧸
      pCore 2 (Y₁ ⊔ (M ⊓ Mc).pCoreIn 2 : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    ¬ Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5)) := by
  intro hfive
  obtain ⟨hf,_,_,hk,_,_,_⟩ := hw.symmetricFive_mixed_inputs hH hfive
  have hu := MixedDGS.mixed_a5_s3_sylow_card_le_1024 hf hk hquot
  have hl := h.symmetricFive_sylow_card_of_residual_unique hw.residual_unique hH hfive
  omega

/-- Original 15.2.8 on every full or proper Omega support, using its actual
rank-one witness and no original 15.1.14 premise. -/
theorem ChosenSmallSource.HStar_wreath_of_omega
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ho : letI := h.prepared.elementary
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized)) :
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((H ⧸ pCore 2 H) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) := by
  let := h.prepared.elementary
  obtain ⟨Y₁,hle,hp,hne,hn,hm,hcentral,hquot⟩ := h.omega_rank_one_selection ho
  have hw := (h.smallResidualWitness_of_moved_selection (h.maximal_overgroups_of_omega ho)
    hle hp hne hn hm (Or.inl hquot) hcentral).1
  intro H hH
  exact ((h.HStar_quotient_of_source_omega ho hH).resolve_left
    (hw.not_symmetricThree_of_cubic_direct hH hquot)).resolve_right
    (hw.not_symmetricFive_of_cubic_direct hH hquot)

end CFSG.Quasithin.Chapter15.Section02
