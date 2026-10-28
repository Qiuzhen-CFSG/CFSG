module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ReselectionSp4
public import Theory.Quasithin.CoprimeRank
public import Theory.Representation.SU3.BinaryDegree.ProjectiveOrder

/-!
# Exceptional maximal overcomponents of the field-four triangle

The three recognized quotients SL₃(4), Sp₄(4), G₂(4) constrain the intrinsic
two-core quotient of any containing subgroup by order divisibility. With
cubic rank two and quasisimplicity, the field-four catalogue reduces to
3.M₂₂, J₂, J₄ and Rudvalis. No arbitrary quotient-rank monotonicity is used.

The 3.M₂₂ row is also excluded for the original join of two normalized
local A₅ sections: their images in M₂₂ coincide and have order 960. Only
the SL₃(4) row survives the ambient order comparison, and its factor seven
survives the literal two-core and central cubic projections, a contradiction.
MaximalSieveSp4 applies both comparisons to the actual common-Q join.

Source: Aschbacher--Smith, 1.2.8(4), A.3.12--14 and 11.1.2,
printed pp.47--50,507,762--764. Imported model calculations retain their
existing ATLAS attribution and certificate provenance.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
open Chapter1.Section02.LocalModels
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
public noncomputable section

private theorem triangle_order {A : Type*} [Group A]
    (hm : Source.IsSL A 3 4 ∨ Source.IsSp A 2 4 ∨ ClassificationModels.IsG2At A 4) :
    Nat.card A = 60480 ∨ Nat.card A = 979200 ∨ Nat.card A = 251596800 := by
  rcases hm with hm | hm | hm
  · left
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv,
      card_eq_card_quotient_mul_card_subgroup (center (Matrix.SpecialLinearGroup (Fin 3) F)),
      Atlas.ExceptionalSupport.card_sl_center]
    change Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) * _ = _
    rw [Matrix.PSL3.LinearThree.card_projective,hF]
    norm_num
  · right; left
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv,Theory.SpecificGroups.SymplecticFour.card_sp,hF]
    norm_num
  · right; right
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv,Atlas.G2.card_Model,hF]
    norm_num

private theorem core_quotient_card_dvd {G : Type*} [Group G] [Finite G]
    {I J : Subgroup G} (hIJ : I ≤ J) :
    Nat.card (I ⧸ pCore 2 I) ∣ Nat.card (J ⧸ pCore 2 J) := by
  let B := I.subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  let e := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hIJ)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hIJ))
  have hk : IsPGroup 2 (q.subgroupMap B).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let a := MonoidHom.quotientPCoreEquivOfSurjective
    (q.subgroupMap B) (q.subgroupMap_surjective B) hk
  rw [←Nat.card_congr e.toEquiv,Nat.card_congr a.toEquiv]
  exact (card_quotient_dvd_card _).trans (B.map q).card_subgroup_dvd_card

private theorem unitary_five_card_dvd {A : Type*} [Group A]
    (hm : ClassicalGroup.IsPSU A 3 5 ∨ IsSU A 3 5) : Nat.card A ∣ 378000 := by
  have hc {F : Type} [Field F] [Finite F]
      (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
      (hF : Nat.card F = 5^2) (hconj : ∀ x, J.conj x = x^5) :
      Nat.card (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) = 126000 := by
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    have hfixed : Nat.card {x : F // J.conj x = x} = 5 := by
      simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
        J.conj 5 1 (by decide) (by simpa only [pow_one] using hF)
        (by simpa only [pow_one] using hconj)
    rw [Representation.SU3.BinaryDegree.card_projective J hF hfixed]
    norm_num
  rcases hm with hm | hm
  · obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv,hc J hF hconj]
    decide
  · obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv,
      card_eq_card_quotient_mul_card_subgroup J.specialToProjective.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective J.specialToProjective
        J.specialToProjective_surjective).toEquiv,hc J hF hconj]
    exact Nat.mul_dvd_mul_left 126000 J.card_specialToProjective_ker_dvd_three

private theorem no_prime_model {A : Type*} [Group A] [Finite A]
    (hr : 2 ≤ primeRank 3 A) {p : ℕ} (hp : p.Prime)
    (hm : ClassicalGroup.IsPSL A 2 p) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let a : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,hF,ZMod.card])
  have hb := Theory.PSL2.primeField_odd_rank (p := p) (r := 3) (by decide)
  rw [primeRank_congr 3 (e.trans (GorensteinWalter.psl2RingEquiv a))] at hr
  exact (by decide : ¬ 2 ≤ 1) (hr.trans hb)

/-- An exceptional overcomponent containing a recognized triangle quotient
has only the M₂₂-cover, J₂, J₄ or Rudvalis possibilities. All other rows
are eliminated by intrinsic quotient orders, cubic rank and quasisimplicity. -/
theorem triangle_exceptional_overcomponent_sieve
    {G : Type*} [Group G] [Finite G] {I J : Subgroup G} (hIJ : I ≤ J)
    (hr : 2 ≤ primeRank 3 (J ⧸ pCore 2 J))
    (hq : IsQuasisimple (J ⧸ pCore 2 J))
    (hmI : Source.IsSL (I ⧸ pCore 2 I) 3 4 ∨ Source.IsSp (I ⧸ pCore 2 I) 2 4 ∨
      ClassificationModels.IsG2At (I ⧸ pCore 2 I) 4)
    (hmJ : FieldFourOvergroup (J ⧸ pCore 2 J)) :
    IsM22Cover (J ⧸ pCore 2 J) ∨
      Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty ((J ⧸ pCore 2 J) ≃* Janko4.Model) ∨
      Nonempty ((J ⧸ pCore 2 J) ≃* Rudvalis.Model) := by
  let A := J ⧸ pCore 2 J
  let := hq
  have hd := core_quotient_card_dvd hIJ
  have hi := triangle_order hmI
  have hc64 : 64 ∣ Nat.card A := by
    apply dvd_trans _ hd
    rcases hi with hi | hi | hi <;> rw [hi] <;> decide
  have small (n : ℕ) (hn : Nat.card A = n)
      (h₁ : ¬ 60480 ∣ n) (h₂ : ¬ 979200 ∣ n) (h₃ : ¬ 251596800 ∣ n) : False := by
    change Nat.card (I ⧸ pCore 2 I) ∣ Nat.card A at hd
    rw [hn] at hd
    rcases hi with hi | hi | hi <;> rw [hi] at hd
    · exact h₁ hd
    · exact h₂ hd
    · exact h₃ hd
  cases hmJ with
  | alternating hm =>
    obtain ⟨e⟩ := hm
    exact (small 2520 (by rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]; norm_num [Nat.factorial])
      (by decide) (by decide) (by decide)).elim
  | alternatingCover hm =>
    obtain ⟨_,⟨z⟩,⟨e⟩⟩ := hm
    have hc : Nat.card A = 7560 := by
      rw [card_eq_card_quotient_mul_card_subgroup (center A),
        Nat.card_congr e.toEquiv,Nat.card_congr z.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    exact (small 7560 hc (by decide) (by decide) (by decide)).elim
  | primeLinear p hp hm => exact (no_prime_model hr hp.1 hm).elim
  | linearTwentyFive hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    have hc : Nat.card A = 7800 := by
      rw [Nat.card_congr e.toEquiv,GorensteinWalter.psl2_card_formula F
        ⟨5,2,by decide,by decide,by decide,by simpa using hF⟩,hF]
      norm_num
    exact (small 7800 hc (by decide) (by decide) (by decide)).elim
  | three u hm =>
    cases u with
    | false => exact (rank_two_not_linear_three_five hr hm).elim
    | true => exact ((by decide : ¬ 64 ∣ 378000)
        (hc64.trans (unitary_five_card_dvd hm))).elim
  | m22 hm => exact (small 443520
      ((Nat.card_congr hm.some.toEquiv).trans Sporadic.Mathieu.m22_order)
      (by decide) (by decide) (by decide)).elim
  | m22Cover hm => exact .inl hm
  | m23 hm => exact (small 10200960
      ((Nat.card_congr hm.some.toEquiv).trans Sporadic.Mathieu.m23_order)
      (by decide) (by decide) (by decide)).elim
  | j1 hm => exact (small 175560
      ((Nat.card_congr hm.some.toEquiv).trans Janko1.card_model)
      (by decide) (by decide) (by decide)).elim
  | j2 hm => exact .inr (.inl hm)
  | j4 hm => exact .inr (.inr (.inl hm))
  | hs hm =>
    exact (small 44352000 ((Nat.card_congr hm.some.toEquiv).trans
      Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier) (by decide) (by decide) (by decide)).elim
  | ru hm => exact .inr (.inr (.inr hm))
  | nilpotentExtension hm =>
    obtain ⟨N,hN,_,he⟩ := hm
    let := hN
    exact (quasisimple_not_sl_two_five_quotient (pCore_quotient_pCore_eq_bot 2) N he).elim
  | elementaryExtension p hp hm => exact (rank_two_not_elementary_extension hr hp hm).elim

private theorem dvd_card_map_of_coprime_kernel
    {A H : Type*} [Group A] [Finite A] [Group H]
    (f : A →* H) (B : Subgroup A) {n : ℕ}
    (hc : Nat.Coprime n (Nat.card f.ker)) (hd : n ∣ Nat.card B) :
    n ∣ Nat.card (B.map f) := by
  let g := f.subgroupMap B
  have hcop : Nat.Coprime n (Nat.card g.ker) := by
    rw [ker_subgroupMap]
    exact hc.of_dvd_right (card_comap_dvd_of_injective f.ker B.subtype B.subtype_injective)
  have hh := g.ker.card_mul_index
  rw [index_eq_card,Nat.card_congr
    (QuotientGroup.quotientKerEquivOfSurjective g (f.subgroupMap_surjective B)).toEquiv] at hh
  exact hcop.dvd_of_dvd_mul_left (hh.symm ▸ hd)

private theorem five_equiv_maximal {A : Type*} [Group A]
    (hm : ClassicalGroup.IsPSL A 2 4) : Nonempty (A ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  exact (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).map
    (fun a => e.trans a)

/-- A containing triple cover of M₂₂ cannot contain the original triangle
join. The two normalized A₅ images coincide in M₂₂, so their join has image
of order 960; the central cubic and two-core kernels cannot remove its seven. -/
theorem triangle_join_overcomponent_not_m22_cover
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) {B C J : Subgroup G}
    (hB : B ∈ localCComponents T) (hC : C ∈ localCComponents T)
    (hJ : J ∈ localCComponents T) (hBJ : B ≤ J) (hCJ : C ≤ J)
    (hnB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hnC : (T : Subgroup G) ≤ normalizer (C : Set G))
    (hmB : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4)
    (hmC : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 4)
    (hmI : Source.IsSL ((B ⊔ C : Subgroup G) ⧸ pCore 2 (B ⊔ C : Subgroup G)) 3 4 ∨
      Source.IsSp ((B ⊔ C : Subgroup G) ⧸ pCore 2 (B ⊔ C : Subgroup G)) 2 4 ∨
      ClassificationModels.IsG2At ((B ⊔ C : Subgroup G) ⧸ pCore 2 (B ⊔ C : Subgroup G)) 4) :
    ¬ IsM22Cover (J ⧸ pCore 2 J) := by
  rintro ⟨_,⟨z⟩,⟨e⟩⟩
  let A := J ⧸ pCore 2 J
  have hz : Nat.card (center A) = 3 := by
    rw [Nat.card_congr z.toEquiv]
    exact Nat.card_zmod 3
  have hA : Nat.card A = 1330560 := by
    rw [card_eq_card_quotient_mul_card_subgroup (center A),
      Nat.card_congr e.toEquiv,Sporadic.Mathieu.m22_order,hz]
  have hIJ : B ⊔ C ≤ J := sup_le hBJ hCJ
  have hd := core_quotient_card_dvd hIJ
  change Nat.card ((B ⊔ C : Subgroup G) ⧸ pCore 2 (B ⊔ C : Subgroup G)) ∣ Nat.card A at hd
  rw [hA] at hd
  have hi : Nat.card ((B ⊔ C : Subgroup G) ⧸ pCore 2 (B ⊔ C : Subgroup G)) = 60480 := by
    rcases triangle_order hmI with hi | hi | hi
    · exact hi
    · rw [hi] at hd; norm_num at hd
    · rw [hi] at hd; norm_num at hd
  obtain ⟨S,hS,hBS⟩ := ChapterA.Section03.SourceEmbeddings.BinaryIntrinsic.local_in_local_overgroup
    T hB hJ hBJ
  have hCS : C.subgroupOf J ∈ localCComponents S :=
    hS.symm ▸ ChapterA.Section03.SourceEmbeddings.local_restrict hC hCJ
  have hsB : (S : Subgroup J) ≤ normalizer (B.subgroupOf J : Set J) := by
    rw [hS,←subgroupOf_normalizer_eq hBJ]
    exact comap_mono hnB
  have hsC : (S : Subgroup J) ≤ normalizer (C.subgroupOf J : Set J) := by
    rw [hS,←subgroupOf_normalizer_eq hCJ]
    exact comap_mono hnC
  let q := QuotientGroup.mk' (pCore 2 J)
  let k := e.toMonoidHom.comp (QuotientGroup.mk' (center A))
  let f := k.comp q
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : Function.Surjective k := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkker : k.ker = center A := by
    rw [MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective,QuotientGroup.ker_mk']
  let : Group.IsSolvable k.ker := by
    rw [hkker]
    exact Group.isSolvable_of_comm fun a b => IsMulCommutative.is_comm.comm a b
  let : Group.IsNilpotent q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isNilpotent
  let : Group.IsSolvable f.ker := by
    rw [←MonoidHom.comap_ker]
    exact isSolvable_comap_of_solvable_ker q k.ker
  let b := subgroupOfEquivOfLe hBJ
  let c := subgroupOfEquivOfLe hCJ
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let cq := QuotientGroup.congr _ _ c (pCore_map_iso 2 c)
  obtain ⟨eb⟩ := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SolvableQuotients.section_map
    f (B.subgroupOf J) hBS (bq.trans (five_equiv_maximal hmB).some)
  obtain ⟨ec⟩ := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SolvableQuotients.section_map
    f (C.subgroupOf J) hCS (cq.trans (five_equiv_maximal hmC).some)
  have heq := m22_local_five_eq (S.mapSurjective (f := f) (hk.comp hq))
    ((B.subgroupOf J).map f) ((C.subgroupOf J).map f)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hBS f)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hCS f)
    ((map_mono hsB).trans (le_normalizer_map f))
    ((map_mono hsC).trans (le_normalizer_map f)) eb ec
  have hcB : Nat.card ((B.subgroupOf J).map f) = 960 := by
    rw [←(pCore 2 ((B.subgroupOf J).map f)).card_mul_index]
    change Nat.card (pCore 2 ((B.subgroupOf J).map f)) *
      Nat.card (((B.subgroupOf J).map f) ⧸ pCore 2 ((B.subgroupOf J).map f)) = 960
    rw [(Sporadic.Mathieu.M22LocalA5Shape.core_shape_of_normalized
      (S.mapSurjective (f := f) (hk.comp hq)) _
      ((map_mono hsB).trans (le_normalizer_map f)) eb).2,
      Nat.card_congr eb.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have h7 : 7 ∣ Nat.card ((B ⊔ C).subgroupOf J) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hIJ).toEquiv]
    exact (hi ▸ (by decide : 7 ∣ 60480)).trans (card_quotient_dvd_card _)
  have h7q : 7 ∣ Nat.card (((B ⊔ C).subgroupOf J).map q) := by
    apply dvd_card_map_of_coprime_kernel q _ ?_ h7
    rw [QuotientGroup.ker_mk']
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := J)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 7 2).pow_right n
  have h7f := dvd_card_map_of_coprime_kernel k _
    (show Nat.Coprime 7 (Nat.card k.ker) by rw [hkker,hz]; decide) h7q
  rw [map_map,subgroupOf_sup hBJ hCJ,Subgroup.map_sup,←heq,sup_idem,hcB] at h7f
  norm_num at h7f

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
