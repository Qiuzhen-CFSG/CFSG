module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalJankoFour
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeJankoFourSections
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicJankoMathieu
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicFiniteContainers

public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.LinearExclusion

/-!
# Recognition of the original residual in a J₄ container

The literal residual quotient embeds, through the two-core quotient maps, as a
section of J₄. The earlier right-component alternatives and J₄ order eliminate
the diagram and unitary rows, and the local J₄ rank-one recognition gives
PSL₂(4). This applies to the unmoved residual and identifies the original right
Hall subgroup as cubic. The strengthened sieve retains the original component
and all prior exclusions.

The private finite-order lemmas are reused through `import all`; their original
module boundary is unchanged.

Source: Aschbacher--Smith, The Classification of Quasithin Groups, II,
5.1.12--13, printed pp.635--637 (the J₄ containing-component row).
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open Chapter1.Section02.LocalModels
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
private theorem unitary_degree_one {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) {f : ℕ} (hf : 1 ≤ f)
    (hF : Nat.card F = (2 ^ f) ^ 2) (hj : ∀ x, J.conj x = x ^ (2 ^ f))
    (hd : Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) ∣ 86775571046077562880) : f = 1 := by
  have hpow := (HermitianForm.BinarySylowOrder.cube_dvd_card_projective J
    (by omega : f ≠ 0) hF hj).trans hd
  have hf7 : f ≤ 7 := by
    by_contra hh
    have hh := (pow_dvd_pow 2 (by omega : 22 ≤ f * 3)).trans
      (by simpa only [pow_mul] using hpow : 2 ^ (f * 3) ∣ 86775571046077562880)
    norm_num at hh
  have hfix := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 f
    (by omega) hF hj
  rw [Representation.SU3.BinaryDegree.card_projective J hF hfix] at hd
  interval_cases f
  · rfl
  all_goals norm_num at hd


private theorem rankOne_simple_of_janko_order {X : Type*} [Group X] [Finite X]
    (hm : ChapterF.Source.IsRankOneModel X) (hns : ¬ Group.IsSolvable X)
    (hd : Nat.card X ∣ 86775571046077562880) : IsSimpleGroup X := by
  cases hm with
  | linear f hf hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    have hf1 : f ≠ 1 := by
      intro he
      subst f
      obtain ⟨a⟩ := BenderSuzuki.External.huppert_II_6_14_a_psl2_card_two
        (by simpa using hF)
      have hc : Nat.card X = 6 := by
        rw [Nat.card_congr (e.trans a).toEquiv,Nat.card_perm,Nat.card_fin]
        rfl
      apply hns
      apply isSolvable_of_prime_dvd_card_eq_two_or_three
      intro p hp hdiv
      rw [hc] at hdiv
      rcases hp.dvd_mul.mp (show p ∣ 2 * 3 from hdiv) with h2 | h3
      · exact .inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
      · exact .inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3)
    have hlarge : 3 < Nat.card F := by
      rw [hF]
      exact (by decide : 3 < 2^2).trans_le
        (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ f))
    exact e.isSimpleGroup_congr.mpr
      (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hlarge)
  | suzuki m hm =>
    obtain ⟨e⟩ := hm
    by_cases hz : m = 0
    · subst m
      let := suzukiZero_isSolvable
      exact (hns (Group.isSolvable_of_isSolvable_injective
        (f := e.toMonoidHom) e.injective)).elim
    · exact e.isSimpleGroup_congr.mpr
        (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).1
  | projective_unitary f hf hm =>
    obtain ⟨F,_,_,J,hF,hj,⟨e⟩⟩ := hm
    have hf1 := unitary_degree_one J hf hF hj ((Nat.card_congr e.toEquiv) ▸ hd)
    subst f
    let := HermitianForm.FixedFieldTwo.projective_isSolvable J
      (by simpa using hF) (by simpa using hj)
    exact (hns (Group.isSolvable_of_isSolvable_injective
      (f := e.toMonoidHom) e.injective)).elim
  | special_unitary f hf hm =>
    obtain ⟨F,_,_,J,hF,hj,⟨e⟩⟩ := hm
    have hf1 := unitary_degree_one J hf hF hj
      ((card_dvd_of_surjective J.specialToProjective J.specialToProjective_surjective).trans
        ((Nat.card_congr e.toEquiv) ▸ hd))
    subst f
    let := HermitianForm.FixedFieldTwo.projective_isSolvable J
      (by simpa using hF) (by simpa using hj)
    let : Group.IsSolvable J.specialToProjective.ker :=
      Group.isSolvable_of_isSolvable_injective
        (inclusion_injective J.specialToProjective_ker_le_center)
    let : Group.IsSolvable J.specialSubgroup := Group.isSolvable_of_ker_le_range
      J.specialToProjective.ker.subtype J.specialToProjective (by simp)
    exact (hns (Group.isSolvable_of_isSolvable_injective
      (f := e.toMonoidHom) e.injective)).elim
  | dihedral hm =>
    obtain ⟨e⟩ := hm
    let := GLS3.Chapter5.dihedralGroup_isSolvable 5
    exact (hns (Group.isSolvable_of_isSolvable_injective
      (f := e.toMonoidHom) e.injective)).elim


variable {G : Type*} [Group G] [Finite G]

/-- The actual unmoved residual in the normal J₄ row has intrinsic quotient
PSL₂(4). Its original local component and every two-core map are retained. -/
theorem residual_section_of_jankoFour
    {T : Sylow 2 G} {L W H A Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (hR : residual H ∈ Chapter1.L G (T : Subgroup G))
    (C : Subgroup Y) (hC : C.IsCComponent)
    (hRC : residual H ≤ C.map Y.subtype)
    (e : (C ⧸ pCore 2 C) ≃* Janko4.Model) :
    ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 := by
  have hR' : (pResidual 2 H).IsCComponent := by
    have hh := hR.1
    rw [residual_sup_sylow T H hH.1.1.2] at hh
    simpa only [residual,subgroupOf,comap_map_eq_self_of_injective H.subtype_injective] using hh
  have hRY : residual H ≤ Y := (map_subtype_le _).trans hY.2
  have hTY := hH.1.1.2.trans hY.2
  let q := QuotientGroup.mk' (pCore 2 Y)
  let S := T.subtype hTY
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y))
  let Rbar := ((residual H).subgroupOf Y).map q
  let Cbar := C.map q
  have hl : (residual H).subgroupOf Y ∈ Chapter1.L Y (S : Subgroup Y) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTY hRY).mp ⟨hRY,hR⟩
  have hlq : Rbar ∈ ChapterA.Section03.localCComponents P :=
    Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hl
  have hRC' : (residual H).subgroupOf Y ≤ C := by
    have hh := comap_mono (f := Y.subtype) hRC
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  have hle : Rbar ≤ Cbar := map_mono hRC'
  let : Group.IsNilpotent (pCore 2 Y) := pCore_isNilpotent
  obtain ⟨Q,hQ,hU⟩ := ChapterA.Section03.SourceEmbeddings.exists_local_sylow_restriction
    P hlq hle (hC.map_quotient (pCore 2 Y)).subnormal
  let U := Rbar.subgroupOf Cbar
  have hn : (P : Subgroup (Y ⧸ pCore 2 Y)) ≤ normalizer (Rbar : Set _) := by
    apply (map_mono (f := q) ?_).trans (le_normalizer_map q)
    rw [←subgroupOf_normalizer_eq hRY]
    exact comap_mono (hH.1.1.2.trans (le_normalizer_residual H))
  have hnU : (Q : Subgroup Cbar) ≤ normalizer (U : Set Cbar) := by
    rw [hQ,←subgroupOf_normalizer_eq hle]
    exact comap_mono hn
  let r := q.subgroupMap ((residual H).subgroupOf Y)
  have hr : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let e₀ := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let e₁ := e₀.trans (subgroupOfEquivOfLe hRY).symm
  let e₂ := r.pCoreQuotientEquiv (q.subgroupMap_surjective _) hr
  let e₃ := (subgroupOfEquivOfLe hle).symm
  let eR : ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃* (U ⧸ pCore 2 U) :=
    (QuotientGroup.congr _ _ e₁ (pCore_map_iso 2 e₁)).trans
      (e₂.trans (QuotientGroup.congr _ _ e₃ (pCore_map_iso 2 e₃)))
  let eC : Cbar ≃* Janko4.Model := (cComponentTwoCoreQuotientEquiv hC).symm.trans e
  have hd : Nat.card ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ∣
      86775571046077562880 := by
    rw [Nat.card_congr eR.toEquiv]
    have hh := (card_quotient_dvd_card (pCore 2 U)).trans U.card_subgroup_dvd_card
    rwa [Nat.card_congr eC.toEquiv,Janko4.Cardinality.model_card] at hh
  have hmodel : ChapterF.Source.IsRankOneModel
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) := by
    rcases Global.right_source_cases h.qtke h.sylow_normalizes hH hgen with hs | hs
    · obtain ⟨K,f,hK,hqs,_,_,hc | hc⟩ := hs
      · have hKR : K = pResidual 2 H := by
          apply hK.eq_of_le hR'
          let := hK.perfect
          apply le_sInf
          rintro N ⟨hn,hN⟩
          let := hn
          let : Group.IsNilpotent (H ⧸ N) := hN.isNilpotent
          exact (le_solvableResidual_of_isPerfect K).trans (solvableResidual_le_of_solvable_quotient N)
        subst K
        obtain ⟨t,_,hne,_⟩ := hc.1.exchanged_product
        exact (hne (mem_normalizer_iff_map_conj_eq.mp
          (show t⁻¹ ∈ normalizer (pResidual 2 H : Set H) by
            rw [normalizer_eq_top]; exact mem_top _)).symm).elim
      · have he : K = pResidual 2 H :=
          BenderHall.SingleClauses.component_eq_residual (S := T.subtype hH.1.1.2) hc.1 hK
        subst K
        have hO : pCore 2 H ≤ sourceKernel ((normalizer (L : Set G)).subgroupOf H) := by
          apply normal_le_normalCore.mpr
          exact (pCore_isPGroup.le_sylow_of_normal (T.subtype hH.1.1.2)).trans
            (comap_mono h.sylow_normalizes)
        exact Prime.single_bender_component_quotient hK hqs hO hc.1 hc.2
    · obtain ⟨K,f,hK,hqs,_,hf,hc,hm⟩ := hs
      have hmodels := Prime.diagram_source_residual_quotient h.sylow_normalizes hH.1.1.2 hK hqs hc hf hm
      have hf2 := Prime.diagram_finite_order hf (by simp [Prime.finiteOrders]) hd hmodels
      subst f
      rcases hmodels with hlin | hsl | hsp
      · exact (not_linear_four_residual_of_escape h.qtke h.sylow_normalizes hH hY hescape hlin).elim
      · have hslU : IsSL (U ⧸ pCore 2 U) 3 4 := by
          obtain ⟨F,_,_,hF,⟨a⟩⟩ := hsl
          exact ⟨F,inferInstance,inferInstance,hF,⟨eR.symm.trans a⟩⟩
        exact (Prime.jankoFour_not_sl3_four
          ((Chapter1.Section02.uniqueness_local_quotient_sqtk h.qtke hY.1).subgroup Cbar)
          eC Q U hU hnU hslU).elim
      · obtain ⟨F,_,_,hF,⟨a⟩⟩ := hsp
        let : Fintype F := Fintype.ofFinite F
        let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
          (by simpa only [Nat.card_eq_fintype_card] using hF)
        let b := a.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
        rw [Nat.card_congr b.toEquiv,Theory.SpecificGroups.SymplecticFour.card_sp,hF] at hd
        norm_num at hd
  let : Group.IsPerfect (pResidual 2 H) := hR'.perfect
  let : Group.IsPerfect ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hns : ¬ Group.IsSolvable ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) := by
    intro hsol
    let := hsol
    let : Group.IsNilpotent (pCore 2 (pResidual 2 H)) := pCore_isNilpotent
    exact hR'.not_isSolvable (Group.isSolvable_of_ker_le_range
      (pCore 2 (pResidual 2 H)).subtype (QuotientGroup.mk' (pCore 2 (pResidual 2 H)))
      (by rw [range_subtype,QuotientGroup.ker_mk']))
  let : IsSimpleGroup ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) :=
    rankOne_simple_of_janko_order hmodel hns hd
  let : IsSimpleGroup (U ⧸ pCore 2 U) := eR.symm.isSimpleGroup
  exact (Prime.JankoFourSections.right_quotient_four eC Q U hU hnU
    (hmodel.of_equiv eR.symm)).of_mulEquiv eR

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- The original sieve retains all preceding exclusions and identifies its
whole residual quotient and original right Hall cubic in the genuine J₄ row. -/
theorem localCartan_escape_seed_jankoFour_section_reduction
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        ¬ SolvableSylowOvergroups (C ⧸ pCore 2 C) ∧
        (∀ m : ℕ, 0 < m → ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          IsSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨ IsSU (C ⧸ pCore 2 C) 3 (2 ^ m))) ∧
        (RankTwoTheoremC (C ⧸ pCore 2 C) →
          K = residual H ∧ C.Normal ∧
          Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p) ∧
        ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 25 ∧
        C.Normal ∧
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 p ∨
            ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 p ∨
            IsSL (C ⧸ pCore 2 C) 3 p ∨ IsSU (C ⧸ pCore 2 C) 3 p)) ∧
        (Nonempty ((C ⧸ pCore 2 C) ≃* Janko4.Model) →
          K = residual H ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 ∧
          Nat.card B = 3) := by
  obtain ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hCn,hJ,hOdd,hJ4⟩ :=
    localCartan_escape_seed_jankoFour_residual_reduction h hH hgen c hY hescape
  refine ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hCn,hJ,hOdd,?_⟩
  intro he
  have hKR := hJ4 he
  have hfour := LocalSieve.residual_section_of_jankoFour h hH hgen hY hescape
    (hKR ▸ hKL) C hC (hKR ▸ hKC) he.some
  have hA5 : Nonempty ((residual H ⧸ pCore 2 (residual H)) ≃* alternatingGroup (Fin 5)) := by
    let a₀ := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
    let eq := QuotientGroup.congr _ _ a₀ (pCore_map_iso 2 a₀)
    obtain ⟨F,_,_,hF,⟨b₀⟩⟩ := hfour
    exact ⟨eq.symm.trans (b₀.trans
      (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some)⟩
  exact ⟨hKR,hfour,LocalSieve.right_hall_card_three_of_residual_A5 h hH hgen c hA5⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
