module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SymplecticMembership
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalSeparation
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.RankOneRadical
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.SymplecticParabolic

/-!
# Excluding the higher-field symplectic row on the original selected component

Odd rank forces S to normalize L, hence Q₁ normalizes L. The genuine C.2.7
input identifies the marked intersection as a symplectic parabolic. Its
literal transport to the original FF quotient supplies the invariant
parabolic needed for both residuals to belong to L(G₁,S). They are nonshort
rank-one groups, so the proved original nonblock theorem places both in
M_Z. Their generation of L contradicts the original escaping condition.

The multiplier and core comparisons also exclude the corresponding C.2.7
star row. The full-Sylow branch is a chi-zero block and is excluded by its
cubic-rank bound. Original pre-exclusion exports retain both primes; the
exchanged source retains both plane sizes. The marker consumer preserves
its original Z₁ and row. No residual-membership or placement premise remains
in these endpoints, including at field size four.

General local-family Borel placement, the SL₃ exclusion, and the remaining
block/parabolic catalogue clauses remain with this task. Original 15.1.14
remains explicit for its existing producer and pre-exclusion assembly owner.
Source: Aschbacher--Smith 15.1.20(2), p.1095, and C.2.7, pp.145--147.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

open Theory.SpecificGroups.SymplecticFour
open ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface

/-- Transport the C.2.7 parabolic to the exact original normalizer image. -/
theorem symplectic_normalizer_marked_parabolic_of_input
    (d : CaseIComponentData T M Mc V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (a : d.NormalizerAction d.L)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hfour : 4 ≤ Nat.card F)
    (e : d.normalizerImage d.L ≃* Sp F) :
    ∃ g : Sp F,
      ((d.normalizerMarkedImage d.L).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = pointParabolic ∨
      ((d.normalizerMarkedImage d.L).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = planeParabolic := by
  let ec := (MulEquiv.ofBijective a.coreToImage
    (a.symplectic_four_core_bijective hi.quasisimple hfour e)).trans e
  have hz : center (d.L ⧸ pCore 2 d.L) = ⊥ := by
    apply map_injective (f := ec.toMonoidHom) ec.injective
    rw [Theory.GroupTheory.FixedElementary.map_center,EvenProjective.center_eq_bot,Subgroup.map_bot]
  let c := d.constrained_coreStarEquiv_of_center_eq_bot hi hz
  let es := c.symm.trans ec
  have he : e.toMonoidHom.comp (d.toNormalizerImage d.L) =
      es.toMonoidHom.comp (toStarImage d.L d.Q1) := by
    apply MonoidHom.ext
    intro x
    change ec (QuotientGroup.mk' _ x) = ec (c.symm (c (QuotientGroup.mk' _ x)))
    rw [c.symm_apply_apply]
  have hm : (d.MZ.subgroupOf d.L).map (toStarImage d.L d.Q1) =
      (starM d.L d.Q1 d.MZ).subgroupOf (starImage d.L d.Q1 d.L) := by
    apply map_injective (starImage d.L d.Q1 d.L).subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le (starM_le d.L d.Q1 d.MZ)]
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,mem_sup_left x.property⟩,⟨hx,x.property⟩,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx.2⟩,hx.1,rfl⟩
  have hm' : (d.normalizerMarkedImage d.L).map e.toMonoidHom =
      ((starM d.L d.Q1 d.MZ).subgroupOf (starImage d.L d.Q1 d.L)).map es.toMonoidHom := by
    rw [normalizerMarkedImage,map_map,he,←map_map,hm]
  rw [hm']
  exact star_symplectic_marked_parabolic_from_source hi es hfour

/-- The two original residuals now force placement, using the proved original
nonblock theorem. The input is the existing C.2.7 source setup, not the
parabolic or residual-membership conclusion. -/
theorem symplectic_le_MZ_of_source_input
    (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hK : d.L ∈ Chapter1.LIn d.G1 d.S)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (a : d.NormalizerAction d.L)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : d.normalizerImage d.L ≃* Sp F) : d.L ≤ d.MZ := by
  let : Group.IsPerfect d.L := Chapter1.mem_L_isPerfect hK.2
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn
  have hm := d.symplectic_normalizer_marked_parabolic_of_input hi a hfour e
  obtain ⟨e',hfam⟩ := d.localFamily_symplectic_residual_members hG hu h hK hi.quasisimple a hF hn e hm
  have hdata := a.symplectic_four_residual_data hi.quasisimple hF hn e'
  have hns := a.symplectic_four_residuals_not_short e' hF hn
  have hplace (P : Subgroup (Sp F)) (hP : P ∈ ({pointParabolic,planeParabolic} : Set (Subgroup (Sp F)))) :
      d.normalizerParabolicResidual d.L (P.map e'.symm.toMonoidHom) ≤ d.MZ := by
    let R := d.normalizerParabolicResidual d.L (P.map e'.symm.toMonoidHom)
    have hr := hfam P hP
    let : Group.IsPerfect R := Chapter1.mem_L_isPerfect hr.2
    obtain ⟨hf,⟨er⟩⟩ := hdata P hP
    let : IsSimpleGroup SL(2,F) := NaturalExtension.model_simple (by omega)
    let : IsSimpleGroup (R ⧸ pCore 2 R) := er.isSimpleGroup
    have hz : center (R ⧸ pCore 2 R) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (R ⧸ pCore 2 R)) inferInstance with hz | hz
      · exact hz
      · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp hz)).elim
    let hqr : IsQuasisimple (R ⧸ pCore 2 R) :=
      { simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }
    have hnot : ¬ ChapterC.IsShort R := by
      rcases hP with rfl | hP
      · exact hns.1
      · have he : P = planeParabolic := hP
        subst P
        exact hns.2
    exact d.localFamily_nonblock_le_MZ hG hempty hM hJ hu h hr hqr hf
      (fun hc => hnot hc.short) F er
  rw [←a.symplectic_four_residuals_generate hi.quasisimple e' hF hn]
  exact sup_le (hplace _ (Or.inl rfl)) (hplace _ (Or.inr rfl))

/-- The original selected component cannot have a higher-field Sp₄ normalizer
image. Both original primes retain their selection; C.2.7 normalization and
both residual memberships are discharged here. -/
theorem PreExclusionSource.constrained_normalizerImage_not_symplectic_four
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n) :
    ¬ Nonempty (d.normalizerImage d.L ≃* Sp F) := by
  rintro ⟨e⟩
  have hK : d.L ∈ Chapter1.LIn d.G1 d.S := ⟨d.L_component.1,s.local_component⟩
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h hK s.quasisimple d.L_not_le_MZ hf
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn
  let ec := (MulEquiv.ofBijective a.coreToImage
    (a.symplectic_four_core_bijective s.quasisimple hfour e)).trans e
  have hnK := d.localFamily_symplectic_four_normalizes hG h hK s.quasisimple ec
  have hi := s.constrained_input_of_normalizes (h := h) hG hf
    ((d.catalogue_radical_le_sylow s.centralizer_sylow hu).trans hnK)
  exact d.L_not_le_MZ (d.symplectic_le_MZ_of_source_input hG hempty hM hJ hu h hK hi a hF hn e)

/-- The later exchanged source has the same exclusion on either plane size. -/
theorem ExchangedSource.constrained_normalizerImage_not_symplectic_four
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hf : generalizedFitting d.L = pCore 2 d.L)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n) :
    ¬ Nonempty (d.normalizerImage d.L ≃* Sp F) := by
  rintro ⟨e⟩
  have hK : d.L ∈ Chapter1.LIn d.G1 d.S := ⟨d.L_component.1,s.local_component⟩
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h hK s.quasisimple d.L_not_le_MZ hf
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn
  let ec := (MulEquiv.ofBijective a.coreToImage
    (a.symplectic_four_core_bijective s.quasisimple hfour e)).trans e
  have hnK := d.localFamily_symplectic_four_normalizes hG h hK s.quasisimple ec
  have hi := s.constrained_input_of_normalizes hG h hf
    ((d.catalogue_radical_le_sylow s.centralizer_sylow hu).trans hnK)
  exact d.L_not_le_MZ (d.symplectic_le_MZ_of_source_input hG hempty hM hJ hu h hK hi a hF hn e)


/-- A symplectic C.2.7 star row gives the same actual matrix quotient in the
normalizer action. Both central covering maps are proved to be isomorphisms. -/
private theorem symplectic_normalizer_of_star
    {d : CaseIComponentData T M Mc V}
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (a : d.NormalizerAction d.L)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hfour : 4 ≤ Nat.card F)
    (e : starImage d.L d.Q1 d.L ≃* Sp F) : Nonempty (d.normalizerImage d.L ≃* Sp F) := by
  let c : PerfectCentralCovering.Cover (d.L ⧸ pCore 2 d.L) (Sp F) :=
    { toMonoidHom := e.toMonoidHom.comp (coreToStar hi.normalizes)
      surjective := e.surjective.comp (coreToStar_surjective hi.normalizes)
      isPerfect := hi.quasisimple.toIsPerfect
      ker_le_center := by
        rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
        exact coreToStar_ker_central_from_source hi }
  have hic := CentralCovers.Even.cover_injective (by omega) c
  let ec := MulEquiv.ofBijective c.toMonoidHom ⟨hic,c.surjective⟩
  have hz : center (d.L ⧸ pCore 2 d.L) = ⊥ := by
    apply map_injective (f := ec.toMonoidHom) ec.injective
    rw [Theory.GroupTheory.FixedElementary.map_center,EvenProjective.center_eq_bot,Subgroup.map_bot]
  have hai : Function.Injective a.coreToImage := (MonoidHom.ker_eq_bot_iff _).mp
    (bot_unique ((a.coreToImage_ker_central hi.quasisimple).trans hz.le))
  exact ⟨(MulEquiv.ofBijective a.coreToImage ⟨hai,a.coreToImage_surjective⟩).symm.trans ec⟩

/-- The selected original star catalogue has no higher-field symplectic row,
including its full-Sylow branch and field size four. -/
theorem PreExclusionSource.constrained_starImage_not_symplectic_four
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n) :
    ¬ Nonempty (starImage d.L d.Q1 d.L ≃* Sp F) := by
  rintro ⟨e⟩
  by_cases hSL : d.SL ≤ d.Q1
  · have hc : ChapterC.IsChiZeroBlock d.L := by
      rcases s.constrained_rankOne_block_of_sylow_le_radical (h := h) hG hf hSL with hc | hc
      · exact Or.inl hc
      · exact Or.inr (Or.inr hc)
    have hr := chiZero_star_threeRank_le_one (R := d.Q1) hc
    rw [primeRank_equiv 3 e] at hr
    have hlo : 2 ≤ primeRank 3 (Sp F) :=
      Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic.trans (primeRank_subgroup_le 3 _)
    omega
  · have hi := s.constrained_input_of_not_contains_sylow (h := h) hG hu hf hSL
    have a := d.localFamily_normalizerAction hG hempty hM hJ hu h
      ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf
    have hfour : 4 ≤ Nat.card F := by
      rw [hF]
      exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn
    exact s.constrained_normalizerImage_not_symplectic_four (h := h) hG hempty hM hJ hu hf hF hn
      (symplectic_normalizer_of_star hi a hfour e)

/-- The exchanged source eliminates the same C.2.7 row on both plane sizes. -/
theorem ExchangedSource.constrained_starImage_not_symplectic_four
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hf : generalizedFitting d.L = pCore 2 d.L)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n) :
    ¬ Nonempty (starImage d.L d.Q1 d.L ≃* Sp F) := by
  rintro ⟨e⟩
  by_cases hSL : d.SL ≤ d.Q1
  · have hc : ChapterC.IsChiZeroBlock d.L := by
      rcases s.constrained_rankOne_block_of_sylow_le_radical h hG hf hSL with hc | hc
      · exact Or.inl hc
      · exact Or.inr (Or.inr hc)
    have hr := chiZero_star_threeRank_le_one (R := d.Q1) hc
    rw [primeRank_equiv 3 e] at hr
    have hlo : 2 ≤ primeRank 3 (Sp F) :=
      Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic.trans (primeRank_subgroup_le 3 _)
    omega
  · have hi := s.constrained_input_of_not_contains_sylow hG h hu hf hSL
    have a := d.localFamily_normalizerAction hG hempty hM hJ hu h
      ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf
    have hfour : 4 ≤ Nat.card F := by
      rw [hF]
      exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn
    exact s.constrained_normalizerImage_not_symplectic_four hG hempty hM hJ hu h hf hF hn
      (symplectic_normalizer_of_star hi a hfour e)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original marker retains its subgroup, seed, row and prime and now
excludes every higher-field symplectic FF row. Original 15.1.14 remains
explicit for its existing producer and pre-exclusion assembly owner. -/
theorem PreparedChosenModule.source_preExclusion_constrained_no_higher_symplectic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (generalizedFitting d.L = pCore 2 d.L →
        ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ),
          Nat.card F = 2^n → 1 < n →
          (¬ Nonempty (d.normalizerImage d.L ≃* Theory.SpecificGroups.SymplecticFour.Sp F)) ∧
          ¬ Nonempty (Chapter1.RadicalExclusions.ModelReduction.starImage d.L d.Q1 d.L ≃*
            Theory.SpecificGroups.SymplecticFour.Sp F)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hf _ _ _ _ _ hF hn =>
    ⟨s.constrained_normalizerImage_not_symplectic_four (h := h) hG hempty hM hJ hu hf hF hn,
      s.constrained_starImage_not_symplectic_four (h := h) hG hempty hM hJ hu hf hF hn⟩⟩
end CFSG.Quasithin.Chapter15.Section01
