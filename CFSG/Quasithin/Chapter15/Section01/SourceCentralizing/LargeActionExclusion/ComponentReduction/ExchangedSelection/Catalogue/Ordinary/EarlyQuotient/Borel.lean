module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.Borel
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.Complete

/-!
# The initial Borel family and the original quotient consumer

The proved initial rank-one constructor supplies its literal Borel equality
before applying the shared 15.1.21 exclusion. The original pre-exclusion
witness is retained at the same component in the quotient and exchanged
applications. In the odd-characteristic marking, this also removes the
PSL₂(5) ≅ PSL₂(4) alternative, leaving the actual PSL₃(2) carrier.

The original 15.1.14 residual is an explicit earlier input, with final
discharge owned by qt-e-1514-global-thompson-residual and
qt-e-15122-pre-exclusion-catalogue. No exhaustive initial or refined
catalogue is assumed or asserted here.
Source: Aschbacher--Smith 15.1.20--21, printed pp.1094--1098.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The original rank-one model supplies the Borel clause required by 15.1.21. -/
theorem PreExclusionSource.false_of_initial_rankOne
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) (hp : p = 3 ∨ p = 5)
    (hm : IsBenderModel d.L ∨ Nonempty ((d.L ⧸ pCore 2 d.L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)) : False := by
  have hB := s.rankOne_borel_eq_of_centralizer_le (h := h) hG hM hu hne hmany hres hL hm
    (s.rankOne_centralizer_le (h := h) hG hM hu hL hm)
  exact s.false_of_rankOne (h := h) hG hM hJ hu hL hp hm hB

/-- The complete initial Borel family feeds the existing early quotient theorem. -/
theorem PreExclusionSource.source_ordinary_post_rank_one_model_of_rankOne
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) (hp : p = 3 ∨ p = 5)
    (hm : IsBenderModel d.L ∨ Nonempty ((d.L ⧸ pCore 2 d.L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)) :
    OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L) :=
  (s.ordinary20_of_rankOne (h := h) hG hM hu hne hmany hres hL hm).postRankOneModel_of_preExclusion
    (h := h) s hG hM hJ hu hL hp

/-- The same-component exchanged application retains the earlier source witness. -/
theorem ExchangedSource.not_ordinary_of_preExclusion_initial_rankOne
    (e : d.ExchangedSource) (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hp : p = 3 ∨ p = 5)
    (hm : IsBenderModel d.L ∨ Nonempty ((d.L ⧸ pCore 2 d.L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)) :
    ¬ IsComponent d.G1 (d.L.subgroupOf d.G1) :=
  e.not_ordinary_of_preExclusion_catalogue (h := h) s hG hM hJ hu hp
    (fun hL => s.ordinary20_of_rankOne (h := h) hG hM hu hne hmany hres hL hm)

/-- The original odd-characteristic marking now leaves only the actual PSL₃(2) model. -/
theorem PreExclusionSource.ordinary_odd_pslThreeTwo
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) (hp : p = 3 ∨ p = 5)
    (hm : ClassicalGroup.IsPSL d.L 3 3 ∨
      ∃ q : ℕ, IsFermatOrMersennePrime q ∧ ClassicalGroup.IsPSL d.L 2 q) :
    Nonempty (d.L ≃* Matrix.PSL3Two.PSL) := by
  rcases s.ordinary_odd_binary_models (h := h) hM.1.2 hL hm with he | he
  · obtain ⟨e⟩ := he
    apply False.elim
    apply s.false_of_initial_rankOne (h := h) hG hM hJ hu hne hmany hres hL hp
    left
    exact .linear 2 (by decide) ⟨GaloisField 2 2,inferInstance,inferInstance,
      GaloisField.card 2 2 (by decide),⟨e⟩⟩
  · exact he

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
