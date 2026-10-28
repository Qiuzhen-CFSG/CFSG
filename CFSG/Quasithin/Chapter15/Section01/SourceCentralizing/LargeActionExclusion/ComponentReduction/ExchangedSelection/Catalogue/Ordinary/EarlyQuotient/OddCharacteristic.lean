module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.SmallExceptions
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.EarlyQuotient.Borel

/-!
# Exhaustion of the ordinary odd-characteristic marking

The checked model reduction leaves PSL₂(4) or PSL₃(2). The initial Borel
argument excludes the former; the original centralizer residual excludes
the latter. Thus the whole odd-characteristic 1.1.5 constructor is
impossible at the original fixed component. Its initial Ordinary20 and
early quotient consumers follow, with the same pre-exclusion witness in
the later exchanged application.

The only earlier-source premise is the literal 15.1.14 residual, retained
for qt-e-1514-global-thompson-residual and the final assembly owner
qt-e-15122-pre-exclusion-catalogue. This proves one full initial family;
the higher-field, alternating and remaining sporadic families are not
assumed or asserted to be exhausted.

Source: Aschbacher--Smith 15.1.20--21, printed pp.1094--1098.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- All actual models in the original odd-characteristic marking are excluded. -/
theorem PreExclusionSource.false_of_initial_odd
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
    False := by
  obtain ⟨e⟩ := s.ordinary_odd_pslThreeTwo (h := h) hG hM hJ hu hne hmany hres hL hp hm
  exact s.false_of_pslThreeTwo_equiv (h := h) hG hM hu hmany hres hL e

/-- The entire odd marking supplies the initial constructor exhaustion at the same d. -/
theorem PreExclusionSource.ordinary20_of_odd
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
    d.Ordinary20Alternatives :=
  (s.false_of_initial_odd (h := h) hG hM hJ hu hne hmany hres hL hp hm).elim

/-- Apply the shared constructor-aware quotient consumer to the full odd marking. -/
theorem PreExclusionSource.source_ordinary_post_rank_one_model_of_odd
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
    OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L) :=
  (s.ordinary20_of_odd (h := h) hG hM hJ hu hne hmany hres hL hp hm).postRankOneModel_of_preExclusion
    (h := h) s hG hM hJ hu hL hp

/-- Later exchanged selection retains the original pre-exclusion witness at the same d. -/
theorem ExchangedSource.not_ordinary_of_preExclusion_initial_odd
    (e : d.ExchangedSource)
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
    (hp : p = 3 ∨ p = 5)
    (hm : ClassicalGroup.IsPSL d.L 3 3 ∨
      ∃ q : ℕ, IsFermatOrMersennePrime q ∧ ClassicalGroup.IsPSL d.L 2 q) :
    ¬ IsComponent d.G1 (d.L.subgroupOf d.G1) :=
  e.not_ordinary_of_preExclusion_catalogue (h := h) s hG hM hJ hu hp
    (fun hL => s.ordinary20_of_odd (h := h) hG hM hJ hu hne hmany hres hL hp hm)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
