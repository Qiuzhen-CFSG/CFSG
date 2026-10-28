module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Sporadic.MathieuEleven
public import Theory.Mathieu.M11.ThompsonNormalizer
public import Theory.Mathieu.M11.Properties.RankLower
public import Theory.GroupTheory.GeneralizedFitting.ComponentCoprimeRankNormal

/-!
# The complete ordinary M11 refinement

The three-rank-two subgroup of M11 forces the original component to be
normal in G1: two distinct conjugate components would contradict the
ambient strongly quasithin bound. The normal M11 Thompson calculation
then centralizes L with the literal embedded two-residual of N_G1(J(S)).
Combining this with the initial central-cover splitting and Sylow-center
centralizer identity proves every clause of Ordinary22's M11 row.

The original two-core quotient marking is retained; neither an exchanged
source nor an extra normality or residual premise is used. Exhaustion and
the remaining Ordinary22 families remain with
qt-e-15122-ordinary-pre-exclusion, and final pre-exclusion catalogue assembly
with qt-e-15122-pre-exclusion-catalogue.

Source: Aschbacher--Smith 15.1.22(6), printed pp.1098--1100, especially
the final paragraph on p.1100; component normality uses the rank argument
of 1.2.1(3).
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- An actual ordinary M11 component is normal in the literal G1. -/
theorem PreExclusionSource.mathieuEleven_normal
    (_s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : d.L ≃* Sporadic.Mathieu.M11) : (d.L.subgroupOf d.G1).Normal := by
  let K := d.L.subgroupOf d.G1
  let f : K ≃* Sporadic.Mathieu.M11 := (subgroupOfEquivOfLe d.L_component.1).trans e
  have hc : Nat.card (center K) = 1 := by
    rw [Nat.card_congr (centerCongr f).toEquiv,Sporadic.Mathieu.m11_center_eq_bot,card_bot]
  have hr : 2 ≤ primeRank 3 K := by
    rw [primeRank_equiv 3 f]
    exact Sporadic.Mathieu.m11_primeRank_three_ge_two
  let := h.elementary
  have hs : IsSQTK KnownSimple.IsKnownSimple d.G1 :=
    caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
      ((IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left))
  apply hL.normal_of_coprime_center_primeRank 3 (by rw [hc]; decide)
  change primeRank 3 d.G1 < 2 * primeRank 3 K
  have hh := hs.stronglyQuasithin 3 Nat.prime_three (by decide)
  omega

/-- The literal G1-normalizer of J(S) has two-residual centralizing L. -/
theorem PreExclusionSource.mathieuEleven_thompson_residual
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : d.L ≃* Sporadic.Mathieu.M11) :
    (pResidual 2 (normalizer
      ((elementaryAbelianMaxJ d.S).subgroupOf d.G1 : Set d.G1))).map
      (d.G1.subtype.comp (normalizer
        ((elementaryAbelianMaxJ d.S).subgroupOf d.G1 : Set d.G1)).subtype) ≤
          centralizer (d.L : Set G) := by
  let K := d.L.subgroupOf d.G1
  let : K.Normal := s.mathieuEleven_normal (h := h) hG hL e
  let f : K ≃* Sporadic.Mathieu.M11 := (subgroupOfEquivOfLe d.L_component.1).trans e
  obtain ⟨S,hS⟩ := s.centralizer_sylow
  have hJ : elementaryAbelianMaxJ (S : Subgroup d.G1) =
      (elementaryAbelianMaxJ d.S).subgroupOf d.G1 := by
    apply map_injective d.G1.subtype_injective
    rw [←elementaryAbelianMaxJ_map_injective _ d.G1.subtype_injective,hS,
      map_subgroupOf_eq_of_le ((show elementaryAbelianMaxJ d.S ≤ d.S from
        sSup_le fun _ hA => hA.1).trans d.S_le_G1)]
  have hr := Sporadic.Mathieu.normal_m11_thompson_residual K f S
  rw [hJ] at hr
  have hm := map_mono (f:=d.G1.subtype) hr
  rw [map_map,map_centralizer_subtype,
    show K.map d.G1.subtype = d.L from map_subgroupOf_eq_of_le d.L_component.1] at hm
  exact hm.trans inf_le_right

/-- All clauses of source 15.1.22(6), from the original two-core quotient marking. -/
theorem PreExclusionSource.ordinary22_of_mathieuEleven_quotient
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* Sporadic.Mathieu.M11) :
    d.Ordinary22Alternatives := by
  obtain ⟨f⟩ := s.mathieuEleven_equiv_of_quotient (h := h) hL e
  exact .mathieuEleven ⟨f⟩
    (s.mathieuEleven_centralizer_eq (h := h) hG hM hu hL f)
    (s.mathieuEleven_thompson_residual (h := h) hG hL f)
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
