module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.Families
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.Planes

/-!
# Source offenders and the outside Sigma difference

The original chosen-module actor theorem supplies a maximum elementary subgroup
outside the two-core. Finite descent and conjugacy then give actual Delta
members both inside and outside T. If every Sigma member fixed V, conjugacy
would make every such member fix its entire H-span. The uniform fixed-centralizer
identity would force a Delta member in T to lie in the two-core, a contradiction.
Thus that identity alone supplies an actual member of Sigma minus Sigma(T).

The uniform fixed-centralizer identity remains a local obligation of
qt-e-152-offender-plane. These selection theorems do not assert that it, the
marked generators, or the final plane centrality have been proved.

Source: Aschbacher--Smith 15.1.12(2), 15.2.9 and 15.2.11, pp.1090,1110--1111.
-/

public section
open Subgroup Stellmacher
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor

namespace CFSG.Quasithin.Chapter15.Section02
open ChosenGeometry Section01
variable {G : Type*} [Group G] [Finite G]

/-- Nonemptiness in Notation 15.2.9, using the original chosen source. -/
theorem ChosenSmallSource.delta_nonempty
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) : (delta H).Nonempty := by
  let := h.prepared.elementary
  obtain ⟨_,_,A,hA,hAN,_⟩ := source_chosen_minimal_actor_equalities
    h.ambient T h.empty h.maximal hH h.centralizing h.prepared.le_selected
    h.prepared.nontrivial h.prepared.normalized h.prepared.seed_span h.prepared.le_local
    (h.prepared.inside_core H hH) h.prepared.quadratic_ratio
  have hf : A.map H.subtype ∈ elementaryAbelianMaxSubgroups H := by
    have ha := (maxFamily_sylow_iff (T.subtype hH.1.1.2) A).mp hA
    have hm := (maxFamily_map_injective_iff H.subtype H.subtype_injective ⊤ A).mpr ha.2
    simpa only [← MonoidHom.range_eq_map, range_subtype] using hm
  apply delta_nonempty_of_maximum_outside
  refine ⟨A.map H.subtype,hf,?_⟩
  intro hn
  exact hAN ((map_le_map_iff_of_injective H.subtype_injective).mp hn)

/-- An actual Delta member escapes the fixed Sylow subgroup. -/
theorem ChosenSmallSource.exists_delta_outside
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    ∃ A ∈ delta H, ¬ A ≤ (T : Subgroup G) :=
  exists_delta_not_le_sylow hH.1.1.2 T.isPGroup' (h.delta_nonempty hH)

omit [Finite G] in
/-- The fixed-centralizer identity forces the literal intersection B(A) to
move V whenever A lies outside its H-normalizer. -/
theorem ChosenGeometry.delta_intersection_moves
    {T V H A : Subgroup G}
    (hNV : H ⊓ normalizer (V : Set G) = T)
    (hA : A ∈ delta H) (hAT : ¬ A ≤ T)
    (hfix : conjugateSpan H V ⊓ centralizer (A : Set G) =
      conjugateSpan H V ⊓ centralizer (A ⊓ twoCoreIn H : Subgroup G)) :
    ¬ A ⊓ twoCoreIn H ≤ centralizer (V : Set G) := by
  intro hc
  have hVU : V ≤ conjugateSpan H V := by
    rw [conjugateSpan_eq]
    exact le_conjugateSpanBy _ _
  have hVCA : V ≤ centralizer (A : Set G) := by
    have hh := le_inf hVU (le_centralizer_iff.mp hc)
    rw [← hfix] at hh
    exact hh.trans inf_le_right
  apply hAT
  rw [← hNV]
  exact le_inf hA.1.1 ((le_centralizer_iff.mp hVCA).trans
    (Subgroup.centralizer_le_normalizer _))

/-- The set difference of image families is inhabited; no choice of a
preimage in T can represent this moving intersection. The remaining
fixed-centralizer and normalizer inputs belong to this offender-plane owner. -/
theorem ChosenSmallSource.sigmaOutside_nonempty_of_fixed_centralizers
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hNV : H ⊓ normalizer (V : Set G) = (T : Subgroup G))
    (hfix : ∀ A ∈ delta H,
      conjugateSpan H V ⊓ centralizer (A : Set G) =
        conjugateSpan H V ⊓ centralizer (A ⊓ twoCoreIn H : Subgroup G)) :
    (sigmaOutside (T : Subgroup G) H).Nonempty := by
  obtain ⟨A,hA,hAT⟩ := h.exists_delta_outside hH
  exact ⟨A ⊓ twoCoreIn H,h.sigmaOutside_of_moves hH ⟨A,hA,rfl⟩
    (delta_intersection_moves hNV hA hAT (hfix A hA))⟩

end CFSG.Quasithin.Chapter15.Section02

namespace CFSG.Quasithin.Chapter15.Section02
open ChosenGeometry Section01
variable {G : Type*} [Group G] [Finite G]

/-- The actual Sylow centralizer of the chosen orbit span is in the right
core. This is the source reduced-action input, transported through H.subtype. -/
theorem ChosenSmallSource.span_sylow_centralizer_le_core
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    (T : Subgroup G) ⊓ centralizer (conjugateSpan H V : Set G) ≤ twoCoreIn H := by
  let := h.prepared.elementary
  let d := source_chosenNormalizer_qrcConfiguration h.ambient T h.empty h.maximal
    h.centralizing h.prepared.le_selected h.prepared.nontrivial h.prepared.normalized
    h.prepared.seed_span hH
  have hq := (source_chosen_equality_inputs h.ambient T h.empty h.maximal hH h.centralizing
    h.prepared.le_selected h.prepared.nontrivial h.prepared.normalized h.prepared.seed_span
    h.prepared.le_local h.prepared.quadratic_ratio).1
  let S := T.subtype hH.1.1.2
  have hS : (S : Subgroup H).map H.subtype = T := map_subgroupOf_eq_of_le hH.1.1.2
  have hc := source_span_centralizer_sylow_le_core d h.prepared.nontrivial
    (h.prepared.inside_core H hH) (source_notFF_of_ratio_two d hq) S hS
  intro a ha
  refine ⟨⟨a,hH.1.1.2 ha.1⟩,hc ⟨ha.1,?_⟩,rfl⟩
  intro u hu
  exact Subtype.ext (ha.2 u hu)

/-- An outside Sigma member exists already from the uniform centralizer
identity. Conjugating the entire image family avoids any normalizer or
marked-wreath assumption in this selection step. Final discharge of the
uniform identity remains with qt-e-152-offender-plane. -/
theorem ChosenSmallSource.sigmaOutside_nonempty_of_uniform_fixed
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hfix : ∀ A ∈ delta H,
      conjugateSpan H V ⊓ centralizer (A : Set G) =
        conjugateSpan H V ⊓ centralizer (A ⊓ twoCoreIn H : Subgroup G)) :
    (sigmaOutside (T : Subgroup G) H).Nonempty := by
  classical
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  by_contra hn
  have hall : ∀ B ∈ sigma H, B ≤ centralizer (V : Set G) := by
    intro B hB
    have hb : B ∈ sigmaAt (T : Subgroup G) H := by
      by_contra hb
      exact hn ⟨B,hB,hb⟩
    exact h.sigmaAt_centralizes hH hb
  obtain ⟨A,hA,hAT⟩ := exists_delta_in_sylow (T.subtype hTH) (h.delta_nonempty hH)
  rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] at hAT
  have hBU := sigma_centralizes_span_of_all_centralize hall ⟨A,hA,rfl⟩
  have hUA : conjugateSpan H V ≤ centralizer (A : Set G) := by
    have he := hfix A hA
    rw [inf_eq_left.mpr (le_centralizer_iff.mp hBU)] at he
    exact inf_eq_left.mp he
  exact hA.2.1 ((le_inf hAT (le_centralizer_iff.mp hUA)).trans
    (h.span_sylow_centralizer_le_core hH))

end CFSG.Quasithin.Chapter15.Section02
