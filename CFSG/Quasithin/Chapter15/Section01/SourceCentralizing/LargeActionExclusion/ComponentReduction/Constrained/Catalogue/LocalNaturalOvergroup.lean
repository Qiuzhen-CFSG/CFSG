module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalNaturalMovingPlane

/-!
# Normal ambient carriers for the remaining natural local blocks

Chapter 1 places an S-invariant member K of the original local family in
one unique C-component A of G₁. Uniqueness makes S normalize A. The
at-most-two component orbit and the full Sylow property then make A normal
in G₁. The original nonzero central seed supplies the two-core needed to
put A in the same local family, where the containing-component theorem
also proves that A is maximal.

An escaping natural block cannot equal A: the already proved ambient
C-component Borel argument excludes that possibility. Thus the remaining
cubic field-four local block lies properly in this normal maximal carrier.
This does not identify K with a component of G₁ or make its Borel invariant
under M_Z. The proper natural embeddings remain to be excluded.

As an actual consumer, all maximal members of the original local family
now have the complete group and intersection rows, retaining the original
central quotients, both binary flag parabolics and Thompson commutator.
The original-marker application also retains its prime, row and moving
plane. The additional block clauses, whole-core A₆ reconstruction and
final source assembly remain separate obligations. Original 15.1.14 stays
explicit at its existing producer and assembly owner.

Source: Aschbacher--Smith 1.2.1(3), 1.2.4 and 1.2.6, printed pp.504--506;
15.1.20(2a) and15.1.21(i), printed pp.1094,1097--1098.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem normal_local_carrier
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hSK : d.S ≤ normalizer (K : Set G)) :
    ∃ A : Subgroup G, A ∈ Chapter1.cComponentsIn d.G1 ∧
      K ≤ A ∧ A ∈ Chapter1.LStarIn d.G1 d.S ∧
      (A.subgroupOf d.G1).Normal ∧ d.G1 ≤ normalizer (A : Set G) ∧
      ∀ B : Subgroup G, B ∈ Chapter1.cComponentsIn d.G1 → K ≤ B → B = A := by
  let := h.elementary
  have hsq : IsSQTK KnownSimple.IsKnownSimple d.G1 := caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
    ((IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left))
  have hquot : IsSQTK KnownSimple.IsKnownSimple (d.G1 ⧸ pCore 2 d.G1) := by
    refine ⟨?_,hsq.isKGroup.quotient (pCore 2 d.G1)⟩
    intro q hq ho
    let : Fact q.Prime := ⟨hq⟩
    exact (primeRank_quotient_le_of_isTwoGroup q ho (pCore 2 d.G1) pCore_isPGroup).trans
      (hsq.stronglyQuasithin q hq ho)
  obtain ⟨P,hP⟩ := s.centralizer_sylow
  have hPS : (P : Subgroup d.G1) = d.S.subgroupOf d.G1 := by
    apply map_injective d.G1.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le d.S_le_G1]
  have hlocal : K.subgroupOf d.G1 ∈ Chapter1.L d.G1 (P : Subgroup d.G1) := by
    rw [hPS]
    exact (Chapter1.mem_LIn_iff_subgroupOf d.S_le_G1 hK.1).mp hK
  obtain ⟨A0,hA0,hunique⟩ := Chapter1.Section02.index_le_two_local_component_source
    hquot P le_rfl (by simp) hlocal
  let A := A0.map d.G1.subtype
  have hAG : A ≤ d.G1 := map_subtype_le _
  have hAeq : A.subgroupOf d.G1 = A0 :=
    comap_map_eq_self_of_injective d.G1.subtype_injective _
  have hAcomp : (A.subgroupOf d.G1).IsCComponent := hAeq.symm ▸ hA0.1
  have hKA : K ≤ A := by
    simpa only [map_subgroupOf_eq_of_le hK.1] using
      (map_mono (f := d.G1.subtype) hA0.2)
  have huniqueA (B : Subgroup G) (hB : B ∈ Chapter1.cComponentsIn d.G1)
      (hKB : K ≤ B) : B = A := by
    have he := hunique (B.subgroupOf d.G1) ⟨hB.2,comap_mono hKB⟩
    simpa only [map_subgroupOf_eq_of_le hB.1] using congrArg (map d.G1.subtype) he
  have hSA0 : (P : Subgroup d.G1) ≤ normalizer (A0 : Set d.G1) := by
    intro x hx
    have hxK : x ∈ normalizer (K.subgroupOf d.G1 : Set d.G1) := by
      apply mem_normalizer_iff.mpr
      intro k
      exact mem_normalizer_iff.mp (hSK (hP ▸ mem_map_of_mem d.G1.subtype hx)) k
    have heK := mem_normalizer_iff_map_conj_eq.mp hxK
    have hinc := map_mono (f := (MulAut.conj x).toMonoidHom) hA0.2
    change (K.subgroupOf d.G1).map (MulAut.conj x).toMonoidHom = K.subgroupOf d.G1 at heK
    rw [heK] at hinc
    exact mem_normalizer_iff_map_conj_eq.mpr
      (hunique _ ⟨hA0.1.map_equiv (MulAut.conj x),hinc⟩)
  have hnA0 : A0.Normal := by
    rcases Chapter1.Section02.proposition_1_2_1_three_orbit_source hquot hA0.1 with hn | hi
    · exact hn
    · have hd := index_dvd_of_le hSA0
      rw [hi] at hd
      exact (P.not_dvd_index hd).elim
  have hGA : d.G1 ≤ normalizer (A : Set G) := by
    let := hnA0
    have hn : (⊤ : Subgroup d.G1) ≤ normalizer (A0 : Set d.G1) := by
      rw [normalizer_eq_top]
    have hh := (map_mono (f := d.G1.subtype) hn).trans
      (A0.le_normalizer_map d.G1.subtype)
    simpa only [←MonoidHom.range_eq_map,range_subtype] using hh
  have hG1H : d.G1 ∈ Chapter1.H G := by
    have hZV : d.Z1 ≤ V := d.Z1_le_fixed.trans inf_le_left
    have hZZ : d.Z1 ≤ d.G1 := hZV.trans (V.le_centralizer.trans (centralizer_le hZV))
    have hZcore : d.Z1 ≤ d.G1.pCoreIn 2 := le_pCoreIn_of_normalizes
      ((IsElementaryAbelian.isPGroup 2 V).to_le hZV) hZZ
      (Subgroup.centralizer_le_normalizer (d.Z1 : Set G))
    intro hz
    exact d.Z1_ne_bot (bot_unique (hZcore.trans hz.le))
  have hAlocal : A ∈ Chapter1.LIn d.G1 d.S := ⟨hAG,
    Chapter1.mem_L_of_cComponent hG1H s.centralizer_sylow hAG hAcomp⟩
  have hAmax : A ∈ Chapter1.LStarIn d.G1 d.S := by
    refine ⟨hAlocal,?_⟩
    intro B hB hAB
    have hBl : B.subgroupOf d.G1 ∈ Chapter1.L d.G1 (P : Subgroup d.G1) := by
      rw [hPS]
      exact (Chapter1.mem_LIn_iff_subgroupOf d.S_le_G1 hB.1).mp hB
    obtain ⟨B0,hB0,_⟩ := Chapter1.Section02.index_le_two_local_component_source
      hquot P le_rfl (by simp) hBl
    have hBB : B ≤ B0.map d.G1.subtype := by
      simpa only [map_subgroupOf_eq_of_le hB.1] using
        (map_mono (f := d.G1.subtype) hB0.2)
    have hBc : B0.map d.G1.subtype ∈ Chapter1.cComponentsIn d.G1 := by
      refine ⟨map_subtype_le _,?_⟩
      simpa only [subgroupOf,comap_map_eq_self_of_injective d.G1.subtype_injective] using hB0.1
    have he := huniqueA _ hBc (hKA.trans (hAB.trans hBB))
    exact le_antisymm (hBB.trans he.le) hAB
  exact ⟨A,⟨hAG,hAcomp⟩,hKA,hAmax,hAeq.symm ▸ hnA0,hGA,huniqueA⟩

/-- An escaping natural local block is properly contained in its unique
ambient C-component, normal in the original G₁. Thus M_Z normalizes it;
no component structure is imposed on the original K. -/
theorem PreExclusionSource.localFamily_linearTwo_strict_carrier
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    {n : ℕ} (hb : IsL2EvenBlock K n) (hp2 : p ≠ 2) :
    ∃ A : Subgroup G, A ∈ Chapter1.cComponentsIn d.G1 ∧ K < A ∧
      A ∈ Chapter1.LStarIn d.G1 d.S ∧ ¬ A ≤ d.MZ ∧
      (A.subgroupOf d.G1).Normal ∧ d.G1 ≤ normalizer (A : Set G) ∧
      ∀ B : Subgroup G, B ∈ Chapter1.cComponentsIn d.G1 → K ≤ B → B = A := by
  obtain ⟨A,hAc,hKA,hAl,hAn,hGn,hAu⟩ := normal_local_carrier (h := h) s hG hK
    (s.localFamily_linearTwo_sylow_normalizes (h := h) hG hM hJ hu hfull hK hq hout hb hp2)
  have hneKA : K ≠ A := by
    intro he
    have hc : (K.subgroupOf d.G1).IsCComponent := he.symm ▸ hAc.2
    exact hout (s.localFamily_linearTwo_le_MZ_of_cComponent (h := h)
      hG hM hJ hu hne hmany hfull hres hK hc hq hb)
  exact ⟨A,hAc,lt_of_le_of_ne hKA hneKA,hAl,fun hA => hout (hKA.trans hA),hAn,hGn,hAu⟩

/-- Every maximal member of the original local family has complete group
and intersection rows: a natural escape would have a larger local carrier.
The additional block clauses still apply only in the ambient component branch. -/
theorem PreExclusionSource.localFamily_maximal_constrained_source_rows
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p) (hp2 : p ≠ 2)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    {K : Subgroup G} (hK : K ∈ Chapter1.LStarIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K) :
    ⁅K,elementaryAbelianMaxJ d.S⁆ = K ∧ LocalConstrainedSourceRows d K := by
  obtain ⟨hm,hr⟩ := d.localFamily_constrained_rows hG hempty hM hJ hu h hK.1 hq hout hf
  refine ⟨hm,?_⟩
  cases hr with
  | naturalTwo n hb _ _ =>
    obtain ⟨A,_,hKA,hA,_⟩ := s.localFamily_linearTwo_strict_carrier (h := h)
      hG hM hJ hu hne hmany hfull hres hK.1 hq hout hb hp2
    exact (hKA.ne (hK.2 A hA.1 hKA.le).symm).elim
  | alternatingFive hb he hc => exact .alternatingFive hb he hc
  | small model equiv marking => exact .small model equiv marking
  | linear n hn e t ht hz hm => exact .linear n hn e t ht hz hm

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original marker keeps its prime, planes and centralizer. Every
natural escape is a proper subgroup of a unique normal ambient component,
while every maximal local member has the full group and intersection rows.
The proper natural embeddings and the additional block clauses remain
obligations of the original source assembly. -/
theorem PreparedChosenModule.source_preExclusion_local_natural_carriers
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hp : m.prime = 3 ∨ m.prime = 5)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → ∀ n : ℕ, IsL2EvenBlock K n →
          m.prime = 3 ∧ n = 2 ∧ m.movingPlane ≤ (blockU K).map K.subtype ∧
            Nat.card m.movingPlane = 4 ∧
            ∃ A : Subgroup G, A ∈ Chapter1.cComponentsIn d.G1 ∧ K < A ∧
              A ∈ Chapter1.LStarIn d.G1 d.S ∧ ¬ A ≤ d.MZ ∧
              (A.subgroupOf d.G1).Normal ∧ d.G1 ≤ normalizer (A : Set G) ∧
              ∀ B : Subgroup G, B ∈ Chapter1.cComponentsIn d.G1 → K ≤ B → B = A) ∧
      (∀ K ∈ Chapter1.LStarIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → generalizedFitting K = pCore 2 K →
          ⁅K,elementaryAbelianMaxJ d.S⁆ = K ∧ CaseIComponentData.LocalConstrainedSourceRows d K) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_,?_⟩
  · intro K hK hq hout n hb
    obtain ⟨hp3,hn,hW,hcard⟩ := s.localFamily_linearTwo_moving_plane_four (h := h)
      hp hG hM hJ hu hfull hK hq hout hb
    have hG1 : d.G1 = centralizer (m.Z1 : Set G) := by
      change centralizer (d.Z1 : Set G) = _
      rw [hZ]
    rw [hG1] at hW hcard
    exact ⟨hp3,hn,hW,hcard,s.localFamily_linearTwo_strict_carrier (h := h)
      hG hM hJ hu hne hmany hfull hres hK hq hout hb (by omega)⟩
  · intro K hK hq hout hf
    exact s.localFamily_maximal_constrained_source_rows (h := h) (by omega)
      hG hempty hM hJ hu hne hmany hfull hres hK hq hout hf

end CFSG.Quasithin.Chapter15.Section01
