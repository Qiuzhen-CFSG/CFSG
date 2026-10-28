module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalNaturalCarrierSieve
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SevenCentralizer
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.BlockRecognition.Matching.Ordinary
public import Theory.SpecificGroups.FFG2DerivedCenter
public import Theory.SpecificGroups.Alternating.SevenFiveSection

/-!
# Natural local members with a constrained selected carrier

An escaping natural local member K lies properly in the original selected
component L. The finite-section sieve makes a constrained L short with
central quotient A₇. Every reduced FF image is centerless except the cubic
A₆ row, so this central quotient identifies the actual FF image as A₇.
The existing whole-block reconstruction and exceptional-block exclusion
therefore make the original L an ordinary A₇ block.

The literal inclusion K ≤ L now gives a contradiction. In the A₇ quotient,
the two-kernel image of K has trivial two-core. Thus the restricted kernel
is exactly O₂(K), and mapping commutators gives U(K) ≤ U(L), including the
entire fixed layer of K. The original full Sylow normalizes K. The proved
five-letter restriction theorem distinguishes its natural SL₂(4) plane
quotient from the permutation-module section of the ordinary A₇ block.
No equality between the moving plane and U(K) is used.

Consequently every natural local member lies in M_Z whenever the original
selected L is constrained. This closes the missing Borel branch and gives
all group/intersection rows for that entire original local family. The
original-marker application also records that any remaining natural escape
has an ordinary selected carrier, retaining its field-four restriction,
original moving plane, strict containment, normality and maximality.
The ordinary-carrier embeddings, additional source block clauses and final
15.1.22 assembly remain separate obligations of this same catalogue owner.
Original 15.1.14 and whole-core A₆ reconstruction retain their producers.

Source: Aschbacher--Smith 15.1.20(2), printed pp.1094--1095;
C.5.13, printed p.163, for the natural-versus-permutation restriction.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem centerless_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hz : center B = ⊥) : center A = ⊥ := by
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [FixedElementary.map_center,hz,Subgroup.map_bot]

private theorem reduced_centerless_or_six {A : Type*} [Group A]
    (hm : ReducedFFModel A) :
    center A = ⊥ ∨ Nonempty ((A ⧸ center A) ≃* alternatingGroup (Fin 6)) := by
  cases hm with
  | linearTwo F e => exact Or.inl (centerless_of_equiv e Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot)
  | linearThree e => exact Or.inl (centerless_of_equiv e (_root_.BinaryLinear.OuterCyclic.binary_center_eq_bot (by decide)))
  | g2DerivedTwo e => exact Or.inl (centerless_of_equiv e Theory.SpecificGroups.g2_derived_two_center_eq_bot)
  | alternating n hn e => exact Or.inl (centerless_of_equiv e (alternatingGroup.center_eq_bot (by simpa using (show 4 ≤ n by omega))))
  | linearFiveTwo e => exact Or.inl (centerless_of_equiv e (_root_.BinaryLinear.OuterCyclic.binary_center_eq_bot (by decide)))
  | tripleSix _ e => exact Or.inr ⟨e⟩

private theorem reduced_seven {A : Type*} [Group A]
    (hm : ReducedFFModel A) (e : (A ⧸ center A) ≃* alternatingGroup (Fin 7)) :
    Nonempty (A ≃* alternatingGroup (Fin 7)) := by
  rcases reduced_centerless_or_six hm with hz | hs
  · exact ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.trans e⟩
  · obtain ⟨es⟩ := hs
    have hc := Nat.card_congr (es.symm.trans e).toEquiv
    rw [nat_card_alternatingGroup,nat_card_alternatingGroup,Nat.card_fin,Nat.card_fin] at hc
    norm_num at hc

private theorem natural_not_in_seven {A : Type*} [Group A] [Finite A]
    (B : Subgroup A) (hB : IsL2EvenBlock B 2) (hA : IsAlternatingBlock A 7)
    (P : Sylow 2 A) (hP : (P : Subgroup A) ≤ normalizer (B : Set A)) : False := by
  obtain ⟨_,⟨m⟩,_⟩ := hA.2.2
  let q := QuotientGroup.mk' (pCore 2 A)
  let f := m.quotientIso.toMonoidHom.comp q
  have hfk : f.ker = pCore 2 A := by
    rw [MonoidHom.ker_comp_of_injective _ _ m.quotientIso.injective,QuotientGroup.ker_mk']
  have hk : IsPGroup 2 (f.subgroupMap B).ker := by
    rw [ker_subgroupMap,hfk]
    exact pCore_isPGroup.comap_subtype
  have he := (alternatingGroup.SevenFiveSection.image_twoCore_eq_bot_and_ker_eq f B hk
    hB.four_quotient_alternatingFive.some).2
  have hkq : (q.comp B.subtype).ker = pCore 2 B := by
    rw [ker_subgroupMap,hfk] at he
    calc
      (q.comp B.subtype).ker = (pCore 2 A).comap B.subtype := by
        ext b
        exact QuotientGroup.eq_one_iff (b : A)
      _ = pCore 2 B := he
  have hU : (blockU B).map B.subtype ≤ blockU A := by
    rw [blockU,map_commutator]
    apply commutator_mono ?_ le_top
    apply map_le_iff_le_comap.mpr
    intro b hb
    exact (QuotientGroup.eq_one_iff (b : A)).mp (hkq.ge hb)
  exact ChapterC.Section05.NormalizerControl.Matching.no_natural_two_in_alternating_seven
    hB hA B.subtype B.subtype_injective hU hkq P (by simpa only [range_subtype] using hP)


/-- A natural local member cannot escape M_Z when its original selected carrier
is constrained. The carrier sieve, whole A₇ reconstruction and the literal
full-Sylow natural-versus-permutation module comparison discharge this branch. -/
theorem PreExclusionSource.localFamily_linearTwo_le_MZ_of_constrained_carrier
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
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
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {n : ℕ} (hb : IsL2EvenBlock K n)
    (hf : generalizedFitting d.L = pCore 2 d.L) : K ≤ d.MZ := by
  by_contra hout
  obtain ⟨_,hn,_,_⟩ := s.localFamily_linearTwo_moving_plane_four (h := h)
    hp hG hM hJ hu hfull hK hq hout hb
  obtain ⟨hKL,_,_,_,_⟩ := s.localFamily_linearTwo_selected_carrier (h := h)
    hG hM hJ hu hne hmany hfull hres hK hq hout hb (by omega)
  obtain ⟨e⟩ := s.localFamily_linearTwo_constrained_carrier_seven (h := h)
    hp hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb hf
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf
  obtain ⟨eA⟩ := reduced_seven
    (s.constrained_reduced_ff_model (h := h) hG hempty hM hJ hu hf)
    ((a.coreCenterQuotientEquiv s.quasisimple).symm.trans e)
  have hL := (s.constrained_seven_block (h := h) hG hempty hM hJ hu hf eA).1
  let B := K.subgroupOf d.L
  have hB : IsL2EvenBlock B 2 :=
    (hn ▸ hb : IsL2EvenBlock K 2).of_mulEquiv (subgroupOfEquivOfLe hKL.le).symm
  obtain ⟨P,hP⟩ := s.component_sylow
  have hSN := s.localFamily_linearTwo_sylow_normalizes (h := h)
    hG hM hJ hu hfull hK hq hout hb (by omega)
  have hPB : (P : Subgroup d.L) ≤ normalizer (B : Set d.L) := by
    apply le_normalizer_iff.mpr
    intro l hl k hk
    have hlS : l.val ∈ d.S := (hP ▸ mem_map_of_mem d.L.subtype hl).1
    exact le_normalizer_iff.mp hSN l hlS k hk
  exact natural_not_in_seven B hB hL P hPB

/-- All group and intersection clauses of 15.1.20(2) on the original local
family when its selected carrier is constrained. The natural branch is
excluded, rather than supplied with a new Borel-normalization premise. -/
theorem PreExclusionSource.localFamily_source_rows_of_constrained_carrier
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
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
    (hL : generalizedFitting d.L = pCore 2 d.L)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K) :
    ⁅K,elementaryAbelianMaxJ d.S⁆ = K ∧ LocalConstrainedSourceRows d K := by
  obtain ⟨hm,hr⟩ := d.localFamily_constrained_rows hG hempty hM hJ hu h hK hq hout hf
  refine ⟨hm,?_⟩
  cases hr with
  | naturalTwo n hb _ _ =>
    exact (hout (s.localFamily_linearTwo_le_MZ_of_constrained_carrier (h := h)
      hp hG hempty hM hJ hu hne hmany hfull hres hK hq hb hL)).elim
  | alternatingFive hb he hc => exact .alternatingFive hb he hc
  | small model equiv marking => exact .small model equiv marking
  | linear n hn e t ht hz hm => exact .linear n hn e t ht hz hm

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- At the literal original marker, natural escapes have ordinary carriers;
if the selected carrier is constrained, every eligible local member has the
full group and intersection rows. The same prime, component and planes are
retained, before any exchanged selection. -/
theorem PreparedChosenModule.source_preExclusion_local_carrier_rows
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
            Nat.card m.movingPlane = 4 ∧ K < d.L ∧
            d.L ∈ Chapter1.LStarIn d.G1 d.S ∧
            (d.L.subgroupOf d.G1).Normal ∧ d.G1 ≤ normalizer (d.L : Set G) ∧
            IsComponent d.G1 (d.L.subgroupOf d.G1)) ∧
      (generalizedFitting d.L = pCore 2 d.L →
        ∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
          ¬ K ≤ d.MZ → generalizedFitting K = pCore 2 K →
            ⁅K,elementaryAbelianMaxJ d.S⁆ = K ∧
              CaseIComponentData.LocalConstrainedSourceRows d K) := by
  obtain ⟨d,hZ,hr,s,hfamily⟩ := h.source_preExclusion_local_natural_selected_carrier
    hG T hempty hM hmany hJ hu hne hfull m hp hres
  refine ⟨d,hZ,hr,s,?_,?_⟩
  · intro K hK hq hout n hb
    obtain ⟨hp3,hn,hW,hcard,hKL,hmax,hLn,hGn,hbranch⟩ := hfamily K hK hq hout n hb
    refine ⟨hp3,hn,hW,hcard,hKL,hmax,hLn,hGn,?_⟩
    rcases hbranch with hc | ⟨hf,_⟩
    · exact hc
    · exact (hout (s.localFamily_linearTwo_le_MZ_of_constrained_carrier (h := h)
        hp hG hempty hM hJ hu hne hmany hfull hres hK hq hb hf)).elim
  · intro hf K hK hq hout hfit
    exact s.localFamily_source_rows_of_constrained_carrier (h := h)
      hp hG hempty hM hJ hu hne hmany hfull hres hf hK hq hout hfit

end CFSG.Quasithin.Chapter15.Section01
