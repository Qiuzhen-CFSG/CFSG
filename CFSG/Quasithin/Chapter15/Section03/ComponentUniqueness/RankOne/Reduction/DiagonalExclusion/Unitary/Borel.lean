module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.DiagonalExclusion.Local
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.UnitaryLocal.Placement
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary
public import CFSG.Quasithin.MainConverse.RankOneLocal
public import Theory.SpecificGroups.SU3.EvenProjectiveComparison
public import Theory.SpecificGroups.SU3.FixedFieldTwo
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# The invariant unitary Borel before the inner-action step

The relatively subnormal component inherits the given Sylow intersection.
The unique proper Sylow overgroup makes that intersection the two-core of
M ∩ L, so Y₊S preserves its normalizer. The actual unitary model is centerless;
component perfectness excludes PSU₃(2), and the intrinsic even-characteristic
calculation supplies characteristic two for the Borel. Source 15.3.33(1)
then places the Borel in M ∩ I.

No rank-two assumption on Y₊ or nontrivial intersection residual is used.
Source: Aschbacher--Smith, 15.3.43, printed p.1139, with F.1.3(1).
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterF.Source
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.DiagonalExclusion
variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L : Subgroup G}

omit [Finite G] in
/-- The component is nontrivial and perfect, independently of intersection residuals. -/
theorem LocalSetup.unitary_component_nonsolvable (h : LocalSetup Yplus S M I L) :
    ¬ Group.IsSolvable L := by
  let e := subgroupOfEquivOfLe h.component_le
  let := h.component.2
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : Nontrivial L := (Subgroup.nontrivial_iff_ne_bot L).mpr (by
    intro he
    exact h.component_outside (he ▸ bot_le))
  exact Group.IsPerfect.not_isSolvable L

/-- Restriction to the component retains the literal S ∩ L. -/
theorem LocalSetup.unitary_component_sylow (h : LocalSetup Yplus S M I L) :
    ∃ P : Sylow 2 L, (P : Subgroup L).map L.subtype = S ⊓ L := by
  obtain ⟨Q, hQ⟩ := h.sylow
  obtain ⟨P, hP⟩ := Candidates.UnitaryLocal.component_sylow
    h.component_le h.component.1 Q hQ
  exact ⟨P, by rw [hP, subgroupOf_map_subtype]⟩

omit [Finite G] in
/-- Simplicity is inherited from the component after the actual model kills its center. -/
theorem LocalSetup.unitary_component_simple (h : LocalSetup Yplus S M I L)
    {n : ℕ} (hn : 0 < n) (hm : ClassicalGroup.IsPSU L 3 (2 ^ n)) :
    IsSimpleGroup L := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨f⟩⟩ := hm
  let e := subgroupOfEquivOfLe h.component_le
  let := h.component.2
  have hz : center (L.subgroupOf I) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    apply (e.trans f).injective
    have hh := (centerCongr (e.trans f) ⟨x, hx⟩).property
    have hz := BenderSuzuki.MatrixGroups.HermitianForm.EvenProjectiveComparison.center_eq_bot
      J hn hcard hconj
    change (e.trans f) x ∈ center (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) at hh
    rw [hz, mem_bot] at hh
    exact hh.trans (map_one _).symm
  let : IsSimpleGroup ((L.subgroupOf I) ⧸ center (L.subgroupOf I)) := IsQuasisimple.simple
  exact (((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).trans e).symm.isSimpleGroup

omit [Finite G] in
/-- The small fixed field is excluded by component perfectness, not by a family tag. -/
theorem LocalSetup.unitary_degree_ge_two (h : LocalSetup Yplus S M I L)
    {n : ℕ} (hn : 0 < n) (hm : ClassicalGroup.IsPSU L 3 (2 ^ n)) : 2 ≤ n := by
  by_contra hn2
  have he : n = 1 := by omega
  subst n
  obtain ⟨F, _, _, J, hcard, hconj, ⟨f⟩⟩ := hm
  let := BenderSuzuki.MatrixGroups.HermitianForm.FixedFieldTwo.projective_isSolvable J
    (by simpa using hcard) (by simpa using hconj)
  exact h.unitary_component_nonsolvable
    (Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective)

/-- The actual unitary model gives the relative rank-one Borel facts. -/
theorem LocalSetup.unitary_borel_facts (h : LocalSetup Yplus S M I L)
    {n : ℕ} (hn : 0 < n) (hm : ClassicalGroup.IsPSU L 3 (2 ^ n)) :
    RankOneBorelFacts L S := by
  obtain ⟨P, hP⟩ := h.unitary_component_sylow
  apply rankOneBorelFacts_of_sylow L S P hP
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hm
  apply rankOneSylowFacts_of_equiv P e
  exact rankOneSylowFacts_psu3 J n hn hcard hconj _

private theorem intersection_twoCore (h : LocalSetup Yplus S M I L)
    (hf : RankOneBorelFacts L S) : (M ⊓ L : Subgroup G).pCoreIn 2 = S ⊓ L := by
  have hML : M ⊓ L ≤ borel L S := hf.unique_maximal _
    (inf_le_inf_right L h.sylow_le)
    (lt_of_le_of_ne inf_le_right (fun he => h.component_outside
      (he.symm.le.trans inf_le_left)))
  obtain ⟨P, hP⟩ := h.unitary_component_sylow
  have hPD : (P : Subgroup L) ≤ (M ⊓ L : Subgroup G).subgroupOf L := by
    intro x hx
    exact inf_le_inf_right L h.sylow_le (hP ▸ mem_map_of_mem L.subtype hx)
  apply le_antisymm
  · have hc := pCoreIn_le_sylow ((M ⊓ L : Subgroup G).subgroupOf L) (P.subtype hPD)
    have hc' := map_mono (f := L.subtype) hc
    rw [map_pCoreIn_of_injective 2 _ L.subtype L.subtype_injective,
      map_subgroupOf_eq_of_le inf_le_right] at hc'
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hPD, hP] using hc'
  · apply le_pCoreIn_of_normalizes _ (inf_le_inf_right L h.sylow_le)
      (hML.trans inf_le_right)
    rw [← hP]
    exact P.isPGroup'.map L.subtype

private theorem borel_characteristicTwo (h : LocalSetup Yplus S M I L)
    {n : ℕ} (hn : 0 < n) (hm : ClassicalGroup.IsPSU L 3 (2 ^ n)) :
    generalizedFitting (borel L S) = pCore 2 (borel L S) := by
  let := h.unitary_component_simple hn hm
  have hna : ¬ IsMulCommutative L := by
    intro ha
    let := ha
    exact h.unitary_component_nonsolvable (Group.isSolvable_of_comm (fun a b => mul_comm' a b))
  have he := MainConverse.psu3_evenCharacteristic hna (h.unitary_degree_ge_two hn hm) hm
  obtain ⟨P, hP⟩ := h.unitary_component_sylow
  have hf : RankOneSylowFacts P := by
    obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hm
    apply rankOneSylowFacts_of_equiv P e
    exact rankOneSylowFacts_psu3 J n hn hcard hconj _
  let B : Subgroup L := normalizer (P : Set L)
  have hne : (P : Subgroup L) ≠ ⊥ := by
    intro hp
    have hh := hf.proper
    change normalizer ((P : Subgroup L) : Set L) < ⊤ at hh
    rw [hp] at hh
    exact hh.ne (⊥ : Subgroup L).normalizer_eq_top
  have hmax : IsMaximalTwoLocal B := by
    refine ⟨⟨P, hne, P.isPGroup', rfl⟩, ?_⟩
    intro N hN hBN
    exact hf.unique_maximal N ((P : Subgroup L).le_normalizer.trans hBN)
      (lt_top_iff_ne_top.mpr (twoLocal_ne_top_of_nonabelian_simple hna hN))
  have hc := he P B hmax (P : Subgroup L).le_normalizer
  have hmap : B.map L.subtype = borel L S := by
    have hh : (S ⊓ L).subgroupOf L = (P : Subgroup L) := by
      rw [← hP]
      exact comap_map_eq_self_of_injective L.subtype_injective _
    change (normalizer ((P : Subgroup L) : Set L)).map L.subtype = _
    rw [← hh, ← subgroupOf_normalizer_eq inf_le_right,
      subgroupOf, map_comap_eq, range_subtype]
    rfl
  let e : B ≃* borel L S :=
    (B.equivMapOfInjective L.subtype L.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  exact generalizedFitting_eq_pCore_of_selfCentralizing 2
    ((Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp hc)

/-- Construct the invariant characteristic-two Borel and apply source 15.3.33(1). -/
theorem LocalSetup.unitary_borel (h : LocalSetup Yplus S M I L)
    (horbit : L = localSpan L S)
    {n : ℕ} (hn : 0 < n) (hm : ClassicalGroup.IsPSU L 3 (2 ^ n)) :
    Yplus ⊔ S ≤ normalizer (borel L S : Set G) ∧
      generalizedFitting (borel L S) = pCore 2 (borel L S) ∧
      borel L S ≤ M ⊓ I := by
  have hf := h.unitary_borel_facts hn hm
  have hML : Yplus ⊔ S ≤ normalizer ((M ⊓ L : Subgroup G) : Set G) :=
    le_normalizer_inf
      ((sup_le (h.yplus_le.trans inf_le_left) h.sylow_le).trans M.le_normalizer)
      (h.join_normalizes horbit)
  have hT : Yplus ⊔ S ≤ normalizer ((S ⊓ L : Subgroup G) : Set G) := by
    rw [← intersection_twoCore h hf]
    exact hML.trans (normalizer_le_normalizer_characteristic_image
      (M ⊓ L) (pCore 2 (M ⊓ L : Subgroup G)))
  have hB : Yplus ⊔ S ≤ normalizer (borel L S : Set G) :=
    le_normalizer_inf (h.join_normalizes horbit)
      (hT.trans (normalizer ((S ⊓ L : Subgroup G) : Set G)).le_normalizer)
  have hc := borel_characteristicTwo h hn hm
  exact ⟨hB, hc, h.characteristic_two_containment _
    (inf_le_left.trans horbit.le) hB hc⟩

end CFSG.Quasithin.Chapter15.Section03.RankOne.DiagonalExclusion
