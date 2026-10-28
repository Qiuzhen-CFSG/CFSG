module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Constrained.Module
public import Theory.GroupTheory.SylowFixedConjugateSpanSplitting
public import Theory.GroupTheory.Commutator.SylowFixedSeed

/-!
# The original constrained span and its moved seed

The same exchanged line Z2 is fixed by S and generates U under L. Normality
of L identifies the full LS commutator with UL. Sylow averaging then splits
U over UL and the actual LS-fixed subgroup, with a fixed representative for
each original seed element. This supplies the B.2.14 input preceding 15.1.28
in Aschbacher--Smith, printed pp.1102--1103.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Theory.SpecificGroups.BinaryComponentResidual ChapterA.Section05To06 Section03 Section03.InitialSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

theorem U_eq_span_LS (d : CaseIComponentData T M Mc V) (s : d.NineSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) :
    conjugateSpanBy (d.Z2 t) (d.L ⊔ d.S) = d.U t := by
  let := s.quasisimple
  exact conjugateSpanBy_sup_of_normalizes_seed _ _ _
    ((le_centralizer_iff.mp (d.Z2_le_centralizer_S s t ht)).trans
      (Subgroup.centralizer_le_normalizer _))
    (d.S_le_G1.trans (d.G1_normalizes_L hG h hf))

theorem U_commutator_LS (d : CaseIComponentData T M Mc V) (s : d.NineSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) :
    ⁅d.U t,d.L ⊔ d.S⁆ = d.UL t := by
  let := s.quasisimple
  let D := d.L ⊔ d.S
  have hZD : d.Z2 t ≤ D := (le_conjugateSpanBy _ _).trans
    ((d.U_le_Q1 s hG hM hu h hi hf t ht).trans ((d.Q1_le_S s hu).trans le_sup_right))
  have hh := commutator_conjugateSpan_eq_of_fixed_supplement
    (d.Z2 t) D D d.L d.S hZD le_sup_left le_sup_right D.le_normalizer
    (sup_le d.L.le_normalizer (d.S_le_G1.trans (d.G1_normalizes_L hG h hf)))
    le_sup_left le_rfl (d.Z2_le_centralizer_S s t ht)
  rwa [d.U_eq_span_LS s hG h hf t ht] at hh

/-- The fixed factor is fixed by the original full Sylow supplement as well as L. -/
theorem U_split_LS (d : CaseIComponentData T M Mc V) (s : d.NineSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) :
    d.U t = d.UL t ⊔ (d.U t ⊓ centralizer ((d.L ⊔ d.S : Subgroup G) : Set G)) := by
  have he := d.U_eq_span_LS s hG h hf t ht
  let := d.U_elementary s hG hM hu h hi hf t ht
  let : IsElementaryAbelian 2 (conjugateSpanBy (d.Z2 t) (d.L ⊔ d.S)) := he.symm ▸ inferInstance
  obtain ⟨P,hP⟩ := s.centralizer_sylow.restrict (show d.S ≤ d.L ⊔ d.S from le_sup_right)
    (sup_le d.L_component.1 d.S_le_G1)
  have hs := conjugateSpan_split_of_sylow_fixed P (hP.symm ▸ d.Z2_le_centralizer_S s t ht)
  rw [he,d.U_commutator_LS s hG hM hu h hi hf t ht] at hs
  exact hs

/-- The source's original splitting with the L-fixed factor. -/
theorem U_split (d : CaseIComponentData T M Mc V) (s : d.NineSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) :
    d.U t = d.UL t ⊔ (d.U t ⊓ centralizer (d.L : Set G)) := by
  apply le_antisymm
  · exact (d.U_split_LS s hG hM hu h hi hf t ht).le.trans
      (sup_le_sup le_rfl (inf_le_inf_left _ (centralizer_le (show d.L ≤ d.L ⊔ d.S from le_sup_left))))
  · exact sup_le (le_normalizer_iff_commutator_le_left.mp
      (le_normalizer_conjugateSpanBy (d.Z2 t) d.L)) inf_le_left

/-- The original seed has an LS-fixed representative modulo UL. -/
theorem Z2_fixed_coset (d : CaseIComponentData T M Mc V) (s : d.NineSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) {z : G} (hz : z ∈ d.Z2 t) :
    ∃ u ∈ d.UL t, u * z ∈ d.U t ⊓ centralizer ((d.L ⊔ d.S : Subgroup G) : Set G) := by
  have he := d.U_eq_span_LS s hG h hf t ht
  let := d.U_elementary s hG hM hu h hi hf t ht
  let : IsElementaryAbelian 2 (conjugateSpanBy (d.Z2 t) (d.L ⊔ d.S)) := he.symm ▸ inferInstance
  obtain ⟨P,hP⟩ := s.centralizer_sylow.restrict (show d.S ≤ d.L ⊔ d.S from le_sup_right)
    (sup_le d.L_component.1 d.S_le_G1)
  have hs := conjugateSpan_fixed_coset_of_sylow P
    (hP.symm ▸ d.Z2_le_centralizer_S s t ht) hz
  rw [he,d.U_commutator_LS s hG hM hu h hi hf t ht] at hs
  exact hs

/-- A nonzero moved seed has exactly the original seed stabilizer in L. -/
theorem Z2_moved_seed (d : CaseIComponentData T M Mc V) (s : d.NineSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    ∃ z ∈ d.Z2 t, z ≠ 1 ∧ ∃ u ∈ d.UL t, u ≠ 1 ∧
      u ∈ centralizer (d.S : Set G) ∧
      u * z ∈ d.U t ⊓ centralizer ((d.L ⊔ d.S : Subgroup G) : Set G) ∧
      d.L ⊓ centralizer ({u} : Set G) = d.L ⊓ centralizer (d.Z2 t : Set G) ∧
      d.L ⊓ centralizer ({u} : Set G) ≤ d.ML := by
  classical
  obtain ⟨z,hz,hzC⟩ := Set.not_subset.mp (d.Z2_not_centralizes_L s hM hu h t ht htS)
  have hzne : z ≠ 1 := by
    rintro rfl
    exact hzC (one_mem _)
  obtain ⟨u,huU,huC⟩ := d.Z2_fixed_coset s hG hM hu h hi hf t ht hz
  have huL : u * z ∈ centralizer (d.L : Set G) := centralizer_le (show d.L ≤ d.L ⊔ d.S from le_sup_left) huC.2
  have hune : u ≠ 1 := by
    intro hue
    apply hzC
    intro l hl
    simpa only [hue,one_mul] using huL l hl
  have huS : u ∈ centralizer (d.S : Set G) := by
    have hh := (centralizer (d.S : Set G)).mul_mem
      (centralizer_le (show d.S ≤ d.L ⊔ d.S from le_sup_right) huC.2)
      ((centralizer (d.S : Set G)).inv_mem (d.Z2_le_centralizer_S s t ht hz))
    simpa only [mul_inv_cancel_right] using hh
  have hZcard : Nat.card (d.Z2 t) = 2 :=
    (card_map_of_injective (MulAut.conj t).injective).trans s.marked_card
  have hcen : centralizer ({z} : Set G) = centralizer (d.Z2 t : Set G) := by
    ext x
    constructor
    · intro hx a ha
      by_cases ha1 : a = 1
      · simp only [ha1,one_mul,mul_one]
      obtain ⟨w,_,hw⟩ := (Nat.card_eq_two_iff' (1 : d.Z2 t)).mp hZcard
      have haz : a = z := congrArg Subtype.val
        ((hw ⟨a,ha⟩ (fun he => ha1 (congrArg Subtype.val he))).trans
          (hw ⟨z,hz⟩ (fun he => hzne (congrArg Subtype.val he))).symm)
      simpa only [haz] using (mem_centralizer_singleton_iff.mp hx).symm
    · intro hx
      exact mem_centralizer_singleton_iff.mpr (hx z hz).symm
  have he : d.L ⊓ centralizer ({u} : Set G) = d.L ⊓ centralizer (d.Z2 t : Set G) := by
    rw [←hcen]
    ext x
    constructor
    · rintro ⟨hxL,hxu⟩
      refine ⟨hxL,mem_centralizer_singleton_iff.mpr ?_⟩
      have hc : Commute x (u * z) := huL x hxL
      have hh := (show Commute x u from mem_centralizer_singleton_iff.mp hxu).inv_right.mul_right hc
      simpa only [inv_mul_cancel_left] using hh.eq
    · rintro ⟨hxL,hxz⟩
      refine ⟨hxL,mem_centralizer_singleton_iff.mpr ?_⟩
      have hc : Commute x (u * z) := huL x hxL
      have hh := hc.mul_right (show Commute x z from mem_centralizer_singleton_iff.mp hxz).inv_right
      simpa only [mul_inv_cancel_right] using hh.eq
  refine ⟨z,hz,hzne,u,huU,hune,huS,huC,he,?_⟩
  rw [he]
  exact le_inf ((inf_le_inf_right _ d.L_component.1).trans
    (d.Z2_centralizer_le_MZ s hM hu h t ht htS)) inf_le_left

/-- The moved line has order two, is S-fixed, and retains the distinguished stabilizer. -/
theorem Z2_moved_line (d : CaseIComponentData T M Mc V) (s : d.NineSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    ∃ ZU : Subgroup G, ZU ≤ d.UL t ∧ Nat.card ZU = 2 ∧
      ZU ≤ centralizer (d.S : Set G) ∧
      d.L ⊓ centralizer (ZU : Set G) = d.L ⊓ centralizer (d.Z2 t : Set G) ∧
      d.L ⊓ centralizer (ZU : Set G) ≤ d.ML := by
  obtain ⟨z,hz,hzne,u,huU,hune,huS,huC,he,hbound⟩ :=
    d.Z2_moved_seed s hG hM hu h hi hf t ht htS
  let := d.U_elementary s hG hM hu h hi hf t ht
  have huU' : u ∈ d.U t := le_normalizer_iff_commutator_le_left.mp
    (le_normalizer_conjugateSpanBy (d.Z2 t) d.L) huU
  refine ⟨zpowers u,zpowers_le.mpr huU,?_,zpowers_le.mpr huS,?_,?_⟩
  · rw [Nat.card_zpowers]
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian u huU') hune
  · simpa only [zpowers_eq_closure,centralizer_closure] using he
  · simpa only [zpowers_eq_closure,centralizer_closure] using hbound

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
