module

public import Stellmacher.Recognition.FongWreathedFusionLocal
public import Stellmacher.Recognition.FongWreathedOddCentralizers
public import Theory.GroupAction.OddInvariantSylow
public import Theory.GroupTheory.CentralizerOddCore
public import Theory.GroupTheory.CyclicNormalCentralizer
public import Theory.GroupTheory.PrimeOrderSylowArithmetic
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# An order-twenty witness from an even five-centralizer

Let `S` be a wreathed Sylow two-subgroup in a finite simple group.  If an
order-five element has an even centralizer, its centralizing involution can be
conjugated to Fong's `J`.  The five-element then lies in the odd core of
`C(J)`, whose quotient has order 96.  An invariant Sylow-five subgroup of that
odd core is normalized by the chosen Sylow two-subgroup.  The derived subgroup
of the latter contains `XF²`; the derived-group centralizer lemma therefore
makes `XF²` commute with the normalized five-subgroup.  Sylow conjugacy inside
the odd core puts a conjugate of the original five-element in that subgroup,
and the commuting order-four and order-five elements give order twenty.

Source: Fong, *Some Sylow subgroups of order 32 and a characterization of
U(3,3)*, printed p. 74.
-/

namespace Stellmacher.Recognition.FongWreathed

open ABG
open Stellmacher.Recognition.FongWreathedIntrinsic

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]


private theorem commutator_mem_of_map_eq
    {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) {x : A} (hx : x ∈ _root_.commutator A) :
    f x ∈ _root_.commutator B := by
  have hmap : Subgroup.map f (_root_.commutator A) = _root_.commutator B := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
    rfl
  exact hmap ▸ Subgroup.mem_map_of_mem f hx

/-- An even order-five centralizer produces an element of order twenty. -/
public theorem exists_order_twenty_of_even_five_centralizer
    (S : Sylow 2 G) (hS : ABG.IsWreathedOfHeight S 2)
    (x : G) (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))]
    (hG : Nat.card G = 90720)
    {s : G} (hs : orderOf s = 5)
    (heven : 2 ∣ Nat.card (Subgroup.centralizer ({s} : Set G)))
    (P : ABG.Wreathed.Presentation S 2) :
    ∃ y : G, orderOf y = 20 := by
  have _hS := hS
  let Cs := Subgroup.centralizer ({s} : Set G)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Cs) 2 heven
  have htG : orderOf (t : G) = 2 := (Subgroup.orderOf_coe t).trans ht
  have hts : Commute (t : G) s :=
    Subgroup.mem_centralizer_singleton_iff.mp t.property
  obtain ⟨g, hg⟩ := isConj_involution_J S P (t : G) htG
  let sJ : G := g * s * g⁻¹
  let JG : G := ((J P : S) : G)
  have hJ : (g : G) * (t : G) * (g : G)⁻¹ = JG := by
    calc
      (g : G) * (t : G) * (g : G)⁻¹ = ((g : G) * (t : G)) * (g : G)⁻¹ := rfl
      _ = (JG * (g : G)) * (g : G)⁻¹ := by rw [hg]
      _ = JG := by simp [mul_assoc]
  have hsJ : orderOf sJ = 5 := by
    simpa [sJ, MulAut.conj_apply] using ((MulAut.conj (g : G)).orderOf_eq s).trans hs
  have hsJcomm : Commute sJ JG := by
    have hh := hts.map (MulAut.conj (g : G))
    change Commute ((g : G) * (t : G) * (g : G)⁻¹) ((g : G) * s * (g : G)⁻¹) at hh
    rw [hJ] at hh
    simpa [sJ] using hh.symm
  let C : Subgroup G := Subgroup.centralizer ({JG} : Set G)
  have hsJC : sJ ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hsJcomm
  let O : Subgroup C := pPrimeCore 2 C
  let q : C →* (C ⧸ O) := QuotientGroup.mk' O
  have hQcard : Nat.card (C ⧸ O) = 96 := by
    simpa only [C, JG] using centralizerJ_oddCore_projective S P x hx |>.1
  have hqorder : orderOf (q ⟨sJ, hsJC⟩) = 1 := by
    have hdiv5 : orderOf (q ⟨sJ, hsJC⟩) ∣ 5 := by
      exact (orderOf_map_dvd q ⟨sJ, hsJC⟩).trans (by simp [hsJ])
    have hdiv96 : orderOf (q ⟨sJ, hsJC⟩) ∣ 96 := by
      rw [← hQcard]
      exact orderOf_dvd_natCard (q ⟨sJ, hsJC⟩)
    have hgcd : orderOf (q ⟨sJ, hsJC⟩) ∣ Nat.gcd 5 96 := Nat.dvd_gcd hdiv5 (hQcard ▸ hdiv96)
    norm_num at hgcd ⊢
    exact hgcd
  have hsJO : (⟨sJ, hsJC⟩ : C) ∈ O := by
    exact (QuotientGroup.eq_one_iff (N := O) ⟨sJ, hsJC⟩).mp (orderOf_eq_one_iff.mp hqorder)
  let sO : O := ⟨⟨sJ, hsJC⟩, hsJO⟩
  have hsO : orderOf sO = 5 := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    exact hsJ
  have hOodd : Odd (Nat.card O) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := C))
  let TC : Sylow 2 C := S.subtype (by
    dsimp [C, JG]
    exact sylow_le_centralizerJ S P)
  have hTCnormal : (TC : Subgroup C) ≤ Subgroup.normalizer (O : Set C) := by
    exact Subgroup.le_normalizer_of_normal
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let action : TC →* MulAut O :=
    O.normalizerMonoidHom.comp (Subgroup.inclusion hTCnormal)
  let : MulDistribMulAction TC O := MulDistribMulAction.compHom O action
  have hbotI : IsInvariant TC O (⊥ : Subgroup O) := by
    refine ⟨fun a z => ?_⟩
    simp only [Subgroup.mem_bot]
    constructor
    · rintro rfl
      exact smul_one a
    · intro hz
      have hh := congrArg (fun w : O => a⁻¹ • w) hz
      simpa only [inv_smul_smul, smul_one] using hh
  obtain ⟨R5, _, hR5I⟩ := exists_invariant_sylow_le_of_isPGroup
    (p := 5) TC.isPGroup' hOodd (⊥ : Subgroup O) IsPGroup.of_bot hbotI
  have h5div : 5 ∣ Nat.card O := by
    have := orderOf_dvd_natCard sO
    simpa only [hsO] using this
  have hOdiv : Nat.card O ∣ Nat.card G :=
    (O.card_subgroup_dvd_card.trans C.card_subgroup_dvd_card).trans (hG ▸ dvd_rfl)
  have h5sq : ¬ 5 ^ 2 ∣ Nat.card O := by
    intro h
    apply (show ¬ 5 ^ 2 ∣ Nat.card G by rw [hG]; norm_num)
    exact h.trans hOdiv
  have hR5card : Nat.card R5 = 5 :=
    R5.card_eq_prime_of_dvd_of_not_sq_dvd h5div h5sq
  let N : Subgroup C := (R5 : Subgroup O).map O.subtype
  have hNnorm : (TC : Subgroup C) ≤ Subgroup.normalizer (N : Set C) := by
    have hforward (a : TC) {z : C} (hz : z ∈ N) :
        (a : C) * z * (a : C)⁻¹ ∈ N := by
      obtain ⟨zO, hzO, rfl⟩ := hz
      exact ⟨a • zO, (hR5I.invariant a zO).mp hzO, rfl⟩
    intro a ha
    apply Subgroup.mem_normalizer_iff.mpr
    intro z
    constructor
    · exact hforward ⟨a, ha⟩
    · intro hz
      have hh := hforward (⟨a, ha⟩ : TC)⁻¹ hz
      have hcoe : ((↑((⟨a, ha⟩ : TC)⁻¹) : C)) = (a : C)⁻¹ := by rfl
      have hcoe' : ((↑((⟨a, ha⟩ : TC)⁻¹) : C))⁻¹ = (a : C) := by rw [hcoe]; simp
      rw [hcoe] at hh
      have hh' : ((a : C)⁻¹ * ((a : C) * z * (a : C)⁻¹) * (a : C)) ∈ N := by
        simpa only [inv_inv] using hh
      simpa [mul_assoc] using hh'
  let H : Subgroup C := Subgroup.normalizer (N : Set C)
  have hNHle : N ≤ H := by
    change N ≤ Subgroup.normalizer (N : Set C)
    exact Subgroup.le_normalizer
  let NH : Subgroup H := N.subgroupOf H
  let : NH.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer (H := N) (K := H) (by
    change N ≤ Subgroup.normalizer (N : Set C)
    exact Subgroup.le_normalizer)).mpr (by
      exact le_rfl)
  have hNcard : Nat.card N = 5 := by
    rw [Subgroup.card_map_of_injective O.subtype_injective]
    exact hR5card
  let : IsCyclic N := isCyclic_of_prime_card hNcard
  let : IsCyclic NH := (Subgroup.subgroupOfEquivOfLe hNHle).isCyclic.mpr inferInstance
  have hcentral : _root_.commutator H ≤ Subgroup.centralizer (NH : Set H) :=
    Subgroup.commutator_le_centralizer_of_isCyclic_normal NH
  have hqS : X P * F P ^ 2 ∈ _root_.commutator S := by
    rw [XF_sq_eq_r_inv]
    rw [P.derived_structure.1]
    exact (Subgroup.zpowers (P.r)).inv_mem (Subgroup.mem_zpowers _)
  let eTC : TC ≃* S := Subgroup.subgroupOfEquivOfLe (by
    dsimp [TC, C, JG]
    exact sylow_le_centralizerJ S P)
  have hqTC : eTC.symm (X P * F P ^ 2) ∈ _root_.commutator TC := by
    apply commutator_mem_of_map_eq eTC.symm.toMonoidHom eTC.symm.surjective
    simpa only [eTC.symm_apply_apply] using hqS
  let fTH : TC →* H :=
    { toFun := fun a => ⟨a, hNnorm a.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hqH : fTH (eTC.symm (X P * F P ^ 2)) ∈ _root_.commutator H := by
    have hmap : Subgroup.map fTH (_root_.commutator TC) ≤ _root_.commutator H := by
      rw [map_commutator_eq]
      exact Subgroup.commutator_mono (by exact le_top) (by exact le_top)
    exact hmap (Subgroup.mem_map_of_mem fTH hqTC)
  obtain ⟨yO, hyO⟩ := R5.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using hsO)
  obtain ⟨u, hu⟩ := isConj_iff.mp hyO
  have hyOorder : orderOf (yO : O) = 5 := by
    rw [← hu]
    exact ((MulAut.conj u).orderOf_eq sO).trans hsO
  let yN : N := ⟨(yO : O), Subgroup.mem_map_of_mem O.subtype yO.property⟩
  let yH : H := ⟨(yN : C), hNHle yN.property⟩
  have hyHNH : yH ∈ (NH : Set H) := by
    change (yH : C) ∈ N
    exact yN.property
  have hcommy : Commute (fTH (eTC.symm (X P * F P ^ 2))) yH := by
    exact (Subgroup.mem_centralizer_iff.mp (hcentral hqH) yH hyHNH).symm
  let qH : H := fTH (eTC.symm (X P * F P ^ 2))
  have hqHorder : orderOf (qH : G) = 4 := by
    change orderOf ((X P * F P ^ 2 : S) : G) = 4
    rw [Subgroup.orderOf_coe]
    exact XF_sq_orderOf P
  have hyHorder : orderOf (yH : G) = 5 := by
    change orderOf (yO : G) = 5
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hyOorder
  have hcommG : Commute (qH : G) (yH : G) := by
    exact (hcommy.map H.subtype).map C.subtype
  let y : G := (qH : G) * (yH : G)
  have hyorder : orderOf y = 20 := by
    dsimp [y]
    rw [hcommG.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hqHorder, hyHorder]; decide), hqHorder,
      hyHorder]
  exact ⟨y, hyorder⟩

end Stellmacher.Recognition.FongWreathed
