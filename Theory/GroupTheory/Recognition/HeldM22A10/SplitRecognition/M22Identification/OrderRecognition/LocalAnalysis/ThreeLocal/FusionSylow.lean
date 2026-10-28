module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.Contracts
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ThreeLocal.FusionSylow.CentralizerControl
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ThreeLocal.FusionSylow.CentralizerTwoStructure
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ThreeLocal.FusionSylow.FusedNine
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Mathlib.GroupTheory.IndexNormal

/-!
# Order-three fusion and elementary Sylow subgroups

An elementary subgroup of order nine is Sylow if its elements of order three
are fused and their centralizer order is not divisible by 27. Otherwise it
lies normally in a subgroup of order 27; that overgroup centralizes a nontrivial
element of the original subgroup, contradicting the centralizer bound.
Sylow conjugacy then transports fusion, elementary structure and centralizers.

The final theorem constructs the fused subgroup from the E and F normalizers.
The local centralizer calculation supplies its self-centralization and the
centralizer bound, discharging every premise of the reduction. Thus the explicit
involution-normalizer data imply the fusion, elementary-nine Sylow structure
and self-centralization clauses of Janko's Lemma 8.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 3, pp.7–8.
-/

open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.HeldM22A10.M22Identification

private theorem centralizer_card_eq_of_isConj {G : Type*} [Group G] {x y : G}
    (h : IsConj x y) : Nat.card (centralizer ({x} : Set G)) =
      Nat.card (centralizer ({y} : Set G)) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  let e := MulAut.conj g
  have he : e x = y := hg
  apply Nat.card_congr (Equiv.subtypeEquiv e.toEquiv ?_)
  intro t
  change t ∈ centralizer ({x} : Set G) ↔ e t ∈ centralizer ({y} : Set G)
  simp only [mem_centralizer_singleton_iff, ← he, ← map_mul, e.injective.eq_iff]

private theorem not_twenty_seven_dvd_of_fused_nine
    {G : Type*} [Group G] [Finite G] (c : G) (P : Subgroup G)
    [IsElementaryAbelian 3 P] (hP : Nat.card P = 9)
    (hf : ∀ x ∈ P, orderOf x = 3 → IsConj x c)
    (hb : ¬27 ∣ Nat.card (centralizer ({c} : Set G))) : ¬27 ∣ Nat.card G := by
  intro h27
  obtain ⟨R, hR, hPR⟩ := Sylow.exists_subgroup_card_pow_succ (p := 3) (n := 2)
    (by simpa using h27) (H := P) (by simpa using hP)
  have hR' : Nat.card R = 27 := hR
  let A := P.subgroupOf R
  have hA : Nat.card A = 9 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hPR).toEquiv]
    exact hP
  have hi : A.index = 3 := by
    have hh := A.index_mul_card
    rw [hA, hR'] at hh
    omega
  let : A.Normal := normal_of_index_eq_minFac_card (by
    rw [hi, hR]
    exact (Nat.prime_three.pow_minFac (by decide : 2 + 1 ≠ 0)).symm)
  let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by rw [hA]; decide)
  let : Fact (IsPGroup 3 R) := ⟨IsPGroup.of_card hR⟩
  obtain ⟨x, hx, hxc⟩ := exists_nontrivial_center_mem_normal (p := 3) A
  have hxP : ((x : R) : G) ∈ P := x.property
  have hxne : ((x : R) : G) ≠ 1 := fun h => hx (Subtype.ext (Subtype.ext h))
  have hxo : orderOf ((x : R) : G) = 3 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian _ hxP) hxne
  have hRC : R ≤ centralizer ({((x : R) : G)} : Set G) := by
    intro y hy
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp hxc ⟨y, hy⟩))
  have hd := card_dvd_of_le hRC
  rw [hR', centralizer_card_eq_of_isConj (hf _ hxP hxo)] at hd
  exact hb hd

private theorem centralizer_map_eq_self {G : Type*} [Group G]
    (P : Subgroup G) (e : G ≃* G) (hP : centralizer (P : Set G) = P) :
    centralizer (P.map e.toMonoidHom : Set G) = P.map e.toMonoidHom := by
  apply le_antisymm
  · intro x hx
    apply mem_map.mpr
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    rw [← hP]
    intro y hy
    apply e.injective
    simp only [map_mul, e.apply_symm_apply]
    exact hx (e y) (mem_map_of_mem e.toMonoidHom hy)
  · simpa only [hP, coe_map] using
      map_centralizer_le_centralizer_image (P : Set G) e.toMonoidHom

/-- A fused elementary nine is Sylow once its centralizer is itself and the
centralizer of its fusion representative has three-part at most nine. -/
public theorem three_fusion_and_sylow_of_fused_nine
    {G : Type*} [Group G] [Finite G] (c : G) (P : Subgroup G)
    [IsElementaryAbelian 3 P] (hP : Nat.card P = 9)
    (hf : ∀ x ∈ P, orderOf x = 3 → IsConj x c)
    (hC : centralizer (P : Set G) = P)
    (hb : ¬27 ∣ Nat.card (centralizer ({c} : Set G))) :
    (∀ x : G, orderOf x = 3 → IsConj x c) ∧
      ∀ S : Sylow 3 G, IsElementaryAbelian 3 S ∧ Nat.card S = 9 ∧
        centralizer (S : Set G) = S := by
  have h27 := not_twenty_seven_dvd_of_fused_nine c P hP hf hb
  have hi : ¬3 ∣ P.index := by
    intro hh
    apply h27
    have hd := Nat.mul_dvd_mul_right hh 9
    rw [← hP, P.index_mul_card] at hd
    simpa only [hP] using hd
  let T : Sylow 3 G := (IsElementaryAbelian.isPGroup 3 P).toSylow hi
  have hT : (T : Subgroup G) = P := rfl
  refine ⟨?_, ?_⟩
  · intro x hx
    have hxp : IsPGroup 3 (zpowers x) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, hx, pow_one])
    obtain ⟨S, hS⟩ := hxp.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
    have hm : (MulAut.conj g) x ∈ P := by
      rw [← hT, ← hg, Sylow.smul_def, Sylow.pointwise_smul_def]
      exact smul_mem_pointwise_smul x (MulAut.conj g) (S : Subgroup G) (hS (mem_zpowers x))
    have ho : orderOf ((MulAut.conj g) x) = 3 := (MulAut.conj g).orderOf_eq x |>.trans hx
    exact (isConj_iff.mpr ⟨g, rfl⟩).trans (hf _ hm ho)
  · intro S
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
    have he : (S : Subgroup G) = P.map (MulAut.conj g).toMonoidHom := by
      rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def, hT,
        Subgroup.pointwise_smul_def]
      rfl
    change IsElementaryAbelian 3 (S : Subgroup G) ∧
      Nat.card (S : Subgroup G) = 9 ∧ centralizer ((S : Subgroup G) : Set G) = S
    rw [he]
    refine ⟨IsElementaryAbelian.map _, ?_, centralizer_map_eq_self P (MulAut.conj g) hC⟩
    rw [card_map_of_injective (MulAut.conj g).injective]
    exact hP

/-- The involution normalizers imply that all elements of order three are
conjugate and every Sylow three-subgroup is elementary of order nine and
self-centralizing. These are the corresponding clauses of Janko's Lemma 8. -/
public theorem three_fusion_and_sylow_of_involution_normalizers
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (D : LocalData G) (k : LocalModelDichotomy.TwistedModel ≃* D.centralizer)
    (h2 : InvolutionNormalizerData D k) :
    (∀ x : G, orderOf x = 3 → IsConj x (CaseII.into D k CaseII.c)) ∧
      ∀ P : Sylow 3 G, IsElementaryAbelian 3 P ∧ Nat.card P = 9 ∧
        centralizer (P : Set G) = P := by
  obtain ⟨P, hPN, hP, hPcard, hcP, hf⟩ :=
    exists_fused_elementary_nine_of_involution_normalizers D k h2
  obtain ⟨hC, hb⟩ :=
    three_centralizer_control_of_fused_nine D k h2 P hPN hP hPcard hcP hf
  let : IsElementaryAbelian 3 P := hP
  exact three_fusion_and_sylow_of_fused_nine (CaseII.into D k CaseII.c) P hPcard hf hC hb

end Theory.GroupTheory.HeldM22A10.M22Identification
