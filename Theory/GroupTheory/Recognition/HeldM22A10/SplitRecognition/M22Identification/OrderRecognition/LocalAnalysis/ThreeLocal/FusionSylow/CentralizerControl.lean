module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ThreeLocal.FusionSylow.CentralizerControl.QuotientRecognition
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ThreeLocal.FusionSylow.CentralizerTwoStructure
public import Theory.GroupTheory.SelfCentralizingCentralQuotient

/-!
# Centralizer control for a Case II subgroup of order nine

Let `H = C_G(c)`. The preceding local calculations give a center of order
three and conjugate involutions whose centralizers are abelian of order twelve.
The central quotient is A₄ or A₅ by the proved small Brauer–Suzuki–Wall case.
Thus `|H|` is 36 or 180. An elementary subgroup of order nine containing `c`
contains `Z(H)`; its quotient image has order three and is self-centralizing
in either alternating group. Lifting this containment proves `C_G(P) = P`.

No ambient Sylow assertion is used. The final theorem retains the normalizer
and fusion premises supplied by the construction of `P`, while the stronger
preceding theorem shows that they are unnecessary for this centralizer step.
This proves precisely the two consequences requested from Janko's Lemma 8;
it does not assert the full Suzuki normalizer dichotomy.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 3, pp.7–8, Lemma 8.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
open CentralizerControl

local instance (n : ℕ) : Fintype (Equiv.Perm (Fin n)) := fintypePerm
local instance (n : ℕ) : Fintype (alternatingGroup (Fin n)) :=
  @Subtype.fintype _ _ Equiv.Perm.sign.decidableMemKer inferInstance
local instance (n : ℕ) : DecidableEq (Equiv.Perm (Fin n)) := fun x y =>
  decidable_of_iff (∀ i, x i = y i) Equiv.ext_iff.symm
local instance (n : ℕ) : DecidableEq (alternatingGroup (Fin n)) := fun x y =>
  decidable_of_iff ((x : Equiv.Perm (Fin n)) = y) Subtype.ext_iff.symm

private theorem a4_three_commute :
    ∀ x y : alternatingGroup (Fin 4), x ≠ 1 → x ^ 3 = 1 →
      x * y = y * x → y = 1 ∨ y = x ∨ y = x ^ 2 := by decide +kernel

private theorem a5_three_commute :
    ∀ x y : alternatingGroup (Fin 5), x ≠ 1 → x ^ 3 = 1 →
      x * y = y * x → y = 1 ∨ y = x ∨ y = x ^ 2 := by decide +kernel

private theorem small_alternating_three_commute {A : Type*} [Group A]
    (he : Nonempty (A ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (A ≃* alternatingGroup (Fin 5)))
    (x : A) (hx : x ≠ 1) (hx3 : x ^ 3 = 1) (y : A) (hy : x * y = y * x) :
    y = 1 ∨ y = x ∨ y = x ^ 2 := by
  rcases he with he | he <;> obtain ⟨e⟩ := he
  all_goals
    have hex : e x ≠ 1 := fun h => hx (e.injective (h.trans (map_one e).symm))
    have hep : e x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
    have hec : e x * e y = e y * e x := by simpa only [← map_mul] using congrArg e hy
  · rcases a4_three_commute (e x) (e y) hex hep hec with h | h | h
    · exact Or.inl (e.injective (by simpa only [map_one] using h))
    · exact Or.inr (Or.inl (e.injective h))
    · exact Or.inr (Or.inr (e.injective (by simpa only [map_pow] using h)))
  · rcases a5_three_commute (e x) (e y) hex hep hec with h | h | h
    · exact Or.inl (e.injective (by simpa only [map_one] using h))
    · exact Or.inr (Or.inl (e.injective h))
    · exact Or.inr (Or.inr (e.injective (by simpa only [map_pow] using h)))

private theorem small_alternating_three_self_centralizing {A : Type*} [Group A] [Finite A]
    (he : Nonempty (A ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (A ≃* alternatingGroup (Fin 5)))
    (R : Subgroup A) (hR : Nat.card R = 3) : centralizer (R : Set A) ≤ R := by
  have : Nontrivial R := Finite.one_lt_card_iff_nontrivial.mp (by rw [hR]; decide)
  obtain ⟨x, hx⟩ := exists_ne (1 : R)
  have hx3 : (x : A) ^ 3 = 1 := by
    have hh := pow_card_eq_one' (x := x)
    rw [hR] at hh
    exact congrArg Subtype.val hh
  intro y hy
  rcases small_alternating_three_commute he (x : A)
    (fun h => hx (Subtype.ext h)) hx3 y (hy x x.property) with h | h | h
  · exact h ▸ R.one_mem
  · exact h ▸ x.property
  · exact h ▸ R.pow_mem x.property 2

universe u

/-- An elementary nine containing the marked element of order three is
self-centralizing, and the marked centralizer has three-part at most nine. -/
public theorem three_centralizer_control_of_nine {G : Type u} [Group G] [Finite G]
    (D : LocalData G) (k : TwistedModel ≃* D.centralizer)
    (h2 : ∀ t : G, orderOf t = 2 → IsConj t D.z) (P : Subgroup G)
    (hP : IsElementaryAbelian 3 P) (hPcard : Nat.card P = 9)
    (hcP : CaseII.into D k CaseII.c ∈ P) :
    centralizer (P : Set G) = P ∧
      ¬27 ∣ Nat.card (centralizer ({CaseII.into D k CaseII.c} : Set G)) := by
  let H := centralizer ({CaseII.into D k CaseII.c} : Set G)
  let cH : H := ⟨CaseII.into D k CaseII.c, mem_centralizer_singleton_iff.mpr rfl⟩
  let t := CaseII.markedInvolutionInThreeCentralizer D k
  have ht : orderOf t = 2 := by
    change orderOf (CaseII.markedInvolutionInThreeCentralizer D k) = 2
    rw [orderOf_mk]
    exact D.z_order
  have hZ : Nat.card (center H) = 3 := CaseII.three_centralizer_center_card D k h2
  have he : Nonempty ((H ⧸ center H) ≃* alternatingGroup (Fin 4)) ∨
      Nonempty ((H ⧸ center H) ≃* alternatingGroup (Fin 5)) := by
    apply alternating_four_or_five_of_center_three hZ t ht
      (CaseII.marked_three_involution_centralizer_card D k)
    · intro x
      apply Subtype.ext
      exact CaseII.three_centralizer_pow_six_of_commuting_involution D k
        h2 x t ht (mem_centralizer_singleton_iff.mp x.property)
    · exact CaseII.three_centralizer_involution_fusion D k h2
  have hHcard : Nat.card H = 36 ∨ Nat.card H = 180 := by
    have hh := (center H).card_eq_card_quotient_mul_card_subgroup
    rw [hZ] at hh
    rcases he with he | he <;> obtain ⟨e⟩ := he
    · left
      rw [Nat.card_congr e.toEquiv] at hh
      norm_num [nat_card_alternatingGroup, Nat.card_fin] at hh
      exact hh
    · right
      rw [Nat.card_congr e.toEquiv] at hh
      norm_num [nat_card_alternatingGroup, Nat.card_fin] at hh
      exact hh
  have hPcomm (x y : G) (hx : x ∈ P) (hy : y ∈ P) : x * y = y * x :=
    congrArg Subtype.val (hP.is_comm.comm (⟨x, hx⟩ : P) ⟨y, hy⟩)
  have hPH : P ≤ H := fun x hx => mem_centralizer_singleton_iff.mpr (hPcomm x _ hx hcP)
  let R := P.subgroupOf H
  have hRcard : Nat.card R = 9 :=
    (Nat.card_congr (subgroupOfEquivOfLe hPH).toEquiv).trans hPcard
  have hcZ : cH ∈ center H := mem_center_iff.mpr (fun x =>
    Subtype.ext (mem_centralizer_singleton_iff.mp x.property))
  have hco : orderOf cH = 3 := by
    rw [orderOf_mk, orderOf_injective (CaseII.into D k) (CaseII.into_injective D k)]
    exact CaseII.actor_orders.2.2.1
  have hZeq : center H = zpowers cH := by
    apply (eq_of_le_of_card_ge (zpowers_le.mpr hcZ) ?_).symm
    rw [Nat.card_zpowers, hco, hZ]
  have hZR : center H ≤ R := by
    rw [hZeq]
    exact zpowers_le.mpr hcP
  let q := QuotientGroup.mk' (center H)
  have hRqcard : Nat.card (R.map q) = 3 := by
    have hh := card_map_mul_kernel q R (by change (QuotientGroup.mk' (center H)).ker ≤ R; simpa only [QuotientGroup.ker_mk'] using hZR)
    rw [QuotientGroup.ker_mk', hZ, hRcard] at hh
    omega
  have hself : centralizer (R : Set H) ≤ R :=
    le_of_centralizer_quotient_le (center H) R (centralizer (R : Set H)) hZR le_rfl
      (small_alternating_three_self_centralizing he (R.map q) hRqcard)
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · intro x hx
    have hxH : x ∈ H := mem_centralizer_singleton_iff.mpr (hx _ hcP).symm
    exact hself (show (⟨x, hxH⟩ : H) ∈ centralizer (R : Set H) from
      fun y hy => Subtype.ext (hx y hy))
  · intro x hx y hy
    exact hPcomm y x hy hx
  · change ¬27 ∣ Nat.card H
    rcases hHcard with h | h <;> rw [h] <;> norm_num

/-- The centralizer control consumed by the fused-nine Sylow argument in
Janko's Lemma 8, with the construction's original explicit premises. -/
public theorem three_centralizer_control_of_fused_nine
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (D : LocalData G) (k : TwistedModel ≃* D.centralizer)
    (h2 : InvolutionNormalizerData D k) (P : Subgroup G)
    (_hPN : P ≤ normalizer (CaseII.E D k : Set G))
    (hP : IsElementaryAbelian 3 P) (hPcard : Nat.card P = 9)
    (hcP : CaseII.into D k CaseII.c ∈ P)
    (_hf : ∀ x ∈ P, orderOf x = 3 → IsConj x (CaseII.into D k CaseII.c)) :
    centralizer (P : Set G) = P ∧
      ¬27 ∣ Nat.card (centralizer ({CaseII.into D k CaseII.c} : Set G)) :=
  three_centralizer_control_of_nine D k h2.involution_fusion P hP hPcard hcP

end Theory.GroupTheory.HeldM22A10.M22Identification
