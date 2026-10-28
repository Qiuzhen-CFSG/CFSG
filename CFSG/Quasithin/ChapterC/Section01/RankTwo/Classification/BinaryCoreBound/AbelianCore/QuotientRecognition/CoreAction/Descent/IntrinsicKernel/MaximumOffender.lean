module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.CoreAction.Descent.ComponentImage
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Maximum elementary subgroups give best offenders on the entire MS core

Write D=[O₂(J),L] and let E have maximum order among the elementary
abelian subgroups of R. For every subgroup B of the actual action image of E,
lift B back to F≤E and compare the elementary subgroup C_D(F)F with E.
The product-order formula and cancellation of the common action kernel give
|B||C_D(B)| ≤ |image(E)||C_D(E)|. Thus the original image of E is itself a
best offender; no replacement that could lose its nontrivial quotient image
is necessary.

This strengthens the counting input for the remaining central-kernel
exclusion. It does not identify the ambient action group with SL₃(2), nor
assert that the component action is centerless.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.1.3 and
B.2.4–5, printed pp.68 and 75–76, applied to C.1.31–34, printed pp.135–137.
-/

public section

open Subgroup
open scoped IsMulCommutative
open Representation.BinaryOffender

namespace CFSG.Quasithin.ChapterC.BinaryMS
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
variable (h : Input κ L R) [IsElementaryAbelian 2 (commutatorCore L)]

private theorem elementary_subgroup_of_le {G : Type*} [Group G]
    {A B : Subgroup G} [IsElementaryAbelian 2 A] (hBA : B ≤ A) :
    IsElementaryAbelian 2 B := by
  refine {
    toIsMulCommutative := ⟨⟨fun x y => Subtype.ext
      (congrArg (fun a : A => (a : G)) ((IsMulCommutative.is_comm (M := A)).comm
        (⟨x, hBA x.property⟩ : A) ⟨y, hBA y.property⟩))⟩⟩
    exponent_dvd_p := ?_ }
  rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
  intro x
  exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2)
    (A := A) (x : G) (hBA x.property))

private theorem card_inter_kernel {G H : Type*} [Group G] [Group H]
    (F : Subgroup G) (q : G →* H) :
    Nat.card (F ⊓ q.ker : Subgroup G) * Nat.card (F.map q) = Nat.card F := by
  have ht := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (q.ker ⊓ F) F
    bot_le inf_le_right
  simp only [Subgroup.relIndex_bot_left, Subgroup.inf_relIndex_right,
    Subgroup.relIndex_ker] at ht
  simpa only [inf_comm] using ht

/-- The image of a maximum elementary subgroup maximizes the actual
multiplicative offender weight among all its subgroups. -/
theorem Input.coreAmbient_maxElementary_weight_card
    (E : Subgroup J) (hE : E ∈ Stellmacher.elementaryAbelianMaxSubgroups R)
    (B : Subgroup h.coreAmbientConjugation.range)
    (hB : B ≤ E.map h.coreAmbientConjugation.rangeRestrict) :
    Nat.card B * Nat.card (fixedSpace h.coreAmbientRepresentation B) ≤
      Nat.card (E.map h.coreAmbientConjugation.rangeRestrict) *
        Nat.card (fixedSpace h.coreAmbientRepresentation
          (E.map h.coreAmbientConjugation.rangeRestrict)) := by
  let q := h.coreAmbientConjugation.rangeRestrict
  let D := commutatorCore L
  let F := E ⊓ B.comap q
  let CE := D ⊓ centralizer (E : Set J)
  let CF := D ⊓ centralizer (F : Set J)
  let U := CF ⊔ F
  let K := E ⊓ q.ker
  let _ : IsElementaryAbelian 2 E := hE.2.1
  let _ : IsElementaryAbelian 2 F := elementary_subgroup_of_le (A := E) inf_le_left
  let _ : IsElementaryAbelian 2 CF := elementary_subgroup_of_le (A := D) inf_le_left
  have hCF : F ≤ centralizer (CF : Set J) := by
    intro f hf c hc
    exact (hc.2 f hf).symm
  have hU : IsElementaryAbelian 2 U :=
    IsElementaryAbelian.sup_of_le_centralizer hCF
  have hDR : D ≤ R := h.commutatorCore_le.trans
    (h.componentCore_eq_inf.le.trans (inf_le_left.trans h.radical.twoCore_le))
  have hUcard : Nat.card U ≤ Nat.card E :=
    hE.2.2 U (sup_le (inf_le_left.trans hDR) (inf_le_left.trans hE.1)) hU
  have hIF : CF ⊓ F ≤ CE := by
    intro x hx
    refine ⟨hx.1.1, ?_⟩
    exact (le_centralizer_iff_isMulCommutative.mpr
      (inferInstance : IsMulCommutative E)) hx.2.1
  have hIcard : Nat.card (CF ⊓ F : Subgroup J) ≤ Nat.card CE :=
    Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hIF)
  have hprod : Nat.card CF * Nat.card F ≤ Nat.card CE * Nat.card E := by
    rw [Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes CF F
      (hCF.trans (Subgroup.centralizer_le_normalizer _))]
    exact Nat.mul_le_mul hIcard hUcard
  have hFmap : F.map q = B := by
    apply le_antisymm
    · rintro x ⟨f, hf, rfl⟩
      exact hf.2
    · intro x hx
      obtain ⟨e, he, rfl⟩ := hB hx
      exact ⟨e, ⟨he, hx⟩, rfl⟩
  have hFK : F ⊓ q.ker = K := by
    apply le_antisymm
    · intro x hx
      exact ⟨hx.1.1, hx.2⟩
    · intro x hx
      exact ⟨⟨hx.1, by change q x ∈ B; rw [show q x = 1 from hx.2]; exact B.one_mem⟩, hx.2⟩
  have hFcard : Nat.card K * Nat.card B = Nat.card F := by
    have hh := card_inter_kernel F q
    rwa [hFK, hFmap] at hh
  have hEcard := card_inter_kernel E q
  have hcount : Nat.card B * Nat.card CF ≤
      Nat.card (E.map q) * Nat.card CE := by
    have hmul : Nat.card K * (Nat.card B * Nat.card CF) ≤
        Nat.card K * (Nat.card (E.map q) * Nat.card CE) := by
      calc
        _ = Nat.card CF * Nat.card F := by rw [← hFcard]; ac_rfl
        _ ≤ Nat.card CE * Nat.card E := hprod
        _ = _ := by rw [← hEcard]; ac_rfl
    exact Nat.le_of_mul_le_mul_left hmul Nat.card_pos
  have hfixed (A : Subgroup J) :
      Nat.card (fixedSpace h.coreAmbientRepresentation (A.map q)) =
        Nat.card (D ⊓ centralizer (A : Set J) : Subgroup J) := by
    apply Nat.card_congr
    exact {
      toFun := fun v => ⟨v.val.toMul, v.val.toMul.property,
        (h.mem_coreAmbientFixedSpace A v.val).mp v.property⟩
      invFun := fun v => ⟨Additive.ofMul ⟨v, v.property.1⟩,
        (h.mem_coreAmbientFixedSpace A _).mpr v.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← hFmap, hfixed F, hFmap, hfixed E]
  exact hcount

/-- A maximum elementary subgroup outside O₂(J) gives a best offender
on D for the faithful ambient action. -/
theorem Input.coreAmbient_maxElementary_isBestOffender
    (E : Subgroup J) (hE : E ∈ Stellmacher.elementaryAbelianMaxSubgroups R)
    (hEN : ¬ E ≤ pCore 2 J) :
    IsBestOffender h.coreAmbientRepresentation
      (E.map h.coreAmbientConjugation.rangeRestrict) := by
  let A := E.map h.coreAmbientConjugation.rangeRestrict
  have hA : IsElementaryTwo A := by
    refine ⟨?_, hE.2.1.map _⟩
    intro hbot
    have hk := (Subgroup.map_eq_bot_iff E).mp hbot
    rw [h.coreAmbientConjugation_rangeKernel] at hk
    exact hEN (hk.trans h.core_centralizer_le)
  refine ⟨hA, fun B hB => ?_⟩
  have hc := h.coreAmbient_maxElementary_weight_card E hE B hB
  have hcB : Nat.card B = 2 ^ rank B := by
    by_cases hb : B = ⊥
    · simp [hb]
    · exact (hA.of_le hB hb).card_eq_two_pow_rank
  have hfixed (C : Subgroup h.coreAmbientConjugation.range) :
      Nat.card (fixedSpace h.coreAmbientRepresentation C) =
        2 ^ Module.finrank (ZMod 2) (fixedSpace h.coreAmbientRepresentation C) := by
    simp only [Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := fixedSpace h.coreAmbientRepresentation C),
      Nat.card_eq_fintype_card, ZMod.card]
  rw [hcB, hA.card_eq_two_pow_rank, hfixed B, hfixed A, ← pow_add, ← pow_add] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc

/-- The genuine MS maximum-elementary witness retains the full best-offender
property on the entire elementary commutator core. -/
theorem Input.exists_coreAmbientBestOffender :
    ∃ E ∈ Stellmacher.elementaryAbelianMaxSubgroups R, ¬ E ≤ pCore 2 J ∧
      IsBestOffender h.coreAmbientRepresentation
        (E.map h.coreAmbientConjugation.rangeRestrict) := by
  obtain ⟨E, hE, hEN⟩ := h.exists_maxElementary_not_le_core
  exact ⟨E, hE, hEN, h.coreAmbient_maxElementary_isBestOffender E hE hEN⟩

end CFSG.Quasithin.ChapterC.BinaryMS
