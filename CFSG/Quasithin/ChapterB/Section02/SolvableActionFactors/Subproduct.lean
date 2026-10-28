module
public import CFSG.Quasithin.ChapterB.Section02.SolvableActionFactors.Rank
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.Internal
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.Choices
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The two possible nonempty Thompson subproducts

A nonempty selected family of at most two actual symmetric-three factors
is a single factor or their full internal product. The conclusion is an
isomorphism for the literal join, retaining the subgroup selected by the
reduced Thompson action.

Source: Aschbacher--Smith B.2.16(2), used in 13.7.4(1), printed p.937.
-/

public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SolvableFFFactors
local notation "S3" => Equiv.Perm (Fin 3)
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (d : SolvableFFFactors ρ)

theorem nonempty_subproduct_models (hc : d.count = 1 ∨ d.count = 2)
    (S : Set (Fin d.count)) (hS : S.Nonempty) :
    Nonempty ((⨆ i ∈ S, d.factor i : Subgroup G) ≃* S3) ∨
      Nonempty ((⨆ i ∈ S, d.factor i : Subgroup G) ≃* (S3 × S3)) := by
  classical
  let es := Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three
  let em (i : Fin d.count) := (d.factorModel i).trans es
  by_cases hall : S = Set.univ
  · have he : (⨆ i ∈ S, d.factor i : Subgroup G) = offenderSubgroup ρ := by
      rw [hall]
      simpa using d.iSup_factor
    let ep : (⨆ i ∈ S, d.factor i : Subgroup G) ≃* (Fin d.count → S3) :=
      (MulEquiv.subgroupCongr he).trans (d.groupProduct.symm.trans (MulEquiv.piCongrRight em))
    rcases hc with hc | hc
    · left
      have ep1 : Nonempty ((Fin d.count → S3) ≃* S3) := by
        rw [hc]
        exact ⟨MulEquiv.piUnique (fun _ : Fin 1 => S3)⟩
      exact ⟨ep.trans ep1.some⟩
    · right
      have ep2 : Nonempty ((Fin d.count → S3) ≃* (S3 × S3)) := by
        rw [hc]
        exact ⟨{ toEquiv := finTwoArrowEquiv _
                 map_mul' := fun _ _ => rfl }⟩
      exact ⟨ep.trans ep2.some⟩
  · left
    obtain ⟨i, hi⟩ := hS
    have hsingle : S = {i} := by
      apply Set.eq_singleton_iff_unique_mem.mpr
      refine ⟨hi, fun j hj => ?_⟩
      by_contra hji
      apply hall
      apply Set.eq_univ_of_forall
      intro k
      have hk : k = i ∨ k = j := by
        have hi' := i.isLt
        have hj' := j.isLt
        have hk' := k.isLt
        have hne : i.val ≠ j.val := fun he => hji (Fin.ext he.symm)
        have hc' : d.count ≤ 2 := by omega
        have he : k.val = i.val ∨ k.val = j.val := by omega
        exact he.imp Fin.ext Fin.ext
      rcases hk with rfl | rfl
      · exact hi
      · exact hj
    have he : (⨆ j ∈ S, d.factor j : Subgroup G) = d.factor i := by
      rw [hsingle]
      simp
    exact ⟨(MulEquiv.subgroupCongr he).trans (em i)⟩
end CFSG.Quasithin.ChapterB.SolvableFFFactors
