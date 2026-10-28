module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/BinaryIndex.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG import paths and Lean 4.33 public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.G2.Primitivity
public import Theory.AtlasPort.LinearGroups.G2.IwasawaCriterion
public import Theory.AtlasPort.OtherSporadic.GroupTheory.PrimitiveNormal
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Index

/-!
Modulo the long-root normal closure, the root relations reduce the point
stabilizer to one involution. Primitivity makes the closure transitive, so the
whole quotient has at most two elements.
-/

@[expose] public section

namespace Atlas.G2.BinaryException
open Atlas.SplitOctonion Atlas.G2.Explicit
abbrev K := ZMod 2
abbrev H : Subgroup (Model K) := longRootNormalClosure
abbrev Q := Model K ⧸ H
abbrev projection : Model K →* Q := QuotientGroup.mk' H

 theorem rootA_in_H (a:K) : rootA a ∈ H :=
  Subgroup.subset_normalClosure (rootA_mem_longRootLocal a)
 theorem rootB_in_H (a:K) : rootB a ∈ H :=
  Subgroup.subset_normalClosure (rootB_mem_longRootLocal a)
 theorem rootE_in_H (a:K) : rootE a ∈ H := by
  rw [← weylS_rootB]
  exact (inferInstance : H.Normal).conj_mem _ (rootB_in_H a) _

 theorem project_A (a:K) : projection (rootA a)=1 :=
  (QuotientGroup.eq_one_iff _).mpr (rootA_in_H a)
 theorem project_B (a:K) : projection (rootB a)=1 :=
  (QuotientGroup.eq_one_iff _).mpr (rootB_in_H a)
 theorem project_E (a:K) : projection (rootE a)=1 :=
  (QuotientGroup.eq_one_iff _).mpr (rootE_in_H a)

 theorem binary_unit_eq_one (a:Kˣ) : a=1 := by
  have h : ∀a:ZMod 2,a=0∨a=1 := by decide
  apply Units.ext
  rcases h a with h|h
  · exact (a.ne_zero h).elim
  · exact h

 theorem binary_torus (a b:Kˣ) : torus a b=1 := by
  rw [binary_unit_eq_one a,binary_unit_eq_one b,torus_identity]

 theorem weylR_in_H : (weylR:Model K) ∈ H := by
  have h := long_rank_one_word (1:Kˣ)
  rw [binary_torus,one_mul] at h
  rw [← h]
  exact H.mul_mem (H.mul_mem (rootE_in_H _) ((inferInstance:H.Normal).conj_mem _
    (rootE_in_H _) _)) (rootE_in_H _)

 theorem project_R : projection weylR=1 := (QuotientGroup.eq_one_iff _).mpr weylR_in_H

 theorem project_C_eq_D (a:K) : projection (rootC a)=projection (rootD a) := by
  have hc : rootF 1 * rootE a * rootF (-1) ∈ H := by
    rw [rootF_neg]
    exact (inferInstance : H.Normal).conj_mem _ (rootE_in_H a) _
  have hq : projection (rootF 1 * rootE a * rootF (-1))=1 :=
    (QuotientGroup.eq_one_iff _).mpr hc
  rw [rootF_conjugate_rootE] at hq
  simp only [one_pow,mul_one,map_mul,project_A,project_B,project_E,one_mul,mul_one,
    rootD_neg,map_inv] at hq
  exact mul_inv_eq_one.mp hq

 theorem project_D_eq_F (a:K) : projection (rootD a)=projection (rootF a) := by
  have h := congrArg projection (weylR_rootD a)
  simpa only [map_mul,map_inv,project_R,one_mul,inv_one,mul_one] using h

 theorem F_sq : (rootF (1:K))^2=1 := by
  rw [pow_two,rootF_add,show (1:K)+1=0 by decide,rootF_zero]

 def quotientBit : Q := projection (rootF 1)
 theorem quotientBit_sq : quotientBit^2=1 := by
  rw [quotientBit,← map_pow,F_sq,map_one]

 def bitSubgroup : Subgroup Q where
  carrier := {x | x=1 ∨ x=quotientBit}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro a b (rfl|rfl) (rfl|rfl) <;> simp [show quotientBit*quotientBit=1 by
      simpa [pow_two] using quotientBit_sq]
  inv_mem' := by
    rintro a (rfl|rfl)
    · exact Or.inl inv_one
    · exact Or.inr (inv_eq_of_mul_eq_one_left (by simpa [pow_two] using quotientBit_sq))

 theorem project_rootF_mem (a:K) : projection (rootF a) ∈ bitSubgroup := by
  have h : ∀a:ZMod 2,a=0∨a=1 := by decide
  rcases h a with rfl|rfl
  · exact Or.inl (by rw [rootF_zero,map_one])
  · exact Or.inr rfl

 theorem unipotent_le_bitComap : unipotent (K := K) ≤ bitSubgroup.comap projection := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with (((((hg|hg)|hg)|hg)|hg)|hg)
  all_goals obtain ⟨a,rfl⟩ := hg
  · exact Or.inl (project_A a)
  · exact Or.inl (project_B a)
  · change projection (rootC a) ∈ bitSubgroup
    rw [project_C_eq_D,project_D_eq_F]
    exact project_rootF_mem a
  · change projection (rootD a) ∈ bitSubgroup
    rw [project_D_eq_F]
    exact project_rootF_mem a
  · exact Or.inl (project_E a)
  · exact project_rootF_mem a

 theorem pointStabilizer_le_bitComap :
    pointStabilizer (K := K) ≤ bitSubgroup.comap projection := by
  rw [← parabolic_eq_pointStabilizer]
  apply sup_le
  · apply sup_le unipotent_le_bitComap
    rintro g ⟨⟨a,b⟩,rfl⟩
    change projection (torus a b) ∈ bitSubgroup
    rw [binary_torus,map_one]
    exact bitSubgroup.one_mem
  · apply (Subgroup.closure_le _).mpr
    rintro g (rfl : g=weylR)
    exact Or.inl project_R

 theorem H_ne_bot : H ≠ ⊥ := by
  intro h
  have ha := rootA_in_H 1
  rw [h,Subgroup.mem_bot] at ha
  have h01 := rootA_injective (ha.trans (rootA_zero (K := K)).symm)
  exact one_ne_zero h01

 theorem quotient_eq_one_or_bit
    [MulAction.IsPreprimitive (Model K) (SingularPoints K)] (g : Model K) :
    projection g=1 ∨ projection g=quotientBit := by
  let := Atlas.GroupTheory.normal_pretransitive (X := SingularPoints K) H H_ne_bot
  obtain ⟨n,hn⟩ := MulAction.exists_smul_eq H (firstPoint (K := K)) (g • firstPoint)
  have hp : n.val⁻¹*g ∈ pointStabilizer := by
    change (n.val⁻¹*g) • firstPoint=firstPoint
    rw [SemigroupAction.mul_smul,← hn]
    exact inv_smul_smul n.val firstPoint
  have hb := pointStabilizer_le_bitComap hp
  change projection (n.val⁻¹*g) ∈ bitSubgroup at hb
  have hnq : projection n.val=1 := (QuotientGroup.eq_one_iff _).mpr n.prop
  have hb' : projection g ∈ bitSubgroup := by
    simpa only [map_mul,map_inv,hnq,inv_one,one_mul] using hb
  exact hb'

 theorem quotient_card_le_two
    [MulAction.IsPreprimitive (Model K) (SingularPoints K)] : Nat.card Q ≤ 2 := by
  let f : Bool → Q := fun b => if b then quotientBit else 1
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective H x
    rcases quotient_eq_one_or_bit g with h|h
    · exact ⟨false,h.symm⟩
    · exact ⟨true,h.symm⟩
  simpa using Nat.card_le_card_of_surjective f hf

theorem index_le_two : H.index ≤ 2 := by
  let := singularPoints_primitive (K := K)
  rw [Subgroup.index_eq_card]
  exact quotient_card_le_two

end Atlas.G2.BinaryException

