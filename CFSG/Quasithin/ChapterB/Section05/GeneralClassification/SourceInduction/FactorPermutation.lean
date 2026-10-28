module

public import Theory.GroupTheory.NormalProductCoordinate
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorModels
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Product

/-!
# Intrinsic permutation of the original B.5.6 direct factors

The two factor models have only 2-group proper normal quotients. A normal map
into the first factor is therefore injective or trivial, since its two-core
is trivial. Normality in a center-free product kills the opposite coordinate.
Surjectivity and finite order turn this into preservation or interchange of
the two literal factors under every automorphism.

The source application discharges all factor-model premises from the actual
SourceTwoFactorCase, retaining only the original trivial ambient two-core.
We also identify the actual centralizer of each factor and provide the
reindexed source data. Source: Aschbacher–Smith, B.5.6(3) and G.6.4.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction
variable {D : Type*} [Group D] [Finite D]
namespace InternalProduct
variable {A B : Subgroup D} (h : InternalProduct A B)
include h


omit [Finite D] in
private theorem product_commutes (a : A) (b : B) : (a : D) * (b : D) = (b : D) * (a : D) := by
  have hh : h.equiv ((a,1) * (1,b)) = h.equiv ((1,b) * (a,1)) := by simp
  rw [map_mul, map_mul] at hh
  simpa only [h.apply_eq, OneMemClass.coe_one, mul_one, one_mul] using hh

omit [Finite D] in
private theorem product_first_normal : A.Normal := by
  let e : (B × A) ≃* D := MulEquiv.prodComm.trans h.equiv
  let h' : InternalProduct B A := ⟨e, fun b a => (h.apply_eq a b).trans (product_commutes h a b)⟩
  exact h'.second_normal

omit [Finite D] in
theorem centralizer_first_eq_second (hz : center A = ⊥) :
    centralizer (A : Set D) = B := by
  have hbC : B ≤ centralizer (A : Set D) := by
    intro b hb
    exact mem_centralizer_iff.mpr (fun a ha => product_commutes h ⟨a,ha⟩ ⟨b,hb⟩)
  apply le_antisymm ?_ hbC
  intro x hx
  obtain ⟨a,b,rfl⟩ := h.exists_mul x
  have haC : (a : D) ∈ centralizer (A : Set D) := by
    have he := (centralizer (A : Set D)).mul_mem hx
      ((centralizer (A : Set D)).inv_mem (hbC b.property))
    simpa only [mul_inv_cancel_right] using he
  have haZ : a ∈ center A := by
    apply mem_center_iff.mpr
    intro z
    exact Subtype.ext (mem_centralizer_iff.mp haC z z.property)
  have ha1 : a = 1 := hz.le haZ
  simpa only [ha1, OneMemClass.coe_one, one_mul] using b.property

omit [Finite D] in
theorem normal_disjoint_first_le_second (hz : center A = ⊥)
    (N : Subgroup D) [N.Normal] (hd : Disjoint N A) : N ≤ B := by
  let : A.Normal := product_first_normal h
  have hc : ⁅N,A⁆ = ⊥ := bot_unique ((commutator_le_inf N A).trans
    (hd inf_le_left inf_le_right))
  rw [← h.centralizer_first_eq_second hz]
  exact commutator_eq_bot_iff_le_centralizer.mp hc

theorem automorphism_permutation [Nontrivial A] [Nontrivial B]
    (hA : ∀ (N : Subgroup A) [N.Normal], N ≠ ⊥ → IsPGroup 2 (A ⧸ N))
    (hB : ∀ (N : Subgroup B) [N.Normal], N ≠ ⊥ → IsPGroup 2 (B ⧸ N))
    (hcore : pCore 2 A = ⊥) (hz : center B = ⊥) (e : MulAut D) :
    (A.map e.toMonoidHom = A ∧ B.map e.toMonoidHom = B) ∨
      (A.map e.toMonoidHom = B ∧ B.map e.toMonoidHom = A) := by
  let f : MulAut (A × B) := h.equiv.trans (e.trans h.equiv.symm)
  have left_coe (a : A) : h.equiv (f (a,1)) = e (a : D) := by
    change h.equiv (h.equiv.symm (e (h.equiv (a,1)))) = e (a : D)
    rw [h.equiv.apply_symm_apply, h.apply_eq]
    simp only [OneMemClass.coe_one, mul_one]
  have right_coe (b : B) : h.equiv (f (1,b)) = e (b : D) := by
    change h.equiv (h.equiv.symm (e (h.equiv (1,b)))) = e (b : D)
    rw [h.equiv.apply_symm_apply, h.apply_eq]
    simp only [OneMemClass.coe_one, one_mul]
  have in_left (x : A × B) (hx : x.2 = 1) : h.equiv x ∈ A := by
    rw [show x = (x.1,x.2) from rfl, h.apply_eq, hx]
    simpa only [OneMemClass.coe_one, mul_one] using x.1.property
  have in_right (x : A × B) (hx : x.1 = 1) : h.equiv x ∈ B := by
    rw [show x = (x.1,x.2) from rfl, h.apply_eq, hx]
    simpa only [OneMemClass.coe_one, one_mul] using x.2.property
  rcases automorphism_product_coordinates hA hB hcore hz f with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · left
    have hAA : A.map e.toMonoidHom ≤ A := by
      rintro _ ⟨a,ha',rfl⟩
      change e a ∈ _
      rw [← left_coe ⟨a,ha'⟩]
      exact in_left _ (ha _)
    have hBB : B.map e.toMonoidHom ≤ B := by
      rintro _ ⟨b,hb',rfl⟩
      change e b ∈ _
      rw [← right_coe ⟨b,hb'⟩]
      exact in_right _ (hb _)
    exact ⟨eq_of_le_of_card_ge hAA (by rw [card_map_of_injective e.injective]),
      eq_of_le_of_card_ge hBB (by rw [card_map_of_injective e.injective])⟩
  · right
    have hAB : A.map e.toMonoidHom ≤ B := by
      rintro _ ⟨a,ha',rfl⟩
      change e a ∈ _
      rw [← left_coe ⟨a,ha'⟩]
      exact in_right _ (ha _)
    have hBA : B.map e.toMonoidHom ≤ A := by
      rintro _ ⟨b,hb',rfl⟩
      change e b ∈ _
      rw [← right_coe ⟨b,hb'⟩]
      exact in_left _ (hb _)
    have hcardA := Nat.le_of_dvd (Nat.card_pos (α := B)) (card_dvd_of_le hAB)
    have hcardB := Nat.le_of_dvd (Nat.card_pos (α := A)) (card_dvd_of_le hBA)
    rw [card_map_of_injective e.injective] at hcardA hcardB
    exact ⟨eq_of_le_of_card_ge hAB (by rwa [card_map_of_injective e.injective]),
      eq_of_le_of_card_ge hBA (by rwa [card_map_of_injective e.injective])⟩
end InternalProduct
end CFSG.Quasithin.ChapterB.SourceInduction


namespace CFSG.Quasithin.ChapterB.SourceInduction
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V}

theorem SourceTwoFactorCase.automorphism_permutation (d : SourceTwoFactorCase ρ)
    (hcore : pCore 2 D = ⊥) (e : MulAut D) :
    (d.first.map e.toMonoidHom = d.first ∧ d.second.map e.toMonoidHom = d.second) ∨
      (d.first.map e.toMonoidHom = d.second ∧ d.second.map e.toMonoidHom = d.first) := by
  let : Nontrivial d.first := d.firstCase.nontrivial
  let : Nontrivial d.second := d.secondCase.nontrivial
  let : d.first.Normal := InternalProduct.product_first_normal d.product
  have hc : pCore 2 d.first = ⊥ := by
    have hle : (pCore 2 d.first).map d.first.subtype ≤ pCore 2 D :=
      le_sSup ⟨inferInstance, pCore_isPGroup.map d.first.subtype⟩
    rw [hcore] at hle
    apply (eq_bot_iff_forall _).mpr
    intro x hx
    exact Subtype.ext (hle (mem_map_of_mem d.first.subtype hx))
  exact d.product.automorphism_permutation d.firstCase.normal_quotient_two
    d.secondCase.normal_quotient_two hc d.secondCase.center_eq_bot e

end CFSG.Quasithin.ChapterB.SourceInduction


namespace CFSG.Quasithin.ChapterB.SourceInduction
open Subgroup Representation Theory.GroupTheory
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V}
namespace InternalProduct
variable {A B : Subgroup D} (h : InternalProduct A B)
include h

noncomputable def swap : InternalProduct B A :=
  ⟨MulEquiv.prodComm.trans h.equiv, fun b a =>
    (h.apply_eq a b).trans (product_commutes h a b)⟩

theorem disjoint : Disjoint A B := by
  apply Subgroup.disjoint_def.mpr
  intro x ha hb
  have he : h.equiv (⟨x,ha⟩,1) = h.equiv (1,⟨x,hb⟩) := by
    simp only [h.apply_eq, OneMemClass.coe_one, mul_one, one_mul]
  exact congrArg (fun p : A × B => (p.1 : D)) (h.equiv.injective he)

theorem commutator_eq_bot : ⁅A,B⁆ = ⊥ := by
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  intro a ha
  exact mem_centralizer_iff.mpr (fun b hb => (product_commutes h ⟨a,ha⟩ ⟨b,hb⟩).symm)
end InternalProduct

noncomputable def SourceTwoFactorCase.swap (d : SourceTwoFactorCase ρ) : SourceTwoFactorCase ρ where
  first := d.second
  second := d.first
  product := d.product.swap
  firstSpace := d.secondSpace
  secondSpace := d.firstSpace
  decomposition := d.decomposition.symm
  firstCase := d.secondCase
  secondCase := d.firstCase
end CFSG.Quasithin.ChapterB.SourceInduction
