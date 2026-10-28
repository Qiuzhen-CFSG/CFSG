module
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.Fintype.Perm
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Large elementary subgroups of E₄ × S₄

An elementary subgroup of order sixteen projects to an elementary subgroup
of S₄ of order at least four. Two distinct nonidentity elements of that
image have a common centralizer of order four. The full product centralizer
therefore has order at most sixteen, forcing equality with the original
abelian subgroup.

Only the common centralizer of two permutations on four letters is checked
by finite computation. The cardinal reduction and the product argument are
structural. This is the local group calculation in Aschbacher–Smith F.5.4(1),
printed p.301, used for the literal exceptional unitary endpoint subgroups.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace SymmetricFourElementary
local notation "S4" => Equiv.Perm (Fin 4)
local notation "C2" => Multiplicative (ZMod 2)

private theorem pair_centralizer :
    ∀ a b x : S4, (a ≠ 1 ∧ a ^ 2 = 1 ∧ b ≠ 1 ∧ b ≠ a ∧ b ^ 2 = 1 ∧
      a * b = b * a ∧ x * a = a * x ∧ x * b = b * x) →
      x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by decide +kernel

private theorem centralizer_card_le_four (B : Subgroup S4)
    [IsElementaryAbelian 2 B] (hB : 4 ≤ Nat.card B) :
    Nat.card (centralizer (B : Set S4)) ≤ 4 := by
  classical
  let : Nontrivial B := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a,ha⟩ := exists_ne (1 : B)
  have ha1 : (a : S4) ≠ 1 := fun h => ha (Subtype.ext h)
  have ha2 : (a : S4)^2=1 := elemPow_eq_one_of_isElementaryAbelian _ a.property
  have hnot : ¬ B ≤ zpowers (a : S4) := by
    intro h
    have hc := card_le_of_le h
    rw [Nat.card_zpowers] at hc
    have ho := Nat.le_of_dvd (by decide : 0 < 2) (orderOf_dvd_of_pow_eq_one ha2)
    omega
  obtain ⟨b,hb,hba⟩ := Set.not_subset.mp hnot
  have hb1 : b ≠ 1 := fun h => hba (h ▸ one_mem _)
  have hbne : b ≠ a := fun h => hba (h ▸ mem_zpowers _)
  have hb2 : b^2=1 := elemPow_eq_one_of_isElementaryAbelian _ hb
  have hab : (a:S4)*b=b*a := congrArg Subtype.val (mul_comm a (⟨b,hb⟩ : B))
  let s : Finset S4 := {1,(a:S4),b,(a:S4)*b}
  have hs (x : centralizer (B : Set S4)) : x.val ∈ s := by
    have hxa := (mem_centralizer_iff.mp x.property a a.property).symm
    have hxb := (mem_centralizer_iff.mp x.property b hb).symm
    simpa only [s,Finset.mem_insert,Finset.mem_singleton] using
      pair_centralizer a b x ⟨ha1,ha2,hb1,hbne,hb2,hab,hxa,hxb⟩
  let f : centralizer (B : Set S4) → s := fun x => ⟨x.val,hs x⟩
  have hf : Function.Injective f := fun x y h => Subtype.ext (congrArg (fun x : s => x.val) h)
  have hc := Nat.card_le_card_of_injective f hf
  have hs4 : s.card ≤ 4 := by
    have h1 := Finset.card_insert_le (1:S4) ({(a:S4),b,(a:S4)*b}:Finset S4)
    have h2 := Finset.card_insert_le (a:S4) ({b,(a:S4)*b}:Finset S4)
    have h3 := Finset.card_insert_le b ({(a:S4)*b}:Finset S4)
    simp only [Finset.card_singleton] at h3
    dsimp [s]
    omega
  exact hc.trans (by simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using hs4)

/-- An elementary subgroup of order sixteen in E₄ × S₄ is self-centralizing. -/
theorem centralizer_eq_of_elementary_card_sixteen
    (A : Subgroup ((C2 × C2) × S4)) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 16) : centralizer (A : Set ((C2 × C2) × S4)) = A := by
  classical
  let B := A.map (MonoidHom.snd (C2 × C2) S4)
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  let f : A → (C2 × C2) × B := fun x => ⟨x.val.1,⟨x.val.2,⟨x.val,x.property,rfl⟩⟩⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact Prod.ext (congrArg (fun z : (C2 × C2) × B => z.1) h)
      (congrArg (fun z : (C2 × C2) × B => z.2.val) h)
  have hc := Nat.card_le_card_of_injective f hf
  have hK : Nat.card (C2 × C2) = 4 := by simp [Nat.card_eq_fintype_card]
  rw [Nat.card_prod,hK,hA] at hc
  have hB : 4 ≤ Nat.card B := by omega
  let C := centralizer (A : Set ((C2 × C2) × S4))
  have hcB (x : C) : x.val.2 ∈ centralizer (B : Set S4) := by
    rintro y ⟨a,ha,rfl⟩
    exact congrArg Prod.snd (mem_centralizer_iff.mp x.property a ha)
  let g : C → (C2 × C2) × centralizer (B : Set S4) := fun x => ⟨x.val.1,⟨x.val.2,hcB x⟩⟩
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    exact Prod.ext (congrArg (fun z : (C2 × C2) × centralizer (B : Set S4) => z.1) h)
      (congrArg (fun z : (C2 × C2) × centralizer (B : Set S4) => z.2.val) h)
  have hC := Nat.card_le_card_of_injective g hg
  rw [Nat.card_prod,hK] at hC
  have hbound := centralizer_card_le_four B hB
  have hle : A ≤ C := le_centralizer_iff_isMulCommutative.mpr inferInstance
  exact (eq_of_le_of_card_ge hle (by rw [hA]; omega)).symm

end SymmetricFourElementary
