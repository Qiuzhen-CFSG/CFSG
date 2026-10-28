module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.LocalSylow

/-!
# The complete elementary-subgroup catalogue for Held's Sylow group

Every elementary abelian subgroup of order sixteen in the displayed D is
exactly one of M, S, L₁ and L₂. The proof counts within 128 binary coordinates,
without enumerating the subgroup lattice or the whole alternating group.
An involution outside the four candidates has only twelve commuting
square-one elements, so cannot lie in an elementary sixteen. An element
belonging to exactly one candidate then forces the entire subgroup into it.
If every element belongs to at least two candidates, a noncommon element
has sixteen shared commuting elements, including a noncommuting pair.
The order-sixteen subgroup would contain that pair, a contradiction.
The four common elements alone cannot contain an elementary sixteen.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Section 1, p.225; this catalogue is used in
Lemmas 2.4 and 2.6.
-/

open Subgroup Equiv
open scoped IsMulCommutative
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
open Coordinates

local instance codeDecidableEq : DecidableEq Code := inferInstance
local instance modelDecidableEq : DecidableEq H := inferInstance
private abbrev DCode := BaseCode × Fin 2 × Fin 2 × Fin 2
local instance dcodeDecidableEq : DecidableEq DCode := inferInstance
private def toCode (a : DCode) : Code := (a.1, a.2.1, a.2.2.1, 0, a.2.2.2)
private def dword (a : DCode) : H := word (toCode a)

private theorem dword_injective : Function.Injective dword := by
  intro a b hab
  have h := word_injective hab
  simpa [toCode, Prod.ext_iff] using h

private theorem dword_mem (a : DCode) : dword a ∈ modelD := by
  rw [dword, word_mem_modelD]
  rfl

private theorem exists_dword {x : H} (hx : x ∈ modelD) : ∃ a, dword a = x := by
  obtain ⟨⟨b,t,t',r,l⟩, rfl⟩ := word_bijective.surjective x
  have hr := (word_mem_modelD _).mp hx
  exact ⟨(b,t,t',l), by simpa [dword, toCode] using congrArg word (show (b,t,t',0,l) = (b,t,t',r,l) by simp_all)⟩

private def rowRead (k : Fin 4) (a : DCode) : BaseCode :=
  ![a.1, (a.1.1, a.1.2.1, a.2.1, a.2.2.2),
    (a.1.1, a.1.2.1, a.2.2.2, a.1.2.2.2),
    (a.1.1, a.1.2.1, a.2.1, a.1.2.2.2)] k

private def row (k : Fin 4) (a : DCode) : Prop := elementaryCode k (rowRead k a) = toCode a
private instance (k : Fin 4) (a : DCode) : Decidable (row k a) := by unfold row; infer_instance

private theorem row_iff (k : Fin 4) (a : DCode) : row k a ↔ dword a ∈ elementary k := by
  rw [mem_elementary]
  constructor
  · intro h
    exact ⟨rowRead k a, (elementaryWord_eq_word k _).trans (congrArg word h)⟩
  · rintro ⟨b, hb⟩
    have hc : elementaryCode k b = toCode a := word_injective ((elementaryWord_eq_word k b).symm.trans hb)
    have test : ∀ (k : Fin 4) (a : DCode) (b : BaseCode),
        elementaryCode k b = toCode a → row k a := by decide +kernel
    exact test k a b hc

private def covered (a : DCode) : Prop := ∃ k, row k a
private def shared (a : DCode) : Prop := ∃ k l, k ≠ l ∧ row k a ∧ row l a
private instance (a : DCode) : Decidable (covered a) := by unfold covered; infer_instance
private instance (a : DCode) : Decidable (shared a) := by unfold shared; infer_instance

private def commutingSquares (a : DCode) : Finset DCode :=
  Finset.univ.filter fun b => dword b ^ 2 = 1 ∧ dword b * dword a = dword a * dword b

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem outside_count : ∀ a : DCode, dword a ^ 2 = 1 → ¬ covered a →
    (commutingSquares a).card = 12 := by decide +kernel

private theorem card_le_coordinates (A : Subgroup H) (hAD : A ≤ modelD)
    (p : DCode → Prop) (hp : ∀ a, dword a ∈ A → p a) :
    Nat.card A ≤ Nat.card {a // p a} := by
  classical
  let f (x : A) : DCode := Classical.choose (exists_dword (hAD x.property))
  have hf (x : A) : dword (f x) = x := Classical.choose_spec (exists_dword (hAD x.property))
  let g (x : A) : {a // p a} := ⟨f x, hp (f x) (by rw [hf]; exact x.property)⟩
  apply Nat.card_le_card_of_injective g
  intro x y h
  apply Subtype.ext
  exact (hf x).symm.trans ((congrArg dword (congrArg Subtype.val h)).trans (hf y))

private theorem elementary_covered (A : Subgroup H) (hAD : A ≤ modelD)
    (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 16) (a : DCode)
    (ha : dword a ∈ A) : covered a := by
  let := hA
  by_contra hn
  have hle := card_le_coordinates A hAD (fun b => b ∈ commutingSquares a) (fun b hb => by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hb,
      setLike_mul_comm hb ha⟩)
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_coe, outside_count a
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ ha) hn] at hle
  omega

private def common (a : DCode) : Prop := ∀ k, row k a
private instance (a : DCode) : Decidable (common a) := by unfold common; infer_instance
private theorem common_card : Nat.card {a : DCode // common a} = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem exclusive_commuting : ∀ (k : Fin 4) (a : DCode), row k a → ¬ shared a →
    ∀ b : DCode, covered b → dword b * dword a = dword a * dword b → row k b := by
  decide +kernel

private def sharedCommuting (a : DCode) : Finset DCode :=
  Finset.univ.filter fun b => shared b ∧ dword b * dword a = dword a * dword b

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem sharedCommuting_card : ∀ a : DCode, shared a → ¬ common a →
    (sharedCommuting a).card = 16 := by decide +kernel

private def witnessLeft : Fin 2 → DCode := ![((0,0,0,1),0,0,0), ((0,0,1,1),0,0,0)]
private def witnessRight : Fin 2 → DCode := ![((0,0,0,0),0,0,1), ((0,0,0,0),1,0,1)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem sharedCommuting_noncommuting : ∀ a : DCode, shared a → ¬ common a →
    ∃ i : Fin 2, witnessLeft i ∈ sharedCommuting a ∧ witnessRight i ∈ sharedCommuting a ∧
      dword (witnessLeft i) * dword (witnessRight i) ≠
        dword (witnessRight i) * dword (witnessLeft i) := by decide +kernel

private theorem mem_of_card_coordinates (A : Subgroup H) (hAD : A ≤ modelD)
    (p : DCode → Prop) (hp : ∀ a, dword a ∈ A → p a)
    (hc : Nat.card {a // p a} ≤ Nat.card A) (b : DCode) (hb : p b) : dword b ∈ A := by
  classical
  let f (x : A) : DCode := Classical.choose (exists_dword (hAD x.property))
  have hf (x : A) : dword (f x) = x := Classical.choose_spec (exists_dword (hAD x.property))
  let g (x : A) : {a // p a} := ⟨f x, hp (f x) (by rw [hf]; exact x.property)⟩
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    exact (hf x).symm.trans ((congrArg dword (congrArg Subtype.val h)).trans (hf y))
  have hsurj := (hg.bijective_of_nat_card_le hc).surjective
  obtain ⟨x, hx⟩ := hsurj ⟨b,hb⟩
  have he : dword b = x := (congrArg dword (congrArg Subtype.val hx)).symm.trans (hf x)
  rw [he]
  exact x.property

/-- The four displayed subgroups exhaust the elementary subgroups of order sixteen in D. -/
public theorem model_elementary_sixteen (A : Subgroup H) (hAD : A ≤ modelD)
    (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 16) :
    ∃ k : Fin 4, A = elementary k := by
  classical
  let := hA
  have hcovered := elementary_covered A hAD hA hcard
  by_cases he : ∃ a : DCode, dword a ∈ A ∧ ¬ shared a
  · obtain ⟨a,ha,hn⟩ := he
    obtain ⟨k,hk⟩ := hcovered a ha
    refine ⟨k, eq_of_le_of_card_ge ?_ (by rw [hcard, elementary_card])⟩
    intro x hx
    obtain ⟨b,rfl⟩ := exists_dword (hAD hx)
    exact (row_iff k b).mp (exclusive_commuting k a hk hn b
      (hcovered b hx) (setLike_mul_comm hx ha))
  · have hs : ∀ a, dword a ∈ A → shared a := by simpa only [not_exists, not_and, not_not] using he
    have hc : ∀ a, dword a ∈ A → common a := by
      intro a ha
      by_contra hn
      have hsub : ∀ b, dword b ∈ A → b ∈ sharedCommuting a := by
        intro b hb
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs b hb, setLike_mul_comm hb ha⟩
      have hsize : Nat.card {b // b ∈ sharedCommuting a} ≤ Nat.card A := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe,
          sharedCommuting_card a (hs a ha) hn, hcard]
      obtain ⟨i,hi,hj,hne⟩ := sharedCommuting_noncommuting a (hs a ha) hn
      have hmem := mem_of_card_coordinates A hAD _ hsub hsize
      exact hne (setLike_mul_comm (hmem _ hi) (hmem _ hj))
    have hle := card_le_coordinates A hAD common hc
    rw [common_card, hcard] at hle
    omega

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
