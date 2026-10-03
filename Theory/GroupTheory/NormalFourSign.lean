module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow

/-!
# The sign of the action on a normal four-group

A two-subgroup acting nontrivially on an elementary four-group detects a
nontrivial sign character of its normalizer. The kernel has index two and
contains the four-group. The action on the three nonidentity elements is
faithful, and a two-group cannot have a nontrivial image in the alternating
group of order three.

This is the index-two subgroup used in Janko–Thompson, Math. Z. 113 (1970),
§6, p.395. Only the noncentral two-group action is needed for this step.
-/

namespace Subgroup

private noncomputable def nonidentityPermHom (A : Type*) [Group A] :
    MulAut A →* Equiv.Perm {a : A // a ≠ 1} where
  toFun f := Equiv.Perm.subtypePerm f.toEquiv (fun x => by simp)
  map_one' := by ext x; rfl
  map_mul' f g := by ext x; rfl

private theorem nonidentityPermHom_injective (A : Type*) [Group A] :
    Function.Injective (nonidentityPermHom A) := by
  intro f g h
  ext x
  by_cases hx : x = 1
  · simp [hx]
  · exact congrArg Subtype.val (congrArg (fun k => k ⟨x, hx⟩) h)

private theorem sign_nontrivial_of_two_group_action
    {P A : Type*} [Group P] [Group A] [Finite P] [Finite A]
    [Fintype {a : A // a ≠ 1}] [DecidableEq {a : A // a ≠ 1}]
    (hP : IsPGroup 2 P) (hA : Nat.card A = 4)
    (f : P →* MulAut A) (hf : ∃ s, f s ≠ 1) :
    ∃ s, Equiv.Perm.sign (nonidentityPermHom A (f s)) ≠ 1 := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype A := Fintype.ofFinite A
  have hX : Nat.card {a : A // a ≠ 1} = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp [← Nat.card_eq_fintype_card, hA]
  let : Nontrivial {a : A // a ≠ 1} :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hAlt : Nat.card (alternatingGroup {a : A // a ≠ 1}) = 3 := by
    rw [nat_card_alternatingGroup, hX]
    decide
  by_contra! hsign
  let a : P →* alternatingGroup {a : A // a ≠ 1} :=
    { toFun s := ⟨nonidentityPermHom A (f s), hsign s⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' s t := by apply Subtype.ext; simp }
  obtain ⟨s, hs⟩ := hf
  have hc : Nat.Coprime (orderOf (a s)) 3 :=
    (hP.orderOf_coprime (by decide : Nat.Coprime 2 3) s).coprime_dvd_left
      (orderOf_map_dvd a s)
  have hd : orderOf (a s) ∣ 3 := hAlt ▸ _root_.orderOf_dvd_natCard (a s)
  have ha : a s = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hc (dvd_refl _) hd)
  apply hs
  apply nonidentityPermHom_injective A
  simpa [a] using congrArg Subtype.val ha

/-- A noncentral two-group action on an elementary four produces an index-two
sign kernel in the normalizer, containing the four-group. -/
public theorem exists_normalizer_sign_of_noncentral_four
    {G : Type*} [Group G] [Finite G]
    (P W : Subgroup G) (hP : IsPGroup 2 P)
    (hPN : P ≤ normalizer (W : Set G))
    [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hnc : ¬ P ≤ centralizer (W : Set G)) :
    ∃ f : normalizer (W : Set G) →* ℤˣ,
      (∃ s, f s ≠ 1) ∧ f.ker.index = 2 ∧
        W ≤ f.ker.map (normalizer (W : Set G)).subtype := by
  classical
  let : Fintype {a : W // a ≠ 1} := Fintype.ofFinite _
  let N := normalizer (W : Set G)
  let ρ := (nonidentityPermHom W).comp W.normalizerMonoidHom
  let f := Equiv.Perm.sign.comp ρ
  let i : P →* N := inclusion hPN
  have ha : ∃ s : P, (W.normalizerMonoidHom.comp i) s ≠ 1 := by
    by_contra! h
    apply hnc
    intro p hp
    have hk : i ⟨p, hp⟩ ∈ W.normalizerMonoidHom.ker := h ⟨p, hp⟩
    rw [normalizerMonoidHom_ker] at hk
    exact hk
  obtain ⟨s, hs⟩ := sign_nontrivial_of_two_group_action hP hW
    (W.normalizerMonoidHom.comp i) ha
  have hindex : f.ker.index = 2 := by
    rw [index_ker]
    have hd : Nat.card f.range ∣ 2 := by
      simpa [Nat.card_eq_fintype_card] using card_subgroup_dvd_card f.range
    have hn : Nontrivial f.range := nontrivial_of_ne
      (⟨f (i s), ⟨i s, rfl⟩⟩ : f.range) 1
      (fun h => hs (congrArg Subtype.val h))
    have hl : 1 < Nat.card f.range := Finite.one_lt_card
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · omega
    · exact h
  refine ⟨f, ⟨i s, hs⟩, hindex, ?_⟩
  intro w hw
  let wN : N := ⟨w, le_normalizer hw⟩
  have hc : wN ∈ W.normalizerMonoidHom.ker := by
    rw [normalizerMonoidHom_ker]
    intro x hx
    exact congrArg Subtype.val
      ((@IsMulCommutative.is_comm W _ _).comm (⟨x, hx⟩ : W) (⟨w, hw⟩ : W))
  refine mem_map.mpr ⟨wN, ?_, rfl⟩
  change Equiv.Perm.sign (nonidentityPermHom W (W.normalizerMonoidHom wN)) = 1
  rw [show W.normalizerMonoidHom wN = 1 from hc, map_one, map_one]

end Subgroup
