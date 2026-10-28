module
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# A derived bound from three elementary quotient lines

Let f map a finite group X onto a four-element group. Suppose its kernel
and three supplied subgroups of X are elementary abelian at two, and the
three subgroup images have order two and are distinct. If [X,ker f] lies
in a subgroup Z, then the derived subgroup of X lies in Z. No centrality
or normality of Z is required.

Each quotient line has a unique nonidentity element. The three distinct
nonidentity elements exhaust the quotient, so every x factors as a*k with
a in one supplied elementary subgroup and k in the kernel. Both factors
are involutions, giving x²=[a,k] in Z. Finally every commutator is a product
of squares, which proves the containment directly in X without a second
quotient construction.

This source-independent finite-group lemma supplies the index-eight
exclusion in the large branch of Stellmacher (10.1), printed pp.60–65 of
`refs/files/stellmacher-n-group.pdf`, with the actual neighborhood quotient
and its three neighbor-module images.
-/

namespace Subgroup
open scoped commutatorElement

private theorem three_order_two_subgroups_cover
    {Q : Type*} [Group Q] [Finite Q]
    (L : Fin 3 → Subgroup Q) (hQ : Nat.card Q = 4)
    (hL : ∀ i, Nat.card (L i) = 2) (hdistinct : Function.Injective L) :
    ∀ q : Q, ∃ i, q ∈ L i := by
  classical
  choose a ha huniq using fun i => (Nat.card_eq_two_iff' (1 : L i)).mp (hL i)
  have hane (i) : (a i : Q) ≠ 1 := fun h => ha i (Subtype.ext h)
  let point : Fin 3 → {q : Q // q ≠ 1} := fun i => ⟨a i,hane i⟩
  have hinj : Function.Injective point := by
    intro i j hij
    have heq : (a i : Q) = a j := congrArg Subtype.val hij
    apply hdistinct
    apply le_antisymm
    · intro q hq
      by_cases hq1 : q = 1
      · exact hq1 ▸ (L j).one_mem
      have hh := huniq i ⟨q,hq⟩ (fun h => hq1 (congrArg Subtype.val h))
      have hqa : q = (a j : Q) := (congrArg Subtype.val hh).trans heq
      exact hqa ▸ (a j).property
    · intro q hq
      by_cases hq1 : q = 1
      · exact hq1 ▸ (L i).one_mem
      have hh := huniq j ⟨q,hq⟩ (fun h => hq1 (congrArg Subtype.val h))
      have hqa : q = (a i : Q) := (congrArg Subtype.val hh).trans heq.symm
      exact hqa ▸ (a i).property
  have hnoncard : Nat.card {q : Q // q ≠ 1} = 3 := by
    let _ := Fintype.ofFinite Q
    change Nat.card ↥(({1} : Set Q)ᶜ) = 3
    rw [Nat.card_eq_fintype_card,Fintype.card_compl_set]
    have hc : Fintype.card Q = 4 := by simpa only [Nat.card_eq_fintype_card] using hQ
    simp [hc]
  have hsurj : Function.Surjective point :=
    ((Nat.bijective_iff_injective_and_card point).mpr
      ⟨hinj,by rw [Nat.card_fin,hnoncard]⟩).2
  intro q
  by_cases hq : q = 1
  · exact ⟨0,hq ▸ (L 0).one_mem⟩
  obtain ⟨i,hi⟩ := hsurj ⟨q,hq⟩
  have hiq : (a i : Q) = q := congrArg Subtype.val hi
  exact ⟨i,hiq ▸ (a i).property⟩

public theorem commutator_le_of_elementary_kernel_three_lines
    {X Q : Type*} [Group X] [Finite X] [Group Q] [Finite Q]
    (f : X →* Q) (_hf : Function.Surjective f) (Z : Subgroup X)
    (hKelem : IsElementaryAbelian 2 f.ker)
    (hKcomm : ⁅(⊤ : Subgroup X),f.ker⁆ ≤ Z)
    (A : Fin 3 → Subgroup X) (hAelem : ∀ i, IsElementaryAbelian 2 (A i))
    (hQcard : Nat.card Q = 4)
    (hAcard : ∀ i, Nat.card ((A i).map f) = 2)
    (hdistinct : Function.Injective (fun i => (A i).map f)) :
    _root_.commutator X ≤ Z := by
  have hcover := three_order_two_subgroups_cover (fun i => (A i).map f)
    hQcard hAcard hdistinct
  have hsquare (x : X) : x^2 ∈ Z := by
    obtain ⟨i,hi⟩ := hcover (f x)
    obtain ⟨a,ha,hfa⟩ := hi
    let k := a⁻¹*x
    have hk : k ∈ f.ker := by
      apply MonoidHom.mem_ker.mpr
      change f (a⁻¹*x) = 1
      rw [map_mul,map_inv,hfa,inv_mul_cancel]
    let _ := hAelem i
    let _ := hKelem
    have ha2 : a^2 = 1 := elemPow_eq_one_of_isElementaryAbelian a ha
    have hk2 : k^2 = 1 := elemPow_eq_one_of_isElementaryAbelian k hk
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ha2)
    have hki : k⁻¹ = k := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hk2)
    have hx : a*k = x := by simp [k]
    have hs : x^2 = ⁅a,k⁆ := by
      rw [←hx,commutatorElement_def,hai,hki,pow_two]
      simp only [mul_assoc]
    rw [hs]
    exact hKcomm (commutator_mem_commutator (mem_top a) hk)
  rw [_root_.commutator_def]
  apply commutator_le.mpr
  intro a _ b _
  have hid : ⁅a,b⁆ = a^2 * (a⁻¹*b)^2 * (b^2)⁻¹ := by
    simp [commutatorElement_def,pow_two,mul_assoc]
  rw [hid]
  exact Z.mul_mem (Z.mul_mem (hsquare a) (hsquare (a⁻¹*b))) (Z.inv_mem (hsquare b))
end Subgroup
