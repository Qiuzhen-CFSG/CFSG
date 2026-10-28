module

public import Theory.Representation.AbelianWeightAutomizer
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Fintype.Perm

/-!
# Three-group weight indices in degree three

The conjugation action on a self-centralizing normal abelian subgroup has
kernel exactly that subgroup. Its faithful permutation action on occurring
weights embeds the quotient in a symmetric group of degree at most three.
A nontrivial three-group quotient then has order three, and all three weights
must occur. Irreducibility is not needed for this argument.

This is the index and weight-count step of Aschbacher–Smith,
Lemma A.3.21(c), printed pp. 55–56.
-/

public section

open scoped IsMulCommutative
namespace Representation
variable {E G V : Type*} [Field E] [IsAlgClosed E] [Group G] [Finite G]
  [AddCommGroup V] [Module E V] [FiniteDimensional E V]

/-- A self-centralizing abelian normal subgroup has index three and three weights. -/
theorem threeGroup_abelian_selfCentralizing_index_and_weights
    (rho : Representation E G V) (hrho : Function.Injective rho)
    (hG : IsPGroup 3 G) (hn : ¬ IsMulCommutative G)
    (hdim : Module.finrank E V ≤ 3)
    (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    (hCA : Subgroup.centralizer (A : Set G) ≤ A)
    (horder : (Nat.card A : E) ≠ 0) :
    A.index = 3 ∧ Nat.card (CharacterWeight (rho.comp A.subtype)) = 3 := by
  classical
  let W := CharacterWeight (rho.comp A.subtype)
  obtain ⟨hfinite, hbound⟩ := characterWeight_card_le (rho.comp A.subtype) horder
  let := hfinite
  let := Fintype.ofFinite W
  let i : G →* Subgroup.normalizer (A : Set G) :=
    (MonoidHom.id G).codRestrict _ (fun g => by rw [A.normalizer_eq_top]; trivial)
  let f : G →* Equiv.Perm W :=
    ((automizerWeightPerm rho A).comp A.normalizerMonoidHom.rangeRestrict).comp i
  have hker : f.ker = A := by
    have h := normalizerWeightPerm_ker rho A hrho horder
    ext g
    change i g ∈ ((automizerWeightPerm rho A).comp
      A.normalizerMonoidHom.rangeRestrict).ker ↔ g ∈ A
    rw [h]
    change g ∈ Subgroup.centralizer (A : Set G) ↔ g ∈ A
    exact ⟨fun h => hCA h, fun h => A.le_centralizer h⟩
  have hdiv : A.index ∣ (Nat.card W).factorial := by
    rw [← hker, Subgroup.index_ker]
    have hd := f.range.card_subgroup_dvd_card
    simpa only [Nat.card_eq_fintype_card, Fintype.card_perm] using hd
  have hbound' : Nat.card W ≤ 3 := hbound.trans hdim
  have hi6 : A.index ≤ 6 := by
    have hle := Nat.le_of_dvd (Nat.factorial_pos (Nat.card W)) hdiv
    exact hle.trans (by simpa only [show Nat.factorial 3 = 6 from rfl] using Nat.factorial_le hbound')
  have hne : A.index ≠ 1 := by
    intro h
    have htop := Subgroup.index_eq_one.mp h
    apply hn
    refine ⟨⟨fun x y => ?_⟩⟩
    exact congrArg Subtype.val (mul_comm (⟨x, htop ▸ Subgroup.mem_top x⟩ : A)
      (⟨y, htop ▸ Subgroup.mem_top y⟩ : A))
  obtain ⟨n, hncard⟩ := hG.index A
  have hnle : n ≤ 1 := by
    by_contra! hh
    have hh' := Nat.pow_le_pow_right (by decide : 0 < 3) hh
    rw [← hncard] at hh'
    norm_num at hh'
    omega
  have hi3 : A.index = 3 := by
    interval_cases n
    · simp_all
    · simpa using hncard
  refine ⟨hi3, ?_⟩
  rw [hi3] at hdiv
  change Nat.card W = 3
  by_contra hnot
  have hsmall : Nat.card W ≤ 2 := by omega
  interval_cases hcard : Nat.card W <;> norm_num [hcard] at hdiv
end Representation
