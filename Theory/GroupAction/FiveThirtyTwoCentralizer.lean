module

public import Theory.GroupAction.CoprimeNormalizerDecomposition
public import Theory.GroupAction.FiveSixteenCentralizer
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Five-centralizers on an abelian group of order thirty-two

Orbit counting forces the fixed subgroup of a faithful five-action to have
order two. Coprime splitting gives a moving subgroup of order sixteen.
The whole normalizer acts faithfully on this moving subgroup, since the
fixed subgroup has no nonidentity automorphisms. Restriction embeds the
centralizer into the centralizer of the restricted five-action, whose order
divides fifteen by the free-action calculation in FiveSixteenCentralizer.

This source-independent finite-action lemma supplies the natural-module
calculation for the PSL₅(2) case of Aschbacher–Smith, 16.3.5, printed p.1179.
-/

open Subgroup
open scoped IsMulCommutative

namespace Subgroup.FiveThirtyTwo

variable {H V : Type*} [Group H] [Finite H] [Group V] [Finite V]
  [IsMulCommutative V] [MulDistribMulAction H V] [FaithfulSMul H V]

/-- The centralizer of a five-subgroup on an abelian group of order 32
has order dividing 15, for the given faithful action. -/
public theorem centralizer_card_dvd_fifteen (A : Subgroup H)
    (hA : Nat.card A = 5) (hV : Nat.card V = 32) :
    Nat.card (centralizer (A : Set H)) ∣ 15 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let F := FixedPoints.subgroup A V
  let W := commutatorAction A V
  let N := normalizer (A : Set H)
  have hF : Nat.card F = 2 := by
    have hmod := (IsPGroup.of_card (p := 5) (G := A) (n := 1)
      (by simpa using hA)).card_modEq_card_fixedPoints V
    change Nat.card V % 5 = Nat.card F % 5 at hmod
    rw [hV] at hmod
    have hdiv : Nat.card F ∣ 32 := hV ▸ F.card_subgroup_dvd_card
    have hproper : Nat.card F ≠ 32 := by
      intro hh
      have htop : F = ⊤ := F.eq_top_of_card_eq (hh.trans hV.symm)
      have hbot : A = ⊥ := by
        apply eq_bot_iff.mpr
        intro a ha
        apply mem_bot.mpr
        apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
        intro v
        have hv : v ∈ F := htop ▸ mem_top v
        simpa only [Subgroup.smul_def, one_smul] using hv ⟨a, ha⟩
      rw [hbot, card_bot] at hA
      omega
    have hmem := Nat.mem_divisors.mpr ⟨hdiv, by decide⟩
    rw [show (32 : ℕ).divisors = {1, 2, 4, 8, 16, 32} by decide] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  have hcop : Nat.Coprime (Nat.card A) (Nat.card V) := by rw [hA, hV]; decide
  have hcompl : IsCompl F W :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (Group.isSolvable_of_comm (fun a b : V => mul_comm a b)) hcop inferInstance
  have hW : Nat.card W = 16 := by
    have hh := card_sup_eq_mul_of_normalizes_of_disjoint F W
      (by rw [normalizer_eq_top]; exact le_top) hcompl.disjoint
    rw [hcompl.sup_eq_top, card_top, hF, hV] at hh
    omega
  let : IsCyclic F := isCyclic_of_prime_card hF
  have hAutF : Nat.card (MulAut F) = 1 := by rw [IsCyclic.card_mulAut, hF]; decide
  let : Subsingleton (MulAut F) := (Nat.card_eq_one_iff_unique.mp hAutF).1
  let : IsInvariant N V F := fixedPoints_isInvariant_of_normalizing_actor N A le_rfl
  let : IsInvariant N V W := commutatorAction_isInvariant_of_normalizing_actor N A le_rfl
  let f := MulDistribMulAction.toMulAut N W
  let r := MulDistribMulAction.toMulAut N F
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_iff.mpr
    intro n hn
    apply mem_bot.mpr
    apply Subtype.ext
    apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
    intro v
    obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.mp
      (show v ∈ F ⊔ W by rw [hcompl.sup_eq_top]; trivial)
    have hxfix : (n : H) • x = x :=
      congrArg Subtype.val (MulEquiv.congr_fun (Subsingleton.elim (r n) 1) ⟨x, hx⟩)
    have hyfix : (n : H) • y = y :=
      congrArg Subtype.val (MulEquiv.congr_fun (MonoidHom.mem_ker.mp hn) ⟨y, hy⟩)
    simp only [smul_mul', hxfix, hyfix, Subgroup.coe_one, one_smul]
  let A₀ := A.subgroupOf N
  let D := A₀.map f
  have hD : Nat.card D = 5 := by
    rw [card_map_of_injective hf]
    exact (Nat.card_congr (subgroupOfEquivOfLe A.le_normalizer).toEquiv).trans hA
  let C := centralizer (A : Set H)
  let c : C →* N := inclusion (centralizer_le_normalizer (A : Set H))
  let g : C →* centralizer (D : Set (MulAut W)) :=
    (f.comp c).codRestrict _ (by
      intro x
      apply mem_centralizer_iff.mpr
      rintro _ ⟨a, ha, rfl⟩
      change f a * f (c x) = f (c x) * f a
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact mem_centralizer_iff.mp x.property a.val ha)
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : N => (z : H)) (hf (congrArg Subtype.val h))
  exact (card_dvd_of_injective g hg).trans (card_centralizer_five_dvd_fifteen D hD hW)
end Subgroup.FiveThirtyTwo
