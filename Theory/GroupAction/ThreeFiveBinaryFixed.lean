module

public import Theory.GroupAction.CoprimeHall
public import Theory.ElementaryAbelian.Basic
public import Theory.GroupAction.Lemmas
public import Theory.GroupAction.NormalizingActor
public import Theory.GroupAction.ThreeFiveMovingFixed

/-!
# Binary fixed-point bounds for three- and five-actions

The moving summand of a coprime three-group action has trivial common fixed
subgroup. Orbit counting makes its order congruent to one modulo three.
A power of two with that residue cannot be congruent to two modulo five.
Thus, if a five-action fixes a nonidentity element of the moving summand,
it fixes at least four elements. Multiplication with the whole-group fixed
subgroup gives the corresponding factor-four bound.

The existence theorem for a nonidentity five-fixed moving vector, combined
with this cardinality argument, proves the full three-by-five inequality in
Thompson, *Nonsolvable finite groups all of whose local subgroups are
solvable*, VI, printed p.630.
-/

open scoped IsMulCommutative

namespace ThreeFiveAction

private theorem two_pow_mod_fifteen (n : ℕ) :
    2 ^ n % 15 = 1 ∨ 2 ^ n % 15 = 2 ∨
      2 ^ n % 15 = 4 ∨ 2 ^ n % 15 = 8 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rcases ih with h | h | h | h <;> simp [pow_succ, Nat.mul_mod, h]

private theorem two_pow_mod_five_ne_two (n : ℕ) (h3 : 2 ^ n % 3 = 1) :
    2 ^ n % 5 ≠ 2 := by
  have h15 := two_pow_mod_fifteen n
  have hmod3 := Nat.mod_mod_of_dvd (2 ^ n) (by decide : 3 ∣ 15)
  have hmod5 := Nat.mod_mod_of_dvd (2 ^ n) (by decide : 5 ∣ 15)
  omega

/-- With no common three-group fixed points, a nontrivial five-fixed subgroup
of a finite two-group has at least four elements. The two actions need not commute. -/
public theorem four_le_card_fixed_of_three_fixed_eq_bot
    {B A W : Type*} [Group B] [Group A] [Group W] [Finite W]
    [MulDistribMulAction B W] [MulDistribMulAction A W]
    (hB : IsPGroup 3 B) (hA : Nat.card A = 5) (hW : IsPGroup 2 W)
    (hfixedB : FixedPoints.subgroup B W = ⊥)
    (hfixedA : FixedPoints.subgroup A W ≠ ⊥) :
    4 ≤ Nat.card (FixedPoints.subgroup A W) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hW.exists_card_eq
  have hmod3 := hB.card_modEq_card_fixedPoints W
  change Nat.ModEq 3 (Nat.card W) (Nat.card (FixedPoints.subgroup B W)) at hmod3
  rw [hfixedB, Subgroup.card_bot, hn] at hmod3
  have hAp : IsPGroup 5 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hmod5 := hAp.card_modEq_card_fixedPoints W
  change Nat.ModEq 5 (Nat.card W) (Nat.card (FixedPoints.subgroup A W)) at hmod5
  have hne2 : Nat.card (FixedPoints.subgroup A W) ≠ 2 := by
    intro heq
    rw [hn, heq] at hmod5
    exact two_pow_mod_five_ne_two n hmod3 hmod5
  have hne1 : Nat.card (FixedPoints.subgroup A W) ≠ 1 :=
    fun h => hfixedA (Subgroup.card_eq_one.mp h)
  obtain ⟨m, hm⟩ := (hW.to_subgroup (FixedPoints.subgroup A W)).exists_card_eq
  have hm2 : 2 ≤ m := by
    by_contra h
    interval_cases m <;> simp_all
  calc
    4 = 2 ^ 2 := by decide
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hm2
    _ = Nat.card (FixedPoints.subgroup A W) := hm.symm

/-- A nonidentity five-fixed vector in the moving summand supplies the full
factor-four inequality. No complement or faithfulness assumption is needed
once that vector is supplied. -/
public theorem four_mul_card_fixed_le_of_moving_fixed
    {H V : Type*} [Group H] [Group V] [Finite V]
    [MulDistribMulAction H V] [IsElementaryAbelian 2 V]
    (B A : Subgroup H) [B.Normal] [Finite B] [IsElementaryAbelian 3 B]
    (hA : Nat.card A = 5)
    (hfixed : commutatorAction B V ⊓ FixedPoints.subgroup A V ≠ ⊥) :
    4 * Nat.card (FixedPoints.subgroup H V) ≤
      Nat.card (FixedPoints.subgroup A V) := by
  let W := commutatorAction B V
  let : IsInvariant A V W := commutatorAction_isInvariant_of_normalizing_actor
    A B (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  let : IsInvariant B V W := commutatorAction_isInvariant
  have hcop : Nat.Coprime (Nat.card B) (Nat.card V) := by
    obtain ⟨b, hb⟩ := (IsElementaryAbelian.isPGroup 3 B).exists_card_eq
    obtain ⟨v, hv⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hb, hv]
    exact ((by decide : Nat.Coprime 3 2).pow_left b).pow_right v
  have hcompl : IsCompl (FixedPoints.subgroup B V) W :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (Group.isSolvable_of_comm fun x y : V => mul_comm x y) hcop inferInstance
  have hfixedB : FixedPoints.subgroup B W = ⊥ := by
    apply Subgroup.map_injective W.subtype_injective
    rw [fixedPoints_subgroup_map_subtype_eq_inf, Subgroup.map_bot]
    simpa only [inf_comm] using hcompl.inf_eq_bot
  have hfixedA : FixedPoints.subgroup A W ≠ ⊥ := by
    intro h
    apply hfixed
    rw [← fixedPoints_subgroup_map_subtype_eq_inf W, h, Subgroup.map_bot]
  have hfour := four_le_card_fixed_of_three_fixed_eq_bot
    (IsElementaryAbelian.isPGroup 3 B) hA
    ((IsElementaryAbelian.isPGroup 2 V).to_subgroup W) hfixedB hfixedA
  let F := FixedPoints.subgroup H V
  let D := W ⊓ FixedPoints.subgroup A V
  have hDcard : Nat.card D = Nat.card (FixedPoints.subgroup A W) := by
    change Nat.card (W ⊓ FixedPoints.subgroup A V : Subgroup V) = _
    rw [← fixedPoints_subgroup_map_subtype_eq_inf W]
    exact Subgroup.card_map_of_injective W.subtype_injective
  have hdisj : Disjoint F D := hcompl.disjoint.mono
    (show F ≤ FixedPoints.subgroup B V from fun _ hx b => hx (b : H)) inf_le_left
  let f : F × D → FixedPoints.subgroup A V := fun x =>
    ⟨x.1.val * x.2.val, fun a => by
      rw [smul_mul', show a • x.1.val = x.1.val from x.1.property (a : H),
        x.2.property.2 a]⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subgroup.mul_injective_of_disjoint hdisj (congrArg Subtype.val h)
  have hbound := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, hDcard] at hbound
  simpa only [Nat.mul_comm] using (Nat.mul_le_mul_left (Nat.card F) hfour).trans hbound

/-- A fixed-free five-complement to a nontrivial elementary abelian
three-group acting faithfully on a binary group has at least four times
as many fixed points as the whole group. -/
public theorem four_mul_card_fixed_le
    {H V : Type*} [Group H] [Finite H] [Group V] [Finite V]
    [MulDistribMulAction H V] [IsElementaryAbelian 2 V]
    (B A : Subgroup H) [B.Normal] [IsElementaryAbelian 3 B]
    [FaithfulSMul B V]
    (hB : B ≠ ⊥) (hA : Nat.card A = 5)
    (hBA : B.IsComplement' A)
    (hfree : B ⊓ Subgroup.centralizer (A : Set H) = ⊥) :
    4 * Nat.card (FixedPoints.subgroup H V) ≤
      Nat.card (FixedPoints.subgroup A V) :=
  four_mul_card_fixed_le_of_moving_fixed B A hA
    (moving_fixed_ne_bot B A hB hA hBA hfree)

end ThreeFiveAction
