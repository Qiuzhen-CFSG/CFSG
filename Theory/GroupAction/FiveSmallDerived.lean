module
public import Theory.GroupAction.FiveActionMinimalOrder
public import Theory.GroupAction.CoprimeFixedCardinality
public import Theory.GroupAction.CoprimeSmallQuotient
public import Theory.GroupAction.CoprimeHall
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Mathlib.GroupTheory.Frattini
import Mathlib.Tactic

/-!
# Small derived subgroups under an order-five action

Orbit counting shows that a nontrivial five-action on a finite two-group
has fixed-subgroup index at least sixteen. Coprime fixed-point lifting
multiplies this estimate across an invariant normal subgroup and its
quotient. Two moving layers in a group of order 1024 therefore leave at
most four fixed elements.

If the derived subgroup has order at most sixteen, it is central. When
the five-action on it is nontrivial, its order is sixteen and it has no
proper nontrivial invariant subgroup; its nontrivial intersection with
the ambient center is consequently the whole derived subgroup. Otherwise
the derived subgroup lies in the fixed subgroup, which is abelian of order
at most four. Both the fixed subgroup and the coprime commutator centralize
it, and together they generate the group.

This is the coprime-action argument in Fong--Seitz I (5H), printed p.30.
The literal root-section application is in
`SourceBinary.HexagonStructure.SmallSuzukiClassTwo`.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupAction

/-- A moving five-action has fixed-subgroup index at least sixteen. -/
theorem sixteen_mul_fixed_card_le_of_five_action
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [MulDistribMulAction A V] (hA : Nat.card A = 5) (hV : IsPGroup 2 V)
    (hmove : FixedPoints.subgroup A V ≠ ⊤) :
    16 * Nat.card (FixedPoints.subgroup A V) ≤ Nat.card V := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let C := FixedPoints.subgroup A V
  have hfive : IsPGroup 5 A := IsPGroup.of_card (p := 5) (n := 1) (by simpa using hA)
  have hm := hfive.card_modEq_card_fixedPoints V
  change Nat.ModEq 5 (Nat.card V) (Nat.card C) at hm
  obtain ⟨k,hk⟩ := (hV.to_subgroup C).exists_card_eq
  have hcop : Nat.Coprime 5 (Nat.card C) := by
    rw [hk]
    exact (by decide : Nat.Coprime 5 2).pow_right k
  have hi : Nat.ModEq 5 C.index 1 := Nat.ModEq.cancel_left_of_coprime hcop
    (by simpa only [C.card_mul_index,mul_one] using hm)
  obtain ⟨n,hn⟩ := hV.exists_card_eq
  obtain ⟨m,hmn,hidx⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show C.index ∣ 2^n from hn ▸ C.index_dvd_card)
  have h16 : 16 ≤ C.index := by
    by_contra hb
    have hmlt : m < 4 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
      (by simpa only [hidx] using Nat.lt_of_not_ge hb)
    rw [hidx] at hi
    interval_cases m
    · have he : C = ⊤ := C.index_eq_one.mp (by simpa using hidx)
      exact hmove he
    · norm_num [Nat.ModEq] at hi
    · norm_num [Nat.ModEq] at hi
    · norm_num [Nat.ModEq] at hi
  calc
    16 * Nat.card C ≤ C.index * Nat.card C := Nat.mul_le_mul_right _ h16
    _ = Nat.card V := C.index_mul_card

/-- Two moving layers in a two-group of order 1024 leave at most four fixed elements. -/
theorem fixed_card_le_four_of_two_five_layers
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [MulDistribMulAction A V] (hA : Nat.card A = 5) (hV : IsPGroup 2 V)
    (hcard : Nat.card V = 1024)
    (N : Subgroup V) [N.Normal] [IsInvariant A V N]
    (hN : FixedPoints.subgroup A N ≠ ⊤)
    (hQ : letI : MulDistribMulAction A (V ⧸ N) := quotientMulDistribMulAction N inferInstance
      FixedPoints.subgroup A (V ⧸ N) ≠ ⊤) :
    Nat.card (FixedPoints.subgroup A V) ≤ 4 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Group.IsNilpotent V := hV.isNilpotent
  let : MulDistribMulAction A (V ⧸ N) := quotientMulDistribMulAction N inferInstance
  have hcop : Nat.Coprime (Nat.card A) (Nat.card V) := by rw [hA,hcard]; decide
  have hF := FixedPoints.card_eq_quotient_mul_kernel_of_coprime
    (inferInstance : Group.IsSolvable V) hcop N inferInstance
  have he : Nat.card (FixedPoints.subgroup A N) =
      Nat.card (N ⊓ FixedPoints.subgroup A V : Subgroup V) := by
    let e : FixedPoints.subgroup A N ≃ ↥(N ⊓ FixedPoints.subgroup A V) :=
      { toFun := fun x => ⟨x.val, x.val.property, fun a => congrArg Subtype.val (x.property a)⟩
        invFun := fun x => ⟨⟨x.val,x.property.1⟩,fun a => Subtype.ext (x.property.2 a)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact Nat.card_congr e
  have h1 := sixteen_mul_fixed_card_le_of_five_action hA (hV.to_subgroup N) hN
  have h2 := sixteen_mul_fixed_card_le_of_five_action hA (hV.to_quotient N) hQ
  have hh := Nat.mul_le_mul h1 h2
  rw [he] at hh
  have hmul : Nat.card N * Nat.card (V ⧸ N) = 1024 := N.card_mul_index.trans hcard
  nlinarith

/-- A derived subgroup of order at most sixteen is central if the five-fixed subgroup has order at most four. -/
theorem derived_central_of_small_five_fixed_subgroup
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [MulDistribMulAction A V] (hA : Nat.card A = 5) (hV : IsPGroup 2 V)
    (hfixed : Nat.card (FixedPoints.subgroup A V) ≤ 4)
    (hderived : Nat.card (commutator V) ≤ 16) : commutator V ≤ center V := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (IsPGroup 2 V) := ⟨hV⟩
  let : Group.IsNilpotent V := hV.isNilpotent
  let D := commutator V
  let C := FixedPoints.subgroup A V
  let : IsInvariant A V D := isInvariant_of_characteristic D
  have hcop : Nat.Coprime (Nat.card A) (Nat.card V) := by
    obtain ⟨n,hn⟩ := hV.exists_card_eq
    rw [hA,hn]
    exact (by decide : Nat.Coprime 5 2).pow_right n
  by_cases htriv : FixedPoints.subgroup A D = ⊤
  · have hDC : D ≤ C := by
      intro d hd a
      exact congrArg Subtype.val (show a • (⟨d,hd⟩ : D) = ⟨d,hd⟩ from
        (show (⟨d,hd⟩ : D) ∈ FixedPoints.subgroup A D from htriv ▸ mem_top _) a)
    have hcommC : IsMulCommutative C := by
      obtain ⟨n,hn⟩ := (hV.to_subgroup C).exists_card_eq
      have hn2 : n ≤ 2 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
        (by change Nat.card C ≤ 4 at hfixed; simpa only [hn] using hfixed)
      interval_cases n
      · let : Subsingleton C := Finite.card_le_one_iff_subsingleton.mp (by omega)
        exact ⟨⟨fun _ _ => Subsingleton.elim _ _⟩⟩
      · let : IsCyclic C := isCyclic_of_prime_card (p := 2) (by simpa using hn)
        infer_instance
      · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hn
    let : IsMulCommutative C := hcommC
    have hCZ : C ≤ centralizer (D : Set V) := by
      intro c hc d hd
      exact congrArg Subtype.val (mul_comm (⟨d,hDC hd⟩ : C) ⟨c,hc⟩)
    have hMZ := commutatorAction_le_centralizer_of_fixed_normal D
      (fun a d hd => hDC hd a)
    have htop : (⊤ : Subgroup V) ≤ centralizer (D : Set V) := by
      rw [←fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
        (inferInstance : Group.IsSolvable V) hcop]
      exact sup_le hCZ hMZ
    intro d hd
    exact mem_center_iff.mpr (fun v => ((htop (mem_top v)) d hd).symm)
  · have hD16 : Nat.card D = 16 := le_antisymm hderived
      (sixteen_le_card_of_five_action_nontrivial hA (hV.to_subgroup D) htriv)
    have hfree := fixed_eq_bot_of_five_action_card_sixteen hA hD16 htriv
    let : Nontrivial D := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨z,hzne,hz⟩ := exists_nontrivial_center_mem_normal D (p := 2)
    let ZD := D ⊓ center V
    let : IsInvariant A V (center V) := isInvariant_of_characteristic _
    let : IsInvariant A V ZD := isInvariant_inf D (center V)
    have hZmove : FixedPoints.subgroup A ZD ≠ ⊤ := by
      intro he
      have hzf : z ∈ FixedPoints.subgroup A D := by
        intro a
        apply Subtype.ext
        exact congrArg (fun x : ZD => (x : V)) (show a • (⟨z,z.property,hz⟩ : ZD) = ⟨z,z.property,hz⟩ from
          (show (⟨z,z.property,hz⟩ : ZD) ∈ FixedPoints.subgroup A ZD from he ▸ mem_top _) a)
      exact hzne (mem_bot.mp (hfree ▸ hzf))
    have hZ16 := sixteen_le_card_of_five_action_nontrivial hA (hV.to_subgroup ZD) hZmove
    have he : ZD = D := eq_of_le_of_card_ge inf_le_left (by omega)
    change D ≤ center V
    rw [←he]
    exact inf_le_right

end Theory.GroupAction
