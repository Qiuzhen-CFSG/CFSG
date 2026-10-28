module

public import Theory.Representation.HexacodeAction.CubicLocalModel.Orders.Intrinsic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

/-!
# The commutator residual in a central cubic extension of S₃

The preimage of A₃ has order nine, is abelian, and equals the two-residual.
A Sylow two-subgroup has order two. Its nonidentity element has fixed
subgroup of order three in the nine-group: an element fixed in the S₃
image must be trivial, and the central kernel is fixed pointwise.
The commutator homomorphism therefore has image of order three. This image
is already two-perfect and has trivial two-core. No splitting is assumed,
and the calculation does not require an exponent-three hypothesis.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1 and Lemma 13.2.2(3), printed pp.876–877, after quotienting
the lifted Klein four in the point stabilizer. The sole finite permutation
calculation is checked by the Lean kernel.
-/

public section

noncomputable section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Representation.Hexacode.CubicLocalModel.Orders.CentralCubicSymmetricFour

set_option synthInstance.maxSize 256 in
private theorem three_centralizer_involution :
    ∀ a b : Equiv.Perm (Fin 3), a ^ 9 = 1 → b ^ 2 = 1 → b ≠ 1 →
      a * b = b * a → a = 1 := by decide +kernel

variable {X : Type*} [Group X] [Finite X]

/-- In a central cubic extension of S₃, the commutator of the two-residual
with any Sylow two-subgroup has order three. -/
private theorem commutator_card_of_central_cubic_s3 (f : X →* Equiv.Perm (Fin 3))
    (hf : Function.Surjective f) (hk : Nat.card f.ker = 3)
    (hc : f.ker ≤ center X) (P : Sylow 2 X) :
    Nat.card (⁅pResidual 2 X, (P : Subgroup X)⁆ : Subgroup X) = 3 := by
  have hXcard : Nat.card X = 18 := by
    rw [card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv, hk]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  let s := Equiv.Perm.sign.comp f
  let N := s.ker
  have hs : Function.Surjective s := (Equiv.Perm.sign_surjective (α := Fin 3)).comp hf
  have hNquot : Nat.card (X ⧸ N) = 2 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective s hs).toEquiv]
    norm_num [Nat.card_eq_fintype_card]
  have hNcard : Nat.card N = 9 := by
    have hcount := N.card_mul_index
    change Nat.card N * Nat.card (X ⧸ N) = Nat.card X at hcount
    rw [hNquot, hXcard] at hcount
    omega
  have hres : pResidual 2 X = N := by
    apply le_antisymm
    · exact sInf_le ⟨inferInstance, IsPGroup.of_card (n := 1) (by simpa using hNquot)⟩
    · intro x hx
      apply mem_pResidual_of_orderOf_coprime
      have ho : orderOf x ∣ Nat.card N := by
        simpa only [Subgroup.orderOf_mk] using orderOf_dvd_natCard (⟨x, hx⟩ : N)
      exact (show Nat.Coprime 2 (Nat.card N) by rw [hNcard]; decide).of_dvd_right ho
  let : IsMulCommutative N := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
    (by simpa using hNcard)
  have hPcard : Nat.card (P : Subgroup X) = 2 := by
    rw [P.card_eq_multiplicity, hXcard]
    decide +kernel
  obtain ⟨t, ht, hall⟩ := (Nat.card_eq_two_iff' (1 : (P : Subgroup X))).mp hPcard
  have ht2 : (t : X) ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := t)
    rw [hPcard] at hh
    exact congrArg Subtype.val hh
  have hft : f t ≠ 1 := by
    intro he
    have htker : (t : X) ∈ f.ker := he
    have ht3 : (t : X) ^ 3 = 1 := by
      have hh := pow_card_eq_one' (x := (⟨t, htker⟩ : f.ker))
      rw [hk] at hh
      exact congrArg Subtype.val hh
    apply ht
    apply Subtype.ext
    change (t : X) = 1
    simpa only [pow_succ, ht2, one_mul] using ht3
  have hkerN : f.ker ≤ N := by
    intro x hx
    change Equiv.Perm.sign (f x) = 1
    rw [MonoidHom.mem_ker.mp hx, map_one]
  have hcN (x y : X) (hx : x ∈ N) (hy : y ∈ N) : x * y = y * x :=
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : N) ⟨y, hy⟩)
  have hcommN (x : N) : ⁅(x : X), (t : X)⁆ ∈ N :=
    (commutator_le_left N (P : Subgroup X)) (commutator_mem_commutator x.property t.property)
  let d : N →* X := {
    toFun x := ⁅(x : X), (t : X)⁆
    map_one' := by simp
    map_mul' x y := by
      change ⁅(x : X) * (y : X), (t : X)⁆ = ⁅(x : X), (t : X)⁆ * ⁅(y : X), (t : X)⁆
      rw [commutatorElement_mul_left_eq_conj_mul,
        hcN (x : X) ⁅(y : X), (t : X)⁆ x.property (hcommN y), mul_inv_cancel_right,
        hcN ⁅(y : X), (t : X)⁆ ⁅(x : X), (t : X)⁆ (hcommN y) (hcommN x)] }
  have hdker : d.ker = f.ker.subgroupOf N := by
    ext x
    change ⁅(x : X), (t : X)⁆ = 1 ↔ (x : X) ∈ f.ker
    rw [commutatorElement_eq_one_iff_mul_comm]
    constructor
    · intro hxt
      apply three_centralizer_involution (f x) (f t)
      · have hx9 : (x : X) ^ 9 = 1 := by
          have hh := pow_card_eq_one' (x := x)
          rw [hNcard] at hh
          exact congrArg Subtype.val hh
        rw [← map_pow, hx9, map_one]
      · rw [← map_pow, ht2, map_one]
      · exact hft
      · simpa only [map_mul] using congrArg f hxt
    · intro hx
      exact (mem_center_iff.mp (hc hx) t).symm
  have hdkerCard : Nat.card d.ker = 3 := by
    rw [hdker, Nat.card_congr (subgroupOfEquivOfLe hkerN).toEquiv, hk]
  have hdrange : Nat.card d.range = 3 := by
    have hh := d.ker.card_mul_index
    rw [index_ker, hdkerCard, hNcard] at hh
    omega
  have hcomm : (⁅N, (P : Subgroup X)⁆ : Subgroup X) = d.range := by
    apply le_antisymm
    · apply commutator_le.mpr
      intro x hx y hy
      by_cases hy1 : y = 1
      · simp only [hy1, commutatorElement_one_right]
        exact d.range.one_mem
      · have hyt : (⟨y, hy⟩ : (P : Subgroup X)) = t := hall _ (fun he => hy1 (congrArg Subtype.val he))
        have he : y = (t : X) := congrArg Subtype.val hyt
        rw [he]
        exact ⟨⟨x, hx⟩, rfl⟩
    · rintro x ⟨a, rfl⟩
      exact commutator_mem_commutator a.property t.property
  rw [hres, hcomm, hdrange]

/-- The intrinsic commutator residual modulo its two-core has order three
in every central cubic extension of S₃. -/
theorem intrinsicCommutatorResidual_quotient_card_of_central_cubic_s3
    (f : X →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (hk : Nat.card f.ker = 3) (hc : f.ker ≤ center X) (P : Sylow 2 X) :
    Nat.card (intrinsicCommutatorResidual P ⧸ pCore 2 (intrinsicCommutatorResidual P)) = 3 := by
  let C : Subgroup X := ⁅pResidual 2 X, (P : Subgroup X)⁆
  have hCcard : Nat.card C = 3 := commutator_card_of_central_cubic_s3 f hf hk hc P
  have hCres : pResidual 2 C = ⊤ := by
    apply top_unique
    intro x _
    apply mem_pResidual_of_orderOf_coprime
    exact (show Nat.Coprime 2 (Nat.card C) by rw [hCcard]; decide).of_dvd_right
      (orderOf_dvd_natCard x)
  have hRcard : Nat.card (intrinsicCommutatorResidual P) = 3 := by
    change Nat.card ((pResidual 2 C).map C.subtype) = 3
    rw [hCres, ← MonoidHom.range_eq_map, range_subtype, hCcard]
  let R := intrinsicCommutatorResidual P
  have hdiv : Nat.card (pCore 2 R) ∣ 3 := hRcard ▸ (pCore 2 R).card_subgroup_dvd_card
  have hcop : Nat.Coprime (Nat.card (pCore 2 R)) 3 := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := R)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  have hcoreCard : Nat.card (pCore 2 R) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) hdiv
  have hcount := (pCore 2 R).card_mul_index
  change Nat.card (pCore 2 R) * Nat.card (R ⧸ pCore 2 R) = Nat.card R at hcount
  rwa [hcoreCard, one_mul, hRcard] at hcount

end Representation.Hexacode.CubicLocalModel.Orders.CentralCubicSymmetricFour
