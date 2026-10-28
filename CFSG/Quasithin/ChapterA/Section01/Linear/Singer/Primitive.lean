module

public import CFSG.Quasithin.ChapterA.Section01.Linear.Singer.Defs
public import Theory.LinearAlgebra.RegularPrimitiveSubgroup
public import Theory.GroupTheory.PrimeCyclicCentralizer

/-!
# The primitive-prime branch of the Singer-overgroup lemma

For a cyclic group X regular on the nonzero vectors of a binary space V,
a prime r with binary order dim(V) divides |X|. Its order-r subgroup R is
irreducible, and its full linear centralizer is X. The cyclic-centralizer
argument gives cyclic r-Sylow subgroups in the overgroup Y.

The shared fixed-vector input makes R centralize every other prime core
of Y. It also centralizes the r-core by cyclicity of the Sylow subgroups.
Fitting self-centralization puts R in the cyclic r-core; hence R and its
centralizer in Y are normal. That centralizer is exactly X inside Y.

This proves the conditional primitive-prime contract for Aschbacher–Smith,
*The Classification of Quasithin Groups*, A.1.12, printed p.22. The earlier
fixed-vector theorem remains an explicit shared premise here; the parent
A.1.12 assembly supplies it and the primitive prime.
-/

namespace CFSG.Quasithin.ChapterA.Singer
open Subgroup
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The primitive-prime branch of A.1.12, conditional only on the shared
fixed-vector theorem in addition to the stated group and prime hypotheses. -/
public theorem normal_of_primitive_prime (X Y : Subgroup (V ≃ₗ[ZMod 2] V))
    (hcyc : IsCyclic X) (hreg : LinearGroup.IsRegularOnNonzero X)
    (hXY : X ≤ Y) (_hodd : Odd (Nat.card Y)) (hsolv : Group.IsSolvable Y)
    (hn : 1 < Module.finrank (ZMod 2) V) {r : ℕ} (hr : r.Prime)
    (hord : orderOf (2 : ZMod r) = Module.finrank (ZMod 2) V)
    (hfp : PrimeFixedPointCentralization Y) : (X.subgroupOf Y).Normal := by
  classical
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun g : V ≃ₗ[ZMod 2] V => (g : V → V)) DFunLike.coe_injective
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (lt_trans Nat.zero_lt_one hn)
  let : IsCyclic X := hcyc
  let : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    have hz : orderOf (2 : ZMod 2) = 0 := by
      rw [show (2 : ZMod 2) = 0 from rfl, orderOf_zero]
    omega
  have hXcard : Nat.card X = 2 ^ Module.finrank (ZMod 2) V - 1 := by
    simpa only [Nat.card_zmod] using hreg.card_eq_pow_finrank_sub_one
  have hrdiv : r ∣ Nat.card X := by
    rw [hXcard]
    apply (ZMod.natCast_eq_zero_iff _ r).mp
    have hle : 1 ≤ 2 ^ Module.finrank (ZMod 2) V := Nat.one_le_pow _ _ (by decide)
    rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, ← hord,
      pow_orderOf_eq_one, sub_self]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) r hrdiv
  let R : Subgroup (V ≃ₗ[ZMod 2] V) := (zpowers x).map X.subtype
  have hRX : R ≤ X := map_subtype_le _
  have hR : Nat.card R = r := by
    rw [card_map_of_injective X.subtype_injective, Nat.card_zpowers, hx]
  have hC : centralizer (R : Set (V ≃ₗ[ZMod 2] V)) = X :=
    hreg.centralizer_eq_of_irreducible_subgroup hRX (by omega)
      (hreg.primitive_subgroup_invariant_eq_bot_or_top hRX hr hr2 hR hord)
  have hRY : R ≤ Y := hRX.trans hXY
  let Q := R.subgroupOf Y
  have hQ : Nat.card Q = r :=
    (Nat.card_congr (subgroupOfEquivOfLe hRY).toEquiv).trans hR
  have hCQ : centralizer (Q : Set Y) = X.subgroupOf Y := by
    ext y
    constructor
    · intro hy
      change (y : V ≃ₗ[ZMod 2] V) ∈ X
      rw [← hC]
      intro a ha
      exact congrArg (fun z : Y => (z : V ≃ₗ[ZMod 2] V))
        (hy ⟨a, hRY ha⟩ ha)
    · intro hy a ha
      apply Subtype.ext
      have hy' : (y : V ≃ₗ[ZMod 2] V) ∈ centralizer (R : Set _) := by
        rw [hC]
        exact hy
      exact hy' a.val ha
  let : IsCyclic (X.subgroupOf Y) :=
    isCyclic_of_injective (subgroupOfEquivOfLe hXY).toMonoidHom
      (subgroupOfEquivOfLe hXY).injective
  let : IsCyclic (centralizer (Q : Set Y)) := by
    rw [hCQ]
    infer_instance
  have hother : ∀ q : ℕ, q.Prime → q ≠ r → Q ≤ centralizer (pCore q Y : Set Y) := by
    intro q hq hqr a ha
    by_cases ha1 : a = 1
    · rw [ha1]
      exact (centralizer (pCore q Y : Set Y)).one_mem
    let aq : Q := ⟨a, ha⟩
    have haq : orderOf aq = r := by
      have hd := _root_.orderOf_dvd_natCard aq
      rw [hQ] at hd
      rcases (Nat.dvd_prime hr).mp hd with he | he
      · exact (ha1 (congrArg Subtype.val (orderOf_eq_one_iff.mp he))).elim
      · exact he
    have har : orderOf a = r := (orderOf_injective Q.subtype Q.subtype_injective aq).trans haq
    have hafree : ∀ v : V, (a : V ≃ₗ[ZMod 2] V) v = v → v = 0 := by
      intro v hav
      by_contra hv
      have hax : (⟨a.val, hRX ha⟩ : X) = 1 := hreg.eq_one_of_apply_eq_self _ hv hav
      apply ha1
      apply Subtype.ext
      exact congrArg (fun z : X => (z : V ≃ₗ[ZMod 2] V)) hax
    let : Fact q.Prime := ⟨hq⟩
    intro b hb
    exact (hfp q r hq hr hqr (pCore q Y) inferInstance pCore_isPGroup
      a har hafree ⟨b, hb⟩).symm.eq
  let : Q.Normal := prime_normal_of_cyclic_centralizer_of_other_cores hsolv Q hQ hother
  rw [← hCQ]
  infer_instance
end CFSG.Quasithin.ChapterA.Singer
