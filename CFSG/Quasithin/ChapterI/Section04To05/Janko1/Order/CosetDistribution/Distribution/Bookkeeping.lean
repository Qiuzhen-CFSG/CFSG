module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Setup
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Inversion fibers and singleton orbits in Bender's count

For an involution `u` outside `H`, multiplication by `u` identifies the
involutions in `Hu` with the elements of `H` inverted by `u`. Grouping the
actual involutions by their quotient fibers gives `|Jₙ| = n bₙ`.

Conjugation by `H` preserves singleton fibers and the condition that their
involution has trivial centralizer in `H`. This action has trivial
stabilizers, so the orbit decomposition proves `b₁ = c + |H| m` for a
natural number `m`. No distribution or counting premise is used.

Source: H. Bender, *Finite groups with large subgroups*, Illinois J. Math.
18 (1974), §2, printed p.223, applied to the §4 count on pp.226–227.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G]

/-- The literal elements of `H` inverted by `u`; closure is not assumed. -/
@[expose] public def BenderInverted (H : Subgroup G) (u : G) :=
  {a : H // u * (a : G) * u⁻¹ = (a : G)⁻¹}

/-- Multiplication by an outside involution identifies its fiber with
exactly those elements of `H` which it inverts. -/
public noncomputable def benderFiberEquivInverted (H : Subgroup G) (u : G)
    (hu : orderOf u = 2) (huH : u ∉ H) :
    BenderFiber H (benderRightCoset H u) ≃ BenderInverted H u := by
  have hu2 : u * u = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hu).1
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  refine {
    toFun := fun t => ⟨⟨t.1 * u, ?_⟩, ?_⟩
    invFun := fun a => ⟨(a.1 : G) * u, ?_, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have ht := t.2.2
    simpa only [benderRightCoset, QuotientGroup.eq, inv_inv, huinv] using ht
  · change u * (t.1 * u) * u⁻¹ = (t.1 * u)⁻¹
    have htinv : t.1⁻¹ = t.1 :=
      inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using (orderOf_eq_prime_iff.mp t.2.1).1)
    simp only [mul_inv_rev, huinv, htinv]
    calc
      u * (t.1 * u) * u = u * t.1 * (u * u) := by group
      _ = u * t.1 := by rw [hu2, mul_one]
  · rcases a with ⟨⟨a, haH⟩, ha⟩
    apply orderOf_eq_prime_iff.mpr
    constructor
    · change u * a * u⁻¹ = a⁻¹ at ha
      rw [huinv] at ha
      calc
        (a * u) ^ 2 = a * (u * a * u) := by simp only [pow_two, mul_assoc]
        _ = 1 := by rw [ha, mul_inv_cancel]
    · intro he
      apply huH
      have hueq : u = a⁻¹ := by
        calc
          u = a⁻¹ * (a * u) := by group
          _ = a⁻¹ := by rw [he, mul_one]
      rw [hueq]
      exact H.inv_mem haH
  · change (QuotientGroup.mk (((a.1 : G) * u)⁻¹) : G ⧸ H) = QuotientGroup.mk u⁻¹
    rw [QuotientGroup.eq, inv_inv, mul_inv_cancel_right]
    exact a.1.property
  · intro t
    apply Subtype.ext
    change t.1 * u * u = t.1
    rw [mul_assoc, hu2, mul_one]
  · intro a
    apply Subtype.ext; apply Subtype.ext
    change (a.1 : G) * u * u = (a.1 : G)
    rw [mul_assoc, hu2, mul_one]

/-- A subgroup description of the inverted elements gives the actual fiber size. -/
public theorem bender_fiber_card_of_inverted_subgroup (H : Subgroup G) (u : G)
    (hu : orderOf u = 2) (huH : u ∉ H) (K : Subgroup G)
    (hK : ∀ a : G, a ∈ K ↔ a ∈ H ∧ u * a * u⁻¹ = a⁻¹) :
    Nat.card (BenderFiber H (benderRightCoset H u)) = Nat.card K := by
  let e : BenderInverted H u ≃ K :=
    { toFun := fun a => ⟨a.1.1, (hK _).mpr ⟨a.1.2, a.2⟩⟩
      invFun := fun a => ⟨⟨a.1, ((hK _).mp a.2).1⟩, ((hK _).mp a.2).2⟩
      left_inv := by intro a; rfl
      right_inv := by intro a; rfl }
  exact Nat.card_congr ((benderFiberEquivInverted H u hu huH).trans e)

end CFSG.Quasithin.Janko1CentralizerData

open Subgroup MulAction
namespace CFSG.Quasithin.Janko1CentralizerData

variable {G : Type*} [Group G]

/-- The actual involutions in non-base fibers of a specified size. -/
@[expose] public def BenderInvolutionsInFibers (H : Subgroup G) (n : ℕ) :=
  {u : G // orderOf u = 2 ∧ benderRightCoset H u ≠ benderBaseCoset H ∧
    Nat.card (BenderFiber H (benderRightCoset H u)) = n}

/-- Equality of right cosets as an internal subgroup-membership test. -/
public theorem benderRightCoset_eq_iff_mul_inv_mem (H : Subgroup G) (x y : G) :
    benderRightCoset H x = benderRightCoset H y ↔ x * y⁻¹ ∈ H := by
  simp only [benderRightCoset, QuotientGroup.eq, inv_inv]

private theorem conj_mem_iff (H : Subgroup G) (a : H) (x : G) :
    (MulAut.conj (a : G)) x ∈ H ↔ x ∈ H := by
  change (a : G) * x * (a : G)⁻¹ ∈ H ↔ x ∈ H
  rw [H.mul_mem_cancel_right (H.inv_mem a.property), H.mul_mem_cancel_left a.property]

private theorem same_coset_conj_iff (H : Subgroup G) (a : H) (x y : G) :
    benderRightCoset H ((MulAut.conj (a : G)) x) =
        benderRightCoset H ((MulAut.conj (a : G)) y) ↔
      benderRightCoset H x = benderRightCoset H y := by
  rw [benderRightCoset_eq_iff_mul_inv_mem, benderRightCoset_eq_iff_mul_inv_mem,
    ← map_inv, ← map_mul, conj_mem_iff]

private noncomputable def fiberConjEquiv (H : Subgroup G) (a : H) (u : G) :
    BenderFiber H (benderRightCoset H u) ≃
      BenderFiber H (benderRightCoset H ((MulAut.conj (a : G)) u)) :=
  (MulAut.conj (a : G)).toEquiv.subtypeEquiv (fun x => by
    change (orderOf x = 2 ∧ benderRightCoset H x = benderRightCoset H u) ↔
      (orderOf ((MulAut.conj (a : G)) x) = 2 ∧
      benderRightCoset H ((MulAut.conj (a : G)) x) =
        benderRightCoset H ((MulAut.conj (a : G)) u))
    rw [(MulAut.conj (a : G)).orderOf_eq, same_coset_conj_iff])

private theorem involutionsInFibers_conj (H : Subgroup G) (n : ℕ)
    (a : H) (u : BenderInvolutionsInFibers H n) :
    orderOf ((MulAut.conj (a : G)) u.1) = 2 ∧
      benderRightCoset H ((MulAut.conj (a : G)) u.1) ≠ benderBaseCoset H ∧
      Nat.card (BenderFiber H (benderRightCoset H ((MulAut.conj (a : G)) u.1))) = n := by
  refine ⟨((MulAut.conj (a : G)).orderOf_eq u.1).trans u.2.1, ?_, ?_⟩
  · intro he
    apply u.2.2.1
    apply (benderRightCoset_eq_base_iff H u.1).mpr
    exact (conj_mem_iff H a u.1).mp
      ((benderRightCoset_eq_base_iff H _).mp he)
  · exact (Nat.card_congr (fiberConjEquiv H a u.1)).symm.trans u.2.2.2

/-- Counting involutions by their actual fibers gives `|Jₙ| = n bₙ`. -/
public theorem bender_involutionsInFibers_card [Finite G] (H : Subgroup G) (n : ℕ) :
    Nat.card (BenderInvolutionsInFibers H n) = n * benderCosetCount H n := by
  classical
  let Ω := {ω : G ⧸ H // ω ≠ benderBaseCoset H ∧ Nat.card (BenderFiber H ω) = n}
  let _ : Fintype Ω := Fintype.ofFinite _
  have : ∀ ω : Ω, Finite (BenderFiber H ω) := fun ω => by
    unfold BenderFiber
    infer_instance
  let e : BenderInvolutionsInFibers H n ≃ Σ ω : Ω, BenderFiber H ω :=
    { toFun := fun u => ⟨⟨benderRightCoset H u.1, u.2.2⟩, ⟨u.1, u.2.1, rfl⟩⟩
      invFun := fun u => ⟨u.2.1, u.2.2.1, u.2.2.2.symm ▸ u.1.2⟩
      left_inv := by intro u; rfl
      right_inv := by
        rintro ⟨⟨ω, hω⟩, u, hu, he⟩
        change benderRightCoset H u = ω at he
        subst ω
        rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  simp only [show ∀ ω : Ω, Nat.card (BenderFiber H ω) = n from fun ω => ω.2.2]
  simp [benderCosetCount, Ω, Nat.mul_comm]

/-- The number of singleton fibers consists of centralized singletons and
free conjugation orbits, each with exactly `|H|` elements. -/
public theorem bender_single_cosets [Finite G] (H : Subgroup G) :
    ∃ m : ℕ, benderCosetCount H 1 = Nat.card (BenderCentralizedSingletons H) +
      Nat.card H * m := by
  classical
  let J := BenderInvolutionsInFibers H 1
  let p : J → Prop := fun u => ∃ a ∈ H, a ≠ 1 ∧ Commute a u.1
  let F := {u : J // ¬ p u}
  have : Finite J := by unfold J BenderInvolutionsInFibers; infer_instance
  let ec : {u : J // p u} ≃ BenderCentralizedSingletons H :=
    { toFun := fun u => ⟨u.1.1, u.1.2.1, u.1.2.2.1, u.1.2.2.2, u.2⟩
      invFun := fun u => ⟨⟨u.1, u.2.1, u.2.2.1, u.2.2.2.1⟩, u.2.2.2.2⟩
      left_inv := by intro u; rfl
      right_inv := by intro u; rfl }
  have hp (a : H) (u : J) (hu : ¬ p u) :
      ¬ p ⟨(MulAut.conj (a : G)) u.1, involutionsInFibers_conj H 1 a u⟩ := by
    rintro ⟨b, hb, hb1, hbu⟩
    let c := (MulAut.conj (a : G)).symm b
    have hcH : c ∈ H := by
      apply (conj_mem_iff H a c).mp
      simpa only [c, MulEquiv.apply_symm_apply] using hb
    have hc1 : c ≠ 1 := by
      intro he
      apply hb1
      rw [← (MulAut.conj (a : G)).apply_symm_apply b]
      change (MulAut.conj (a : G)) c = 1
      rw [he, map_one]
    have hcu : Commute c u.1 := by
      apply (MulAut.conj (a : G)).injective
      simpa only [map_mul, c, MulEquiv.apply_symm_apply] using hbu.eq
    exact hu ⟨c, hcH, hc1, hcu⟩
  let _ : MulAction H F := {
    smul a u := ⟨⟨(MulAut.conj (a : G)) u.1.1,
      involutionsInFibers_conj H 1 a u.1⟩, hp a u.1 u.2⟩
    one_smul u := by
      apply Subtype.ext; apply Subtype.ext
      change (1 : G) * u.1.1 * (1 : G)⁻¹ = u.1.1
      simp
    mul_smul a b u := by
      apply Subtype.ext; apply Subtype.ext
      change ((a : G) * (b : G)) * u.1.1 * ((a : G) * (b : G))⁻¹ =
        (a : G) * ((b : G) * u.1.1 * (b : G)⁻¹) * (a : G)⁻¹
      group }
  have hstab (u : F) : stabilizer H u = ⊥ := by
    apply eq_bot_iff.mpr
    intro a ha
    apply mem_bot.mpr
    by_contra hne
    apply u.2
    have he := congrArg (fun v : F => v.1.1) ha
    change (a : G) * u.1.1 * (a : G)⁻¹ = u.1.1 at he
    exact ⟨a, a.property, fun h1 => hne (Subtype.ext h1),
      mul_inv_eq_iff_eq_mul.mp he⟩
  have hfree := Nat.card_congr (selfEquivOrbitsQuotientProd hstab)
  rw [Nat.card_prod] at hfree
  have hsplit := Nat.card_congr (Equiv.sumCompl p).symm
  rw [Nat.card_sum, Nat.card_congr ec, hfree] at hsplit
  refine ⟨Nat.card (Quotient (orbitRel H F)), ?_⟩
  have hJ := bender_involutionsInFibers_card H 1
  simpa only [one_mul, J, Nat.mul_comm] using hJ.symm.trans hsplit

end CFSG.Quasithin.Janko1CentralizerData
