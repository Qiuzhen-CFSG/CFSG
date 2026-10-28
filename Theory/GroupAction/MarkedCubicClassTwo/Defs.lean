module

public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Theory.Frattini.PGroup
public import Mathlib.GroupTheory.Nilpotent

/-!
# Marked cubic generators and their literal quotients

Two cubic subgroups generate a finite group with an elementary Frattini
plane. Each marked subgroup meets the Frattini subgroup trivially, so every
quotient below Frattini retains its order and its separation from deeper
layers. The action input records two commuting square-one automorphisms
which invert opposite marked generators.

The cyclic-fixed-subgroup contract quantifies over automorphisms of the
literal quotient, with explicit compatibility on representatives. It is an
input to the class bound, not an assertion about arbitrary three-groups.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
Lemma F.6.16, printed p.308, combined manuscript of 1 March 2004.
-/

@[expose] public section

open Subgroup
namespace MarkedCubicClassTwo
variable {P : Type*} [Group P]

/-- The two specified cubic generators and their opposite involutory actions. -/
structure CubicMarking (A B : Subgroup P) (a b : MulAut P) : Prop where
  card_left : Nat.card A = 3
  card_right : Nat.card B = 3
  generate : A ⊔ B = ⊤
  left_sq : a ^ 2 = 1
  right_sq : b ^ 2 = 1
  commute : Commute a b
  left_inverts : ∀ x ∈ A, a x = x⁻¹
  left_fixes : ∀ x ∈ B, a x = x
  right_fixes : ∀ x ∈ A, b x = x
  right_inverts : ∀ x ∈ B, b x = x⁻¹

/-- Every compatible induced pair below Frattini has cyclic fixed subgroups.
An induced automorphism already entails invariance of the quotient kernel. -/
def QuotientCyclicFixed (a b : MulAut P) : Prop :=
  ∀ (N : Subgroup P) (_ : N.Normal), N ≤ frattini P →
    ∀ aN bN : MulAut (P ⧸ N),
      (∀ x, aN (QuotientGroup.mk' N x) = QuotientGroup.mk' N (a x)) →
      (∀ x, bN (QuotientGroup.mk' N x) = QuotientGroup.mk' N (b x)) →
      IsCyclic aN.fixedSubgroup ∧ IsCyclic bN.fixedSubgroup

variable [Finite P]

/-- Neither cubic marking disappears in a quotient below the Frattini plane. -/
theorem disjoint_frattini_of_cubic_generators
    (A B : Subgroup P) (hA : Nat.card A = 3) (hB : Nat.card B = 3)
    (hgen : A ⊔ B = ⊤) (hplane : Nat.card (P ⧸ frattini P) = 9) :
    Disjoint A (frattini P) := by
  let : Fact (Nat.card A).Prime := ⟨hA ▸ Nat.prime_three⟩
  rcases eq_bot_or_eq_top_of_prime_card ((frattini P).subgroupOf A) with hh | hh
  · apply disjoint_def.mpr
    intro x hxA hxF
    have hx : (⟨x, hxA⟩ : A) ∈ (frattini P).subgroupOf A := hxF
    rw [hh] at hx
    exact congrArg Subtype.val (mem_bot.mp hx)
  · have hAF : A ≤ frattini P := by
      intro x hx
      exact show (⟨x, hx⟩ : A) ∈ (frattini P).subgroupOf A from hh ▸ mem_top _
    have hBF : B ⊔ frattini P = ⊤ := by
      apply top_unique
      rw [← hgen]
      exact sup_le (hAF.trans le_sup_right) le_sup_left
    have hBtop : B = ⊤ := frattini_nongenerating hBF
    have hcP : Nat.card P = 3 := by simpa only [hBtop, Nat.card_congr Subgroup.topEquiv.toEquiv] using hB
    have hdiv := card_dvd_of_surjective (QuotientGroup.mk' (frattini P))
      (QuotientGroup.mk'_surjective (frattini P))
    rw [hplane, hcP] at hdiv
    norm_num at hdiv

omit [Finite P] in
/-- A marked subgroup disjoint from the kernel retains its order. -/
theorem quotient_marked_card (A N : Subgroup P) [N.Normal]
    (hd : Disjoint A N) : Nat.card (A.map (QuotientGroup.mk' N)) = Nat.card A := by
  let f := (QuotientGroup.mk' N).subgroupMap A
  have hi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_iff.mpr
    intro x hx
    apply mem_bot.mpr
    apply Subtype.ext
    exact disjoint_def.mp hd x.property
      ((QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val (MonoidHom.mem_ker.mp hx)))
  exact (Nat.card_congr (MulEquiv.ofBijective f ⟨hi, (QuotientGroup.mk' N).subgroupMap_surjective A⟩).toEquiv).symm

omit [Finite P] in
/-- Separation from a layer survives quotienting by a subgroup of that layer. -/
theorem quotient_marked_disjoint (A V N : Subgroup P) [N.Normal]
    (hd : Disjoint A V) (hNV : N ≤ V) :
    Disjoint (A.map (QuotientGroup.mk' N)) (V.map (QuotientGroup.mk' N)) := by
  apply disjoint_def.mpr
  rintro x ⟨u, hu, rfl⟩ ⟨v, hv, hvu⟩
  have hdiff : v⁻¹ * u ∈ N := QuotientGroup.eq.mp hvu
  have huV : u ∈ V := by
    simpa only [mul_inv_cancel_left] using V.mul_mem hv (hNV hdiff)
  rw [disjoint_def.mp hd hu huV, map_one]


omit [Finite P] in
/-- Quotient transport retains both marked inclusions and all action equations. -/
theorem CubicMarking.quotient {A B : Subgroup P} {a b : MulAut P}
    (h : CubicMarking A B a b) (N : Subgroup P) [N.Normal]
    (hAN : Disjoint A N) (hBN : Disjoint B N)
    (aN bN : MulAut (P ⧸ N))
    (haN : ∀ x, aN (QuotientGroup.mk' N x) = QuotientGroup.mk' N (a x))
    (hbN : ∀ x, bN (QuotientGroup.mk' N x) = QuotientGroup.mk' N (b x)) :
    CubicMarking (A.map (QuotientGroup.mk' N)) (B.map (QuotientGroup.mk' N)) aN bN where
  card_left := (quotient_marked_card A N hAN).trans h.card_left
  card_right := (quotient_marked_card B N hBN).trans h.card_right
  generate := by
    rw [← Subgroup.map_sup, h.generate, map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  left_sq := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    change aN (aN (QuotientGroup.mk' N y)) = QuotientGroup.mk' N y
    rw [haN, haN, show a (a y) = y from DFunLike.congr_fun h.left_sq y]
  right_sq := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    change bN (bN (QuotientGroup.mk' N y)) = QuotientGroup.mk' N y
    rw [hbN, hbN, show b (b y) = y from DFunLike.congr_fun h.right_sq y]
  commute := by
    apply MulEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    change aN (bN (QuotientGroup.mk' N y)) = bN (aN (QuotientGroup.mk' N y))
    rw [hbN, haN, haN, hbN, show a (b y) = b (a y) from DFunLike.congr_fun h.commute.eq y]
  left_inverts := by
    rintro _ ⟨x, hx, rfl⟩
    rw [haN, h.left_inverts x hx, map_inv]
  left_fixes := by
    rintro _ ⟨x, hx, rfl⟩
    rw [haN, h.left_fixes x hx]
  right_fixes := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hbN, h.right_fixes x hx]
  right_inverts := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hbN, h.right_inverts x hx, map_inv]

end MarkedCubicClassTwo
