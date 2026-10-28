module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.Group

/-!
# The degree-28 action in Suzuki's unitary recognition theorem

This is the exact permutation-action input at q = 3: a normal regular subgroup
of a point stabilizer, with cyclic quotient of order eight. Regularity gives
an orbit bijection and a complement given by the two-point stabilizer. Hence
the root group, point stabilizer and group have orders 27, 216 and 6048.
No unitary recognition conclusion is assumed in this interface.

Source: M. Suzuki, *A characterization of the 3-dimensional projective unitary
group over a finite field of odd characteristic*, J. Algebra 2 (1965), pp. 1–2.
-/

namespace Stellmacher.Recognition

open MulAction

/-- Suzuki's three hypotheses at q = 3. Faithfulness is an ambient action
hypothesis when applying recognition; normality is recorded by `[Q.Normal]`. -/
public structure SuzukiThreeHypotheses
    (G Ω : Type*) [Group G] [MulAction G Ω]
    (a : Ω) (Q : Subgroup (stabilizer G a)) [Q.Normal] : Prop where
  degree : Nat.card Ω = 28
  doubly_transitive : IsMultiplyPretransitive G Ω 2
  regular : ∀ x y : Ω, x ≠ a → y ≠ a →
    ∃! q : Q, ((q : stabilizer G a) : G) • x = y
  quotient_cyclic : IsCyclic ((stabilizer G a) ⧸ Q)
  quotient_card : Nat.card ((stabilizer G a) ⧸ Q) = 8

/-- The local conclusions needed for the coordinate part of Suzuki's proof.
These are conclusions to be proved from `SuzukiThreeHypotheses`, not extra
assumptions in the recognition theorem. The torus exponent is -3 modulo 8. -/
public structure SuzukiThreeLocalStructure
    (G Ω : Type*) [Group G] [MulAction G Ω]
    (a b : Ω) (Q : Subgroup (stabilizer G a)) : Prop where
  root_cube : ∀ q : Q, q ^ 3 = 1
  root_noncommuting : ∃ x y : Q, x * y ≠ y * x
  root_center_card : Nat.card (Subgroup.center Q) = 3
  swap_exists : ∃ t : G, t ^ 2 = 1 ∧ t • a = b ∧ t • b = a ∧
    ∀ k : stabilizer (stabilizer G a) b,
      t⁻¹ * ((k : stabilizer G a) : G) * t = ((k : stabilizer G a) : G) ^ 5

namespace SuzukiThreeHypotheses

variable {G Ω : Type*} [Group G] [MulAction G Ω]
    {a : Ω} {Q : Subgroup (stabilizer G a)} [Q.Normal]
    (h : SuzukiThreeHypotheses G Ω a Q)

include h

/-- A faithful action of degree 28 has a finite acting group. -/
public theorem finite_group [FaithfulSMul G Ω] : Finite G := by
  let : Finite Ω := Nat.finite_of_card_ne_zero (by rw [h.degree]; decide)
  exact Finite.of_injective (MulAction.toPerm : G → Equiv.Perm Ω)
    MulAction.toPerm_injective

/-- The root group is in bijection with the complement of the base point. -/
public noncomputable def rootEquivComplement (b : Ω) (hb : b ≠ a) :
    Q ≃ {x : Ω // x ≠ a} := by
  let f : Q → {x : Ω // x ≠ a} := fun q =>
    ⟨((q : stabilizer G a) : G) • b, by
      intro he
      apply hb
      have hfix := (q : stabilizer G a).property
      rw [mem_stabilizer_iff] at hfix
      exact (MulAction.injective ((q : stabilizer G a) : G)) (he.trans hfix.symm)⟩
  apply Equiv.ofBijective f
  constructor
  · intro q r he
    obtain ⟨s, _, hs⟩ := h.regular b (f r) hb (f r).property
    exact (hs q (congrArg Subtype.val he)).trans (hs r rfl).symm
  · intro x
    obtain ⟨q, hq, _⟩ := h.regular b x hb x.property
    exact ⟨q, Subtype.ext hq⟩

/-- Evaluation of the root-coordinate bijection. -/
public theorem rootEquivComplement_apply (b : Ω) (hb : b ≠ a) (q : Q) :
    (h.rootEquivComplement b hb q : Ω) = ((q : stabilizer G a) : G) • b := by
  rfl

public theorem root_card : Nat.card Q = 27 := by
  classical
  let : Finite Ω := Nat.finite_of_card_ne_zero (by rw [h.degree]; decide)
  let : Fintype Ω := Fintype.ofFinite Ω
  have hcard : Fintype.card Ω = 28 := by simpa using h.degree
  have hcompl : Nat.card {x : Ω // x ≠ a} = 27 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq, hcard]
  have : Nonempty {x : Ω // x ≠ a} :=
    Nat.card_pos_iff.mp (by omega : 0 < Nat.card {x : Ω // x ≠ a}) |>.1
  obtain ⟨b, hb⟩ := ‹Nonempty {x : Ω // x ≠ a}›
  exact (Nat.card_congr (h.rootEquivComplement b hb)).trans hcompl

public theorem stabilizer_card : Nat.card (stabilizer G a) = 216 := by
  have hc := Q.card_mul_index
  rw [Q.index_eq_card, h.quotient_card, h.root_card] at hc
  omega

public theorem group_card : Nat.card G = 6048 := by
  let := h.doubly_transitive
  let : IsPretransitive G Ω := isPretransitive_of_is_two_pretransitive
  have hc := (stabilizer G a).card_mul_index
  rw [index_stabilizer_of_transitive, h.degree, h.stabilizer_card] at hc
  omega

/-- The two-point stabilizer inside the one-point stabilizer complements Q. -/
public theorem root_complement (b : Ω) (hb : b ≠ a) :
    Q.IsComplement' (stabilizer (stabilizer G a) b) := by
  rw [Subgroup.isComplement'_def, Subgroup.isComplement_iff_existsUnique_inv_mul_mem]
  intro g
  have hga : (g : G) • b ≠ a := by
    intro he
    apply hb
    exact (MulAction.injective (g : G))
      (he.trans (mem_stabilizer_iff.mp g.property).symm)
  obtain ⟨q, hq, huniq⟩ := h.regular b ((g : G) • b) hb hga
  refine ⟨q, ?_, ?_⟩
  · change (((q : stabilizer G a) : G)⁻¹ * (g : G)) • b = b
    rw [mul_smul, ← hq, inv_smul_smul]
  · intro r hr
    apply huniq r
    change (((r : stabilizer G a) : G)⁻¹ * (g : G)) • b = b at hr
    rw [mul_smul] at hr
    exact (inv_smul_eq_iff.mp hr).symm

/-- The quotient map identifies the two-point stabilizer with H/Q. -/
public noncomputable def twoPointEquivQuotient (b : Ω) (hb : b ≠ a) :
    stabilizer (stabilizer G a) b ≃* ((stabilizer G a) ⧸ Q) :=
  MulEquiv.ofBijective
    ((QuotientGroup.mk' Q).comp (stabilizer (stabilizer G a) b).subtype)
    (Subgroup.isComplement_subgroup_right_iff_bijective.mp
      (h.root_complement b hb).symm)

public theorem twoPoint_card (b : Ω) (hb : b ≠ a) :
    Nat.card (stabilizer (stabilizer G a) b) = 8 :=
  (Nat.card_congr (h.twoPointEquivQuotient b hb).toEquiv).trans h.quotient_card

public theorem twoPoint_cyclic (b : Ω) (hb : b ≠ a) :
    IsCyclic (stabilizer (stabilizer G a) b) :=
  (h.twoPointEquivQuotient b hb).isCyclic.mpr h.quotient_cyclic

/-- An involution exchanging any prescribed pair of distinct points exists.
Cauchy's theorem gives an involution; faithfulness gives a moved point and
double transitivity carries its two-cycle to the prescribed pair. -/
public theorem exists_swap [FaithfulSMul G Ω] (b : Ω) (hb : b ≠ a) :
    ∃ t : G, t ^ 2 = 1 ∧ t • a = b ∧ t • b = a := by
  classical
  let : Finite G := h.finite_group
  obtain ⟨j, hj⟩ := exists_prime_orderOf_dvd_card' 2
    (by rw [h.group_card]; decide : 2 ∣ Nat.card G)
  have hjpow : j ^ 2 = 1 := by rw [← hj]; exact pow_orderOf_eq_one j
  have hjne : j ≠ 1 := by
    intro he
    simp [he] at hj
  obtain ⟨x, hx⟩ : ∃ x : Ω, j • x ≠ x := by
    by_contra! he
    exact hjne (eq_of_smul_eq_smul (fun x => (he x).trans (one_smul G x).symm))
  obtain ⟨g, hgx, hgjx⟩ :=
    is_two_pretransitive_iff.mp h.doubly_transitive hx.symm hb.symm
  refine ⟨g * j * g⁻¹, ?_, ?_, ?_⟩
  · calc
      (g * j * g⁻¹) ^ 2 = g * j ^ 2 * g⁻¹ := by simp only [pow_two]; group
      _ = 1 := by rw [hjpow]; group
  · rw [mul_smul, mul_smul, ← hgx, inv_smul_smul, hgjx]
  · rw [mul_smul, mul_smul, ← hgjx, inv_smul_smul, ← mul_smul j j x,
      ← pow_two, hjpow, one_smul, hgx]

end SuzukiThreeHypotheses
end Stellmacher.Recognition
