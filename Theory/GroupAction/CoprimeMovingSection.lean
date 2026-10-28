module

public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.Lemmas
public import Theory.GroupAction.RegularNonidentityOrbit
public import Theory.GroupTheory.NormalizedSupCard
import Mathlib.Tactic.Basic

/-!
# The moving section of an abelian coprime quotient

Let K act coprimely on the finite solvable group P. Let N be invariant,
normal, and contained in [P,K], with P/N abelian. Suppose N meets C_P(K)
trivially and every nonidentity actor has the same fixed subgroup C_P(K).
If |P| = |C_P(K)| |N|² and |K| = |N|−1, then |[P,K]| = |N|² and
K is transitive on the nonidentity N-cosets in [P,K].

Fixed-point lifting identifies C_{P/N}(K) with the image of C_P(K),
and the quotient map carries [P,K] onto [P/N,K]. The abelian coprime
splitting gives the orders. Lifting fixed points for each cyclic actor
subgroup makes the moving action free, and an orbit count proves
transitivity. The final formula keeps the factor from N on the right.

Source application: GLS, Volume 4, Chapter 2, opening of Lemma 15.7,
with P = R₁, N = M°, and the literal two-point torus K.
-/

noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupAction

private theorem commutatorAction_map_of_surjective
    {P Q K : Type*} [Group P] [Group Q] [Group K]
    [MulDistribMulAction K P] [MulDistribMulAction K Q]
    (f : P →* Q) (hf : Function.Surjective f)
    (he : ∀ k : K, ∀ x : P, f (k • x) = k • f x) :
    (commutatorAction K P).map f = commutatorAction K Q := by
  rw [commutatorAction_eq_closure, commutatorAction_eq_closure, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨k, y, rfl⟩, rfl⟩
    exact ⟨k, f y, by rw [map_mul, map_inv, he]⟩
  · rintro ⟨k, y, rfl⟩
    obtain ⟨z, rfl⟩ := hf y
    exact ⟨z⁻¹ * (k • z), ⟨k, z, rfl⟩, by rw [map_mul, map_inv, he]⟩

private theorem fixed_quotient_mem_fixed_of_pointwise
    {P K : Type*} [Group P] [Group K] [Finite P] [Finite K]
    [MulDistribMulAction K P] (N : Subgroup P) [N.Normal]
    (hN : IsInvariant K P N) (hs : Group.IsSolvable P)
    (hc : Nat.Coprime (Nat.card K) (Nat.card P))
    (hpoint : ∀ k : K, k ≠ 1 → ∀ x : P, k • x = x → x ∈ fixedPointSubgroup K P) :
    letI : MulDistribMulAction K (P ⧸ N) := quotientMulDistribMulAction N hN
    ∀ k : K, k ≠ 1 → ∀ x : P ⧸ N, k • x = x → x ∈ fixedPointSubgroup K (P ⧸ N) := by
  let : MulDistribMulAction K (P ⧸ N) := quotientMulDistribMulAction N hN
  intro k hk x hx
  let T := zpowers k
  let : MulDistribMulAction T P := MulDistribMulAction.compHom P T.subtype
  have hNT : IsInvariant T P N := ⟨fun t y => hN.invariant (t : K) y⟩
  have hcopT : Nat.Coprime (Nat.card T) (Nat.card P) :=
    hc.of_dvd_left T.card_subgroup_dvd_card
  have hmap := fixedPoints_subgroup_quotient_eq_map_of_solvable_coprime hs hcopT N hNT
  have hxT : x ∈ @FixedPoints.subgroup T (P ⧸ N) _ _
      (quotientMulDistribMulAction N hNT) := by
    intro t
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp t.property
    have hh : (k ^ i) • x = x := MulAction.mem_fixedBy_zpow hx i
    change (t : K) • x = x
    rwa [hi] at hh
  rw [hmap] at hxT
  obtain ⟨y, hy, rfl⟩ := hxT
  have hyK := hpoint k hk y (hy ⟨k, mem_zpowers k⟩)
  intro a
  change QuotientGroup.mk' N (a • y) = QuotientGroup.mk' N y
  rw [hyK a]

/-- Coprime action on an abelian quotient gives the order of the literal
moving subgroup and transitivity on its nonidentity cosets. -/
public theorem moving_section_of_abelian_quotient
    {P K : Type*} [Group P] [Group K] [Finite P] [Finite K]
    [MulDistribMulAction K P] (N : Subgroup P) [N.Normal]
    (hN : IsInvariant K P N) (hs : Group.IsSolvable P)
    (hc : Nat.Coprime (Nat.card K) (Nat.card P)) [IsMulCommutative (P ⧸ N)]
    (hNC : N ≤ commutatorAction K P)
    (hNF : Disjoint N (fixedPointSubgroup K P))
    (hpoint : ∀ k : K, k ≠ 1 → ∀ x : P, k • x = x → x ∈ fixedPointSubgroup K P)
    (hcard : Nat.card P = Nat.card (fixedPointSubgroup K P) * (Nat.card N) ^ 2)
    (hactor : Nat.card N = Nat.card K + 1) :
    Nat.card (commutatorAction K P) = (Nat.card N) ^ 2 ∧
      ∀ x ∈ commutatorAction K P, x ∉ N →
        ∀ y ∈ commutatorAction K P, y ∉ N → ∃ k : K, ∃ a ∈ N, y = (k • x) * a := by
  let C := commutatorAction K P
  let F := fixedPointSubgroup K P
  let Q := P ⧸ N
  let : MulDistribMulAction K Q := quotientMulDistribMulAction N hN
  let π : P →* Q := QuotientGroup.mk' N
  let CQ := commutatorAction K Q
  let FQ := fixedPointSubgroup K Q
  have he : ∀ k : K, ∀ x : P, π (k • x) = k • π x := fun _ _ => rfl
  have hmap : C.map π = CQ := commutatorAction_map_of_surjective π
    (QuotientGroup.mk'_surjective N) he
  have hfixedMap : F.map π = FQ :=
    (fixedPoints_subgroup_quotient_eq_map_of_solvable_coprime hs hc N hN).symm
  have hcopQ : Nat.Coprime (Nat.card K) (Nat.card Q) :=
    hc.of_dvd_right N.index_dvd_card
  have hsplitQ : IsCompl FQ CQ :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (Group.isSolvable_of_comm (fun x y : Q => mul_comm x y)) hcopQ inferInstance
  have hFQcard : Nat.card FQ = Nat.card F := by
    rw [← hfixedMap, ← relIndex_ker, QuotientGroup.ker_mk',
      ← inf_relIndex_right, hNF.eq_bot, relIndex_bot_left]
  have hQprod : Nat.card F * Nat.card CQ = Nat.card Q := by
    have hh := card_sup_eq_mul_of_normalizes_of_disjoint FQ CQ
      le_normalizer_of_normal hsplitQ.disjoint
    rw [hsplitQ.sup_eq_top, card_top, hFQcard] at hh
    exact hh.symm
  have hCQcard : Nat.card CQ = Nat.card N := by
    have hh : Nat.card N * Nat.card Q = Nat.card P := N.card_mul_index
    rw [← hQprod, hcard, pow_two] at hh
    apply Nat.mul_left_cancel (show 0 < Nat.card F from Nat.card_pos)
    apply Nat.mul_left_cancel (show 0 < Nat.card N from Nat.card_pos)
    simpa only [Nat.mul_assoc, Nat.mul_left_comm] using hh
  have hNCcard : Nat.card N * Nat.card CQ = Nat.card C := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup P) N C bot_le hNC
    rw [relIndex_bot_left, relIndex_bot_left] at hh
    have himage : N.relIndex C = Nat.card CQ := by
      rw [← hmap, ← relIndex_ker, QuotientGroup.ker_mk']
    rwa [himage] at hh
  have hCcard : Nat.card C = (Nat.card N) ^ 2 := by
    rw [← hNCcard, hCQcard, pow_two]
  let : IsInvariant K Q CQ := commutatorAction_isInvariant
  have hfree : ∀ k : K, k ≠ 1 → ∀ x : CQ, k • x = x → x = 1 := by
    intro k hk x hx
    have hfix : (x : Q) ∈ FQ := fixed_quotient_mem_fixed_of_pointwise N hN hs hc hpoint
      k hk x (congrArg Subtype.val hx)
    exact Subtype.ext (disjoint_def.mp hsplitQ.disjoint hfix x.property)
  refine ⟨hCcard, ?_⟩
  intro x hx hxN y hy hyN
  have hxQ : π x ∈ CQ := hmap ▸ mem_map_of_mem π hx
  have hyQ : π y ∈ CQ := hmap ▸ mem_map_of_mem π hy
  have hxn : (⟨π x, hxQ⟩ : CQ) ≠ 1 := fun hh =>
    hxN ((QuotientGroup.eq_one_iff x).mp (congrArg Subtype.val hh))
  have hyn : (⟨π y, hyQ⟩ : CQ) ≠ 1 := fun hh =>
    hyN ((QuotientGroup.eq_one_iff y).mp (congrArg Subtype.val hh))
  obtain ⟨k, hk⟩ := exists_smul_eq_of_free_of_card (hCQcard.trans hactor) hfree hxn hyn
  have hπ : π (k • x) = π y := congrArg Subtype.val hk
  have ha : (k • x)⁻¹ * y ∈ N := QuotientGroup.eq.mp hπ
  exact ⟨k, (k • x)⁻¹ * y, ha, by simp⟩

end Theory.GroupAction
