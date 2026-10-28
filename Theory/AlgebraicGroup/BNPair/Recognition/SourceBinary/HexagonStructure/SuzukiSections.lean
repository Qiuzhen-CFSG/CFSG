module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.FrattiniDetection
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.SuzukiCoordinates
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OrderFormulas
public import Theory.Representation.Suzuki.BinaryDegree
public import BenderSuzuki.External.Huppert.XI.theorem_3_6

/-!
# Effective Suzuki sections and the initial hexagon parameter bound

An actual identification R_j ≃ Sz(2^(2m+1)), with m > 0, makes any
nontrivial section action faithful. Its effective-action kernel is a
two-group by FrattiniDetection. Simplicity and nonsolvability of the
concrete matrix group eliminate that kernel. Thus root movement gives
faithful action on the literal source quotient, with no effectiveness,
perfectness, or simplicity assumption about an unknown ambient group.

The same reflection moves Φ(U_sj): the canonical own-root conjugate
contains a nontrivial square and is disjoint from its reflected root.
Both effective quotients therefore satisfy the Suzuki binary degree
bound. Multiplying their orders proves |U_sj| ≥ 2^(8b), b = 2m+1.
The exact five-root order gives 4b ≤ 3a when the opposite root has
order 2^a. These are the actual initial inequalities in (6C).

The matrix-square lemma includes m = 0. Faithfulness and the degree
bounds here require m > 0; no solvable Sz(2) conclusion is claimed.
The remaining odd-Cartan and equal-parameter contradictions in (6C),
unitary exclusion (6D), and solvable-section arguments remain separate.
The original-factor applications are in CFSG HexagonStructure/SuzukiSections.

Source: Fong–Seitz I (4F), (5D)–(5F), (6C), printed pp.23–24,26–28,39–41.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (j : Fin 2) {m : ℕ} (hm : 0 < m)
  (μ : rankOne Q split j ≃* SuzukiMatrixGroup m)

include hm μ in
/-- On a genuine nonsolvable Suzuki rank-one group, every nontrivial
section action is faithful on the literal effective quotient. -/
theorem suzuki_section_effectiveAction_injective (d : RootSection Q split j)
    (hmove : d.action ≠ 1) : Function.Injective d.effectiveAction := by
  let : IsSimpleGroup (SuzukiMatrixGroup m) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  let : IsSimpleGroup (rankOne Q split j) := μ.isSimpleGroup
  have hf : Function.Injective d.action := by
    apply d.action.ker_eq_bot_iff.mp
    exact (inferInstance : d.action.ker.Normal).eq_bot_or_eq_top.resolve_right
      (fun he => hmove (MonoidHom.ker_eq_top_iff.mp he))
  have htwo := d.effectiveKernel_isTwo_of_faithful hf
  apply d.effectiveAction.ker_eq_bot_iff.mp
  rcases (inferInstance : d.effectiveAction.ker.Normal).eq_bot_or_eq_top with hk | hk
  · exact hk
  · have hR : IsPGroup 2 (rankOne Q split j) :=
      htwo.of_equiv ((MulEquiv.subgroupCongr hk).trans topEquiv)
    have hM := hR.of_equiv μ
    let : Group.IsNilpotent (SuzukiMatrixGroup m) := hM.isNilpotent
    exact (BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hm inferInstance).elim

include hm μ in
/-- The (4F) lower bound applies to the actual source effective section. -/
theorem suzuki_section_card_bound (d : RootSection Q split j)
    (hmove : d.action ≠ 1) : 2^(4*(2*m+1)) ≤ Nat.card d.EffectiveCarrier := by
  let ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) (Additive d.EffectiveCarrier) :=
    d.effectiveRepresentation.comp μ.symm.toMonoidHom
  have hf : Function.Injective ρ :=
    (d.effectiveRepresentation_injective
      (suzuki_section_effectiveAction_injective Q split j hm μ d hmove)).comp μ.symm.injective
  have hd := Representation.Suzuki.finrank_ge (by omega : 1 ≤ m) ρ hf
  have hc : Nat.card d.EffectiveCarrier =
      2 ^ Module.finrank (ZMod 2) (Additive d.EffectiveCarrier) := by
    change Nat.card (Additive d.EffectiveCarrier) = _
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive d.EffectiveCarrier))
  rw [hc]
  exact Nat.pow_le_pow_right (by decide) hd

/-- Root geometry discharges the action premise on the whole radical. -/
theorem suzuki_radical_action_ne_one (hhex : rotationOrder Q = 6)
    (i : Fin 2) (hij : i ≠ j) (s : RootReflection Q split j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    (radicalSection Q split j hKj).action ≠ 1 := by
  intro he
  apply simpleRoot_ne_bot Q split i
  apply eq_bot_iff.mpr
  intro a ha
  apply mem_bot.mpr
  by_contra hn
  exact reflection_moves_section Q split hhex i j hij s
    (radicalSection Q split j hKj) a ha
    (simpleRoot_le_other_remainder Q split hhex i j hij ha) hn
    (by change (⊥ : Subgroup _).map _ ≤ _; rw [Subgroup.map_bot]; exact bot_le)
    (by rw [he]; rfl)

include hm μ in
theorem suzuki_radical_effective (hhex : rotationOrder Q = 6)
    (i : Fin 2) (hij : i ≠ j) (s : RootReflection Q split j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    (radicalSection Q split j hKj).IsEffective := by
  unfold RootSection.IsEffective
  rw [(MonoidHom.ker_eq_bot_iff _).mpr
    (suzuki_section_effectiveAction_injective Q split j hm μ _
      (suzuki_radical_action_ne_one Q split j hhex i hij s hKj))]
  exact bot_le

include hm μ in
theorem suzuki_radical_card_bound (hhex : rotationOrder Q = 6)
    (i : Fin 2) (hij : i ≠ j) (s : RootReflection Q split j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    2^(4*(2*m+1)) ≤ Nat.card ((simpleRemainder Q split j) ⧸
      frattini (simpleRemainder Q split j)) := by
  have hh := suzuki_section_card_bound Q split j hm μ _
    (suzuki_radical_action_ne_one Q split j hhex i hij s hKj)
  have he : (radicalSection Q split j hKj).effectiveDenominator =
      frattini (simpleRemainder Q split j) := by
    rw [RootSection.effectiveDenominator_eq]
    exact sup_bot_eq _
  change 2^(4*(2*m+1)) ≤ (radicalSection Q split j hKj).effectiveDenominator.index at hh
  rw [he] at hh
  exact hh

/-- The matrix root has a nontrivial square, including Sz(2). This uses
only the existing exact multiplication law. -/
theorem suzuki_root_exists_nontrivial_square (m : ℕ) :
    ∃ a : SuzukiRootSubgroup m, a^2 ≠ 1 := by
  refine ⟨ReeSource.matrixRootPoint m 1 0, ?_⟩
  have hs : (ReeSource.matrixRootPoint m 1 0)^2 = ReeSource.matrixRootPoint m 0 1 := by
    simp only [pow_two, ReeSource.matrixRootPoint_mul, CharTwo.add_self_eq_zero,
      zero_add, map_one, mul_one]
  rw [hs]
  intro he
  have hh := congrArg (fun x : SuzukiRootSubgroup m => x.val.val (0 : Fin 4) (2 : Fin 4)) he
  simp [ReeSource.matrixRootPoint, SuzukiRootGL, SuzukiRootMatrix] at hh

/-- Transfer a square to the literal own-root conjugate in the radical. -/
theorem suzuki_conjugate_exists_nontrivial_square (i : Fin 2)
    (ν : simpleRoot Q split j ≃* SuzukiRootSubgroup m) :
    ∃ a : rootAt Q split j (Q.simple i), a^2 ≠ 1 := by
  obtain ⟨b,hb⟩ := suzuki_root_exists_nontrivial_square m
  let a := ν.symm b
  have ha : a^2 ≠ 1 := by
    intro he
    apply hb
    have hh := congrArg ν he
    simpa only [map_pow, map_one, a, MulEquiv.apply_symm_apply] using hh
  let n := representative (Q.simple i)
  let v : rootAt Q split j (Q.simple i) := ⟨(n : X ⧸ Q.D)⁻¹*a*n, by
    change (n : X ⧸ Q.D)*((n : X ⧸ Q.D)⁻¹*a*n)*(n : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split j
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using a.property⟩
  refine ⟨v,fun he => ha (Subtype.ext ?_)⟩
  change (a : X ⧸ Q.D)^2 = 1
  have hh := congrArg (fun x : rootAt Q split j (Q.simple i) =>
    MulAut.conj (n : X ⧸ Q.D) (x : X ⧸ Q.D)) he
  change (MulAut.conj (n : X ⧸ Q.D)) ((v : X ⧸ Q.D)^2) =
    (MulAut.conj (n : X ⧸ Q.D)) 1 at hh
  rw [map_pow, map_one] at hh
  simpa only [v, MulAut.conj_apply, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using hh

/-- The second effective source section in (6C): Φ(U_sj), even when the
opposite endpoint is linear. -/
theorem suzuki_frattini_radical_action_ne_one (hhex : rotationOrder Q = 6)
    (i : Fin 2) (hij : i ≠ j) (s : RootReflection Q split j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (ν : simpleRoot Q split j ≃* SuzukiRootSubgroup m) :
    (frattiniSection Q split j (radicalSection Q split j hKj)).action ≠ 1 := by
  obtain ⟨a,ha⟩ := suzuki_conjugate_exists_nontrivial_square Q split j i ν
  intro he
  exact reflection_moves_frattini_radical_of_conjugate_square Q split hhex i j hij s hKj a ha
    (by rw [he]; rfl)

include hm μ in
/-- Two successive literal effective sections force the source (6C)
lower bound on the entire radical. -/
theorem suzuki_radical_two_layer_bound (hhex : rotationOrder Q = 6)
    (i : Fin 2) (hij : i ≠ j) (s : RootReflection Q split j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (ν : simpleRoot Q split j ≃* SuzukiRootSubgroup m) :
    2^(8*(2*m+1)) ≤ Nat.card (simpleRemainder Q split j) := by
  let d := radicalSection Q split j hKj
  let f := frattiniSection Q split j d
  have h1 := suzuki_radical_card_bound Q split j hm μ hhex i hij s hKj
  have h2 := suzuki_section_card_bound Q split j hm μ f
    (suzuki_frattini_radical_action_ne_one Q split j hhex i hij s hKj ν)
  have hsz : Nat.card f.EffectiveCarrier ≤ Nat.card (frattini d.numerator) := by
    calc
      Nat.card f.EffectiveCarrier ≤ Nat.card f.numerator :=
        Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
      _ = Nat.card (frattini d.numerator) :=
        Nat.card_congr ((frattini d.numerator).equivMapOfInjective
          d.numerator.subtype d.numerator.subtype_injective).symm.toEquiv
  calc
    2^(8*(2*m+1)) = 2^(4*(2*m+1))*2^(4*(2*m+1)) := by
      rw [← pow_add]; congr 1; omega
    _ ≤ Nat.card (d.numerator ⧸ frattini d.numerator) * Nat.card (frattini d.numerator) :=
      Nat.mul_le_mul h1 (h2.trans hsz)
    _ = Nat.card d.numerator := (frattini d.numerator).index_mul_card

include hm μ in
/-- The initial parameter inequality of (6C), using the literal five-root
order and both actual effective sections, not an unrelated module bound. -/
theorem suzuki_hexagon_parameter_bound (hhex : rotationOrder Q = 6)
    (i : Fin 2) (hij : i ≠ j) (s : RootReflection Q split j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (ν : simpleRoot Q split j ≃* SuzukiRootSubgroup m)
    {a : ℕ} (hopp : Nat.card (simpleRoot Q split i) = 2^a) :
    4*(2*m+1) ≤ 3*a := by
  have hUj : Nat.card (simpleRoot Q split j) = 2^(2*(2*m+1)) := by
    rw [Nat.card_congr ν.toEquiv, ReeSource.matrixRoot_card, ← pow_mul]
    congr 1; omega
  have hU : Nat.card split.U = (2^a*2^(2*(2*m+1)))^3 := by
    have hu := unipotent_card_even Q split 3 hhex
    have hi : i = 0 ∨ i = 1 := by omega
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (hij rfl).elim
    · rwa [hopp,hUj] at hu
    · rwa [hUj,hopp,mul_comm (2^(2*(2*m+1))) (2^a)] at hu
    · exact (hij rfl).elim
  have hV : Nat.card (simpleRemainder Q split j) = 2^(3*a+4*(2*m+1)) := by
    have hh := unipotent_card_simple Q split j
    rw [hU,hUj] at hh
    apply Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide : 0 < 2))
    calc
      2^(2*(2*m+1)) * Nat.card (simpleRemainder Q split j) =
          (2^a*2^(2*(2*m+1)))^3 := hh.symm
      _ = 2^(2*(2*m+1)) * 2^(3*a+4*(2*m+1)) := by
        rw [← pow_add, ← pow_mul, ← pow_add]
        congr 1; omega
  have hb := suzuki_radical_two_layer_bound Q split j hm μ hhex i hij s hKj ν
  rw [hV] at hb
  have hh := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb
  omega
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
