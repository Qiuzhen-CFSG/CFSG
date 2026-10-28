module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SectionMovement
public import Theory.Representation.SL2.PerfectCoreQuotientDegree

/-!
# The middle-root product is not invariant for unequal linear parameters

If R_j normalized the three-middle-root product M, the literal quotient
V_j/M would have a faithful effective binary representation. Its two
outside roots give a surjection onto the effective quotient and hence an
upper bound |U_i|². Transporting the actual action to SL₂(2ᵇ) gives the
lower bound 2^(2b). The concrete SL₂ group is proved perfect for b > 1;
no perfectness of an unknown original local factor is assumed.

When |U_i| < 2ᵇ these bounds contradict one another. Thus R_j does not
normalize M, and the characteristic derived subgroup of V_j lies strictly
inside M. Together with the earlier nonabelian-radical theorem this gives
1 < [V_j,V_j] < M on the same finite marked quotient. A binary opposite
endpoint is allowed, and the acting field of order four is included.

Source: Fong--Seitz I (4B), (5D) and the second paragraph of (6E), printed
p.44. Identifying the derived subgroup with the single middle root and
proving the full mixed commutator identities and irreducibility still
require the subsequent odd-Cartan argument.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates GTwoSource Theory.PSL2.SemilinearCoverage
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  {F : Type*} [Field F] [Finite F] [CharP F 2]
  (j : Fin 2) (hKj : simpleRemainder Q split j ≤ localKernel Q j)
  (μ : localGroup Q split j ≃* PSL(2,F)) (s : RootReflection Q split j)

include hKj μ s in
/-- Faithful effective sections for a binary linear field of order at
least four have the source (4B) lower bound. Perfectness here is proved for
the concrete SL₂ model, and is not an ambient-group assumption. -/
theorem linear_effectiveSection_card_bound (d : RootSection Q split j)
    (hf : Function.Injective d.effectiveRepresentation)
    {b : ℕ} (hb : 1 < b) (hF : Nat.card F = 2^b) :
    2^(2*b) ≤ Nat.card d.EffectiveCarrier := by
  have hlarge : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 2 ≤ b by omega)
  have hex : ∃ a : F, a ≠ 0 ∧ a^2 ≠ 1 := by
    obtain ⟨x,hx⟩ : IsCyclic Fˣ := inferInstance
    refine ⟨x, Units.ne_zero x, fun he => ?_⟩
    have ho : orderOf x ≤ 2 := orderOf_le_of_pow_eq_one (n := 2) (by decide)
      (Units.ext (by simpa using he))
    have hc := Nat.card_eq_card_units_add_one F
    rw [← orderOf_eq_card_of_forall_mem_zpowers hx] at hc
    omega
  obtain ⟨a,ha,hasq⟩ := hex
  let : Group.IsPerfect (SL2 F) := ⟨Matrix.SL2.commutator_eq_top ha hasq⟩
  let ρ : Representation (ZMod 2) (SL2 F) (Additive d.EffectiveCarrier) :=
    d.effectiveRepresentation.comp (alignedPinning Q split j hKj μ s).toMonoidHom
  have hρ : Function.Injective ρ := hf.comp (alignedPinning Q split j hKj μ s).injective
  have hn : ∃ g, ρ g ≠ 1 := by
    refine ⟨Theory.PSL2.SemilinearCoverage.uni 1, fun he => ?_⟩
    have hh := hρ (he.trans (map_one ρ).symm)
    have h01 := congrArg (fun g : SL2 F => g.val 0 1) hh
    simp [Theory.PSL2.SemilinearCoverage.uni] at h01
  let e : ((SL2 F) ⧸ pCore 2 (SL2 F)) ≃* SL2 F :=
    (QuotientGroup.quotientMulEquivOfEq (Matrix.SL2.twoCore_eq_bot F)).trans QuotientGroup.quotientBot
  have hd := Representation.SL2.perfect_core_quotient_finrank_bound
    (V := Additive d.EffectiveCarrier) e ρ hn (by omega) hF
  have hc : Nat.card d.EffectiveCarrier = 2 ^ Module.finrank (ZMod 2) (Additive d.EffectiveCarrier) := by
    change Nat.card (Additive d.EffectiveCarrier) = _
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive d.EffectiveCarrier))
  rw [hc]
  exact Nat.pow_le_pow_right (by decide) hd

/-- The two outside roots cover the exact effective quotient by the three
middle roots, so its order is at most |U_i|². -/
theorem middleFactorSection_card_le (hm : rotationOrder Q = 6)
    (i : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hA : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ = ⊥)
    (hR : rankOne Q split j ≤ normalizer (middleRoots Q split i j : Set _)) :
    Nat.card (middleFactorSection Q split j hKj hm i hij hKi hA hR).EffectiveCarrier ≤
      Nat.card (simpleRoot Q split i)^2 := by
  let d := middleFactorSection Q split j hKj hm i hij hKi hA hR
  let V := d.numerator
  let A := simpleRoot Q split i
  let E := rootAt Q split i (Q.simple j)
  have hAV : A ≤ V := simpleRoot_le_other_remainder Q split hm i j hij
  have hEV : E ≤ V := (exchanged_roots_le_remainder Q split hm i j hij).1
  have hMV : middleRoots Q split i j ≤ V := middleRoots_le_remainder Q split hm i j hij
  let q := QuotientGroup.mk' d.effectiveDenominator
  have hkill (z : V) (hz : (z : X ⧸ Q.D) ∈ middleRoots Q split i j) : q z = 1 := by
    apply (QuotientGroup.eq_one_iff z).mpr
    rw [d.effectiveDenominator_eq]
    exact (show d.denominator ≤ frattini d.numerator ⊔ d.denominator from le_sup_right) hz
  let f : A × E → d.EffectiveCarrier := fun z =>
    q (inclusion hAV z.1) * q (inclusion hEV z.2)
  have hf : Function.Surjective f := by
    intro z
    induction z using QuotientGroup.induction_on with
    | H x =>
      have hx : (x : X ⧸ Q.D) ∈ (simpleRemainder Q split j : Set (X ⧸ Q.D)) := x.property
      rw [radical_five_product Q split hm i j hij] at hx
      obtain ⟨abcd,⟨abc,⟨ab,⟨a,ha,b,hb,rfl⟩,c,hc,rfl⟩,v,hv,rfl⟩,e,he,hx⟩ := hx
      have hbM : b ∈ middleRoots Q split i j := (show rootAt Q split j (Q.simple i) ≤ middleRoots Q split i j from
        le_sup_left.trans le_sup_left) hb
      have hcM : c ∈ middleRoots Q split i j := (show rootAt Q split i (Q.simple j*Q.simple i) ≤ middleRoots Q split i j from
        le_sup_right.trans le_sup_left) hc
      have hvM : v ∈ middleRoots Q split i j := (show rootAt Q split j (Q.simple i*Q.simple j) ≤ middleRoots Q split i j from
        le_sup_right) hv
      let av : V := ⟨a,hAV ha⟩
      let bv : V := ⟨b,hMV hbM⟩
      let cv : V := ⟨c,hMV hcM⟩
      let vv : V := ⟨v,hMV hvM⟩
      let ev : V := ⟨e,hEV he⟩
      have hx' : av*bv*cv*vv*ev = x := Subtype.ext hx
      refine ⟨(⟨a,ha⟩,⟨e,he⟩),?_⟩
      change q av * q ev = q x
      rw [←hx', map_mul, map_mul, map_mul, map_mul,
        hkill bv hbM, hkill cv hcM, hkill vv hvM, mul_one, mul_one, mul_one]
  have hc := Nat.card_le_card_of_surjective f hf
  have hEc : Nat.card E = Nat.card A :=
    (Nat.card_congr (rightConjugateEquiv A (representative (Q.simple j) : X ⧸ Q.D))).symm
  simpa only [Nat.card_prod, hEc, pow_two] using hc

include hKj μ s in
/-- The precise non-invariance argument on printed p.44: a smaller opposite
root cannot cover a faithful effective quotient by the middle roots. -/
theorem rankOne_not_normalizes_middle (hm : rotationOrder Q = 6)
    (i : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hA : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ = ⊥)
    {b : ℕ} (hb : 1 < b) (hF : Nat.card F = 2^b)
    (hsmall : Nat.card (simpleRoot Q split i) < Nat.card F) :
    ¬ rankOne Q split j ≤ normalizer (middleRoots Q split i j : Set _) := by
  intro hR
  let d := middleFactorSection Q split j hKj hm i hij hKi hA hR
  have hl := linear_effectiveSection_card_bound Q split j hKj μ s d
    (middleFactorSection_injective Q split j hKj μ s hm i hij hKi hA hR) hb hF
  have hu := middleFactorSection_card_le Q split j hKj hm i hij hKi hA hR
  have hpow : (Nat.card F)^2 ≤ Nat.card (simpleRoot Q split i)^2 := by
    rw [hF, ←pow_mul, Nat.mul_comm b 2]
    exact hl.trans hu
  nlinarith

include hKj μ s in
/-- Consequently the actual derived subgroup lies strictly inside the three
middle roots. This is the strict containment preceding the torus analysis. -/
theorem radical_commutator_lt_middle (hm : rotationOrder Q = 6)
    (i : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hA : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ = ⊥)
    {b : ℕ} (hb : 1 < b) (hF : Nat.card F = 2^b)
    (hsmall : Nat.card (simpleRoot Q split i) < Nat.card F) :
    ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ < middleRoots Q split i j := by
  apply lt_of_le_of_ne (radical_commutator_le_middle Q split hm i j hij hKi hA)
  intro he
  apply rankOne_not_normalizes_middle Q split j hKj μ s hm i hij hKi hA hb hF hsmall
  rw [←he]
  intro r hr
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hV := (rankOne_le_parabolic Q split j).trans
    (remainder_parabolic_normalizes Q split j hKj)
  rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (hV hr)]

include hKj μ s in
/-- The unequal linear branch includes a binary opposite endpoint and uses
no perfectness hypothesis on either unknown original local factor. -/
theorem unequal_linear_middle_structure
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (hm : rotationOrder Q = 6) (i : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (μi : localGroup Q split i ≃* PSL(2,E)) (si : RootReflection Q split i)
    {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hE : Nat.card E = 2^a) (hF : Nat.card F = 2^b) :
    ¬ rankOne Q split j ≤ normalizer (middleRoots Q split i j : Set _) ∧
      ⊥ < ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ ∧
      ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ < middleRoots Q split i j := by
  have hA := simpleRoot_commutator_eq_bot_of_linear Q split i μi
  have hsmall : Nat.card (simpleRoot Q split i) < Nat.card F := by
    rw [GTwoSource.simpleRoot_card Q split i hKi μi, hE, hF]
    exact Nat.pow_lt_pow_right (by decide) hab
  exact ⟨rankOne_not_normalizes_middle Q split j hKj μ s hm i hij hKi hA (by omega) hF hsmall,
    bot_lt_iff_ne_bot.mpr (radical_commutator_ne_bot Q split hm i j hij si),
    radical_commutator_lt_middle Q split j hKj μ s hm i hij hKi hA (by omega) hF hsmall⟩

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
