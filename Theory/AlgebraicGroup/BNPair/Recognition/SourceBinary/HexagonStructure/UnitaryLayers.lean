module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.UnitarySections
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.CartanActions
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OrderFormulas
public import Theory.SpecificGroups.SU3.SylowOmega
public import Theory.SpecificGroups.SU3.BinaryRootFrattini
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport

/-!
# Two actual unitary Frattini layers in the hexagon

Hermitian root coordinates have a nontrivial square. Transport through the
actual Sylow and scalar projection supplies such a square in the canonical
root, for special as well as projective unitary actors. Its conjugate lies
in the radical, and its square in the radical's Frattini subgroup. The
source reflection moves this square to a disjoint root. The concrete
unitary degree theorem therefore applies to both literal Frattini layers.

Multiplication gives |U_sj| ≥ 2^(12n). The five-root coordinates then force
2n ≤ a if the opposite root has order 2^a, excluding orders two, four and
eight when n ≥ 2. These are actual section actions, without perfectness
assumptions on the original factors. The general unitary exclusion, its
lower-central-series step and the degree-one scalar cases remain separate.

Source: Fong--Seitz I (5D), (6D), printed pp.26--27,41--43. This is the
successive-section input to (6D), not its full exclusion.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates HermitianForm

private theorem square_witness_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : ∃ b : B, b^2 ≠ 1) : ∃ a : A, a^2 ≠ 1 := by
  obtain ⟨b,hb⟩ := h
  refine ⟨e.symm b,fun he => hb ?_⟩
  simpa only [map_pow,map_one,e.apply_symm_apply] using congrArg e he

variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
  {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
  (hconj : ∀ x, J.conj x = x^(2^n))

private instance : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
  Finite.of_surjective J.specialToProjective J.specialToProjective_surjective

include hcard hconj hn in
private theorem hermitian_square_witness : ∃ a : hermitianUnipotentCoord J, a^2 ≠ 1 := by
  let : CharP F 2 := by
    let := Fintype.ofFinite F
    apply charP_of_card_eq_prime_pow (p := 2) (f := n*2)
    simpa only [Nat.card_eq_fintype_card,pow_mul] using hcard
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  obtain ⟨a,ha⟩ := EvenSemilinear.coord_first_surjective J hcard hf 1
  refine ⟨a,fun he => (one_ne_zero : (1 : F) ≠ 0) ?_⟩
  exact ha.symm.trans ((BinaryRootFrattini.square_one_iff J a).mp he)

include hn hcard hconj in
/-- Every actual projective unitary Sylow contains a nontrivial square.
The Hermitian form need not already be in standard coordinates. -/
theorem projective_unitary_sylow_square_witness
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) : ∃ a : T, a^2 ≠ 1 := by
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  obtain ⟨e⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv J (2^n) hcard hf
  let T' := T.mapSurjective (f := e.toMonoidHom) e.surjective
  let a : T ≃* T' := (T : Subgroup _).equivMapOfInjective e.toMonoidHom e.injective
  let J' := OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  exact square_witness_of_equiv
    (a.trans (SylowOmega.projectiveSylowEquivCoords J' hn hcard hf rfl T'))
    (hermitian_square_witness J' hn hcard hconj)

include hn hcard hconj in
/-- The actual scalar projection preserves the Sylow square witness. -/
theorem special_unitary_sylow_square_witness (T : Sylow 2 J.specialSubgroup) :
    ∃ a : T, a^2 ≠ 1 :=
  square_witness_of_equiv (SylowOmega.specialSylowEquivProjective J T)
    (projective_unitary_sylow_square_witness J hn hcard hconj _)

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- Identify a canonical root with a full Sylow through its actual actor
marking and the exact root order, then transport a square. -/
theorem root_square_of_model_sylow (j : Fin 2)
    {M : Type*} [Group M] [Finite M]
    (μ : rankOne Q split j ≃* M) (T : Sylow 2 M)
    (hcard : Nat.card (simpleRoot Q split j) = Nat.card T)
    (hsquare : ∃ t : T, t^2 ≠ 1) :
    ∃ a : simpleRoot Q split j, a^2 ≠ 1 := by
  let A := (simpleRoot Q split j).subgroupOf (rankOne Q split j)
  have hA : IsPGroup 2 A := (split.isTwo.to_le (simpleRoot_le Q split j)).comap_subtype
  obtain ⟨S,hS⟩ := hA.exists_le_sylow
  let S' := S.mapSurjective (f := μ.toMonoidHom) μ.surjective
  let eS : S ≃* S' := (S : Subgroup _).equivMapOfInjective μ.toMonoidHom μ.injective
  let eA : A ≃* simpleRoot Q split j := subgroupOfEquivOfLe
    (show simpleRoot Q split j ≤ rankOne Q split j from le_sup_left)
  have hc : Nat.card A = Nat.card S := by
    calc
      Nat.card A = Nat.card (simpleRoot Q split j) := Nat.card_congr eA.toEquiv
      _ = Nat.card T := hcard
      _ = Nat.card S' := Nat.card_congr (S'.equiv T).symm.toEquiv
      _ = Nat.card S := Nat.card_congr eS.symm.toEquiv
  have he : A = (S : Subgroup (rankOne Q split j)) := eq_of_le_of_card_ge hS hc.ge
  exact square_witness_of_equiv
    (eA.symm.trans ((MulEquiv.subgroupCongr he).trans (eS.trans (S'.equiv T)))) hsquare

/-- Transport a canonical-root square into the own-root conjugate of the
same radical; no local model or parameter restriction is needed. -/
theorem root_square_frattini_action_ne_one
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (s : RootReflection Q split j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hsquare : ∃ a : simpleRoot Q split j, a^2 ≠ 1) :
    (frattiniSection Q split j (radicalSection Q split j hKj)).action ≠ 1 := by
  obtain ⟨a,ha⟩ := square_witness_of_equiv
    (ReeSource.RootAction.conjugateEquiv (simpleRoot Q split j) (representative (Q.simple i))) hsquare
  intro he
  exact reflection_moves_frattini_radical_of_conjugate_square Q split hhex i j hij s hKj a ha
    (by rw [he]; rfl)

variable (j : Fin 2) (σ : J.specialSubgroup →* rankOne Q split j)
  (hσ : Function.Surjective σ)

include hn hcard hconj σ hσ in
/-- The literal Φ(U_sj)/Φ²(U_sj) has at least 6n binary dimensions. -/
theorem unitary_frattini_radical_card_bound
    (hhex : rotationOrder Q = 6) (i : Fin 2) (hij : i ≠ j)
    (s : RootReflection Q split j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hsquare : ∃ a : simpleRoot Q split j, a^2 ≠ 1) :
    2^(6*n) ≤ Nat.card (frattini (simpleRemainder Q split j) ⧸
      frattini (frattini (simpleRemainder Q split j))) := by
  let d := radicalSection Q split j hKj
  let f := frattiniSection Q split j d
  have hb := unitary_section_card_bound Q split j J hn hcard hconj σ hσ f
    (root_square_frattini_action_ne_one Q split hhex i j hij s hKj hsquare)
  have he : f.effectiveDenominator = frattini f.numerator := by
    rw [f.effectiveDenominator_eq]; exact sup_bot_eq _
  change 2^(6*n) ≤ f.effectiveDenominator.index at hb
  rw [he] at hb
  let e : frattini d.numerator ≃* f.numerator :=
    (frattini d.numerator).equivMapOfInjective d.numerator.subtype d.numerator.subtype_injective
  have hc := Nat.card_congr (QuotientGroup.congr _ _ e (frattini_map_equiv e)).toEquiv
  change Nat.card (frattini d.numerator ⧸ frattini (frattini d.numerator)) =
    Nat.card (f.numerator ⧸ frattini f.numerator) at hc
  change 2^(6*n) ≤ Nat.card (frattini d.numerator ⧸ frattini (frattini d.numerator))
  rw [hc]
  exact hb

include hn hcard hconj σ hσ in
/-- The first literal unitary Frattini layer, with no projective marking
required beyond the actual special-unitary cover. -/
theorem unitary_radical_first_layer_card_bound
    (hhex : rotationOrder Q = 6) (i : Fin 2) (hij : i ≠ j)
    (s : RootReflection Q split j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    2^(6*n) ≤ Nat.card (simpleRemainder Q split j ⧸ frattini (simpleRemainder Q split j)) := by
  let d := radicalSection Q split j hKj
  have hmove : d.action ≠ 1 := by
    intro he
    apply simpleRoot_ne_bot Q split i
    apply eq_bot_iff.mpr
    intro a ha
    apply mem_bot.mpr
    by_contra hn
    exact reflection_moves_section Q split hhex i j hij s d a ha
      (simpleRoot_le_other_remainder Q split hhex i j hij ha) hn
      (by change (⊥ : Subgroup _).map _ ≤ _; rw [Subgroup.map_bot]; exact bot_le)
      (by rw [he]; rfl)
  have h1 := unitary_section_card_bound Q split j J hn hcard hconj σ hσ d hmove
  have he : d.effectiveDenominator = frattini d.numerator := by
    rw [d.effectiveDenominator_eq]; exact sup_bot_eq _
  change 2^(6*n) ≤ d.effectiveDenominator.index at h1
  rw [he] at h1
  exact h1

include hn hcard hconj σ hσ in
/-- The two actual unitary sections give the source whole-radical lower bound. -/
theorem unitary_radical_two_layer_bound
    (hhex : rotationOrder Q = 6) (i : Fin 2) (hij : i ≠ j)
    (s : RootReflection Q split j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hsquare : ∃ a : simpleRoot Q split j, a^2 ≠ 1) :
    2^(12*n) ≤ Nat.card (simpleRemainder Q split j) := by
  let d := radicalSection Q split j hKj
  have h1 := unitary_radical_first_layer_card_bound J hn hcard hconj Q split j σ hσ
    hhex i hij s hKj
  have h2 := unitary_frattini_radical_card_bound J hn hcard hconj Q split j σ hσ
    hhex i hij s hKj hsquare
  have hsize : Nat.card (frattini d.numerator ⧸ frattini (frattini d.numerator)) ≤
      Nat.card (frattini d.numerator) :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  calc
    2^(12*n) = 2^(6*n)*2^(6*n) := by rw [←pow_add]; congr 1; omega
    _ ≤ Nat.card (d.numerator ⧸ frattini d.numerator)*Nat.card (frattini d.numerator) :=
      Nat.mul_le_mul h1 (h2.trans hsize)
    _ = Nat.card d.numerator := (frattini d.numerator).index_mul_card

include hn hcard hconj σ hσ in
/-- The five actual root orders and the two unitary layers force 2n ≤ a.
The exponent a denotes the order of the entire opposite root. -/
theorem unitary_hexagon_parameter_bound
    (hhex : rotationOrder Q = 6) (i : Fin 2) (hij : i ≠ j)
    (s : RootReflection Q split j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hsquare : ∃ a : simpleRoot Q split j, a^2 ≠ 1)
    (hroot : Nat.card (simpleRoot Q split j) = (2^n)^3)
    {a : ℕ} (hopp : Nat.card (simpleRoot Q split i) = 2^a) : 2*n ≤ a := by
  have hU : Nat.card split.U = (2^a*(2^n)^3)^3 := by
    have hu := unipotent_card_even Q split 3 hhex
    have hi : i = 0 ∨ i = 1 := by omega
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (hij rfl).elim
    · rwa [hopp,hroot] at hu
    · rwa [hroot,hopp,mul_comm ((2^n)^3) (2^a)] at hu
    · exact (hij rfl).elim
  have hV : Nat.card (simpleRemainder Q split j) = 2^(3*a+6*n) := by
    have hh := unipotent_card_simple Q split j
    rw [hU,hroot] at hh
    apply Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (Nat.pow_pos (by decide : 0 < 2)))
    calc
      (2^n)^3 * Nat.card (simpleRemainder Q split j) = (2^a*(2^n)^3)^3 := hh.symm
      _ = (2^n)^3 * 2^(3*a+6*n) := by
        simp only [←pow_mul,←pow_add]
        congr 1
        omega
  have hb := unitary_radical_two_layer_bound J hn hcard hconj Q split j σ hσ
    hhex i hij s hKj hsquare
  rw [hV] at hb
  have hh := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb
  omega

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
