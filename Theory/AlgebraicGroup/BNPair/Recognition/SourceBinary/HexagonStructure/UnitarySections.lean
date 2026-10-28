module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.FrattiniDetection
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootLocalCover
public import Theory.Representation.SU3.BinaryDegree

/-!
# Effective unitary sections with their scalar kernel retained

An actual surjection from SU₃(2ⁿ), n ≥ 2, onto the root-generated R_j
proves its perfectness from the concrete model. If its action on a
literal section is nontrivial, the effective action is nontrivial:
otherwise its image would be both perfect and a two-group by the
Frattini-kernel theorem. The actual central panel projection onto
PSU₃ then puts the effective-action kernel inside the literal K_j.

The resulting binary representation has dimension at least 6n by the
proved unitary degree theorem. Root movement discharges its nontriviality
on U_sj. The same argument applies to special and projective actors;
no scalar kernel is discarded and no faithful SU₃ action is presumed.
Original-factor and original-quotient applications are in the matching
CFSG module, where both model inputs are constructed.

Source: Fong–Seitz I (4D), (5D)–(5F), (6D), printed pp.21–22,26–28,41–43.
This is the nonsolvable effective-section input, not the full (6D)
exclusion. The solvable SU₃(2)/PSU₃(2) case, and therefore the primitive
divisor exception at exponent six, are outside n ≥ 2 and remain required.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (j : Fin 2)
  {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
  {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
  (hconj : ∀ x, J.conj x = x^(2^n))
  (σ : J.specialSubgroup →* rankOne Q split j) (hσ : Function.Surjective σ)

private theorem effective_action_ne_one_of_perfect
    (d : RootSection Q split j) [Group.IsPerfect (rankOne Q split j)]
    (hmove : d.action ≠ 1) : d.effectiveAction ≠ 1 := by
  intro he
  have hp := d.effectiveKernel_action_isTwo
  rw [MonoidHom.ker_eq_top_iff.mpr he, ← MonoidHom.range_eq_map] at hp
  let : Group.IsNilpotent d.action.range := hp.isNilpotent
  let : Group.IsPerfect d.action.range := Group.IsPerfect.range d.action
  obtain ⟨r,hr⟩ : ∃ r, d.action r ≠ 1 := by
    by_contra! hh
    exact hmove (MonoidHom.ext hh)
  let : Nontrivial d.action.range := ⟨⟨⟨d.action r,⟨r,rfl⟩⟩, 1,
    fun hh => hr (congrArg Subtype.val hh)⟩⟩
  exact Group.IsPerfect.not_isNilpotent d.action.range inferInstance

include hn hcard hconj σ hσ in
/-- The concrete special-unitary cover detects nontrivial action on the
literal effective quotient. The actor need not itself be the special model. -/
theorem unitary_section_effectiveAction_ne_one (d : RootSection Q split j)
    (hmove : d.action ≠ 1) : d.effectiveAction ≠ 1 := by
  let : Group.IsPerfect J.specialSubgroup :=
    Representation.SU3.BinaryDegree.isPerfect_specialSubgroup J hn hcard hconj
  let : Group.IsPerfect (rankOne Q split j) := Group.IsPerfect.ofSurjective hσ
  exact effective_action_ne_one_of_perfect Q split j d hmove

include hn hcard hconj σ hσ in
/-- The special and projective unitary branches both have the source (4D)
bound on the same effective section, without discarding the scalar center. -/
theorem unitary_section_card_bound (d : RootSection Q split j)
    (hmove : d.action ≠ 1) : 2^(6*n) ≤ Nat.card d.EffectiveCarrier := by
  have heff := unitary_section_effectiveAction_ne_one Q split j J hn hcard hconj σ hσ d hmove
  let ρ : Representation (ZMod 2) J.specialSubgroup (Additive d.EffectiveCarrier) :=
    d.effectiveRepresentation.comp σ
  have hrho : ∃ g, ρ g ≠ 1 := by
    by_contra! hh
    apply heff
    apply MonoidHom.ext
    intro r
    obtain ⟨g,rfl⟩ := hσ r
    ext z
    have hz := congrArg (fun f : Module.End (ZMod 2) (Additive d.EffectiveCarrier) =>
      f (Additive.ofMul z)) (hh g)
    exact Additive.ofMul.injective hz
  have hd := Representation.SU3.BinaryDegree.finrank_ge J hn hcard hconj ρ hrho
  have hc : Nat.card d.EffectiveCarrier =
      2 ^ Module.finrank (ZMod 2) (Additive d.EffectiveCarrier) := by
    change Nat.card (Additive d.EffectiveCarrier) = _
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive d.EffectiveCarrier))
  rw [hc]
  exact Nat.pow_le_pow_right (by decide) hd

include hn hcard hconj σ hσ in
/-- The action kernel lies in the literal panel kernel. The actual local
projective marking and the special-unitary cover are earlier model inputs. -/
theorem unitary_section_effective
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (d : RootSection Q split j) (hmove : d.action ≠ 1) : d.IsEffective := by
  let : Group.IsPerfect J.specialSubgroup :=
    Representation.SU3.BinaryDegree.isPerfect_specialSubgroup J hn hcard hconj
  let : Group.IsPerfect (rankOne Q split j) := Group.IsPerfect.ofSurjective hσ
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  have hq : 2 < 2^n := (by decide : 2 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) hn)
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    BenderSuzuki.External.huppert_II_10_13 J (2^n) hq hcard hfixed
  let π := μ.toMonoidHom.comp (RootLocalCover.projection Q split j)
  have hπ : Function.Surjective π := μ.surjective.comp
    (RootLocalCover.central_odd_cover Q split j hKj).1
  have hker : π.ker = (RootLocalCover.projection Q split j).ker := by
    ext r
    change μ (RootLocalCover.projection Q split j r) = 1 ↔ RootLocalCover.projection Q split j r = 1
    exact μ.map_eq_one_iff
  have hc : π.ker ≤ center (rankOne Q split j) :=
    hker ▸ RootLocalCover.projection_ker_central Q split j
  have hm : ∃ r, d.effectiveAction r ≠ 1 := by
    by_contra! hh
    exact unitary_section_effectiveAction_ne_one Q split j J hn hcard hconj σ hσ d hmove
      (MonoidHom.ext hh)
  have hh := Representation.SU3.BinaryDegree.ker_le_of_perfect_central_cover π hπ hc d.effectiveAction hm
  rwa [hker, RootLocalCover.projection_ker] at hh

include hn hcard hconj σ hσ in
/-- The actual whole radical is an effective unitary section with at least
6n binary dimensions. Its root movement is established internally. -/
theorem unitary_radical_effective_and_card_bound
    (hhex : rotationOrder Q = 6) (i : Fin 2) (hij : i ≠ j)
    (s : RootReflection Q split j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    (radicalSection Q split j hKj).IsEffective ∧
      2^(6*n) ≤ Nat.card ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j)) := by
  let d := radicalSection Q split j hKj
  have hmove : d.action ≠ 1 := by
    intro he
    apply simpleRoot_ne_bot Q split i
    apply eq_bot_iff.mpr
    intro a ha
    apply mem_bot.mpr
    by_contra hne
    exact reflection_moves_section Q split hhex i j hij s d a ha
      (simpleRoot_le_other_remainder Q split hhex i j hij ha) hne
      (by change (⊥ : Subgroup _).map _ ≤ _; rw [Subgroup.map_bot]; exact bot_le)
      (by rw [he]; rfl)
  refine ⟨unitary_section_effective Q split j J hn hcard hconj σ hσ hKj μ d hmove, ?_⟩
  have hh := unitary_section_card_bound Q split j J hn hcard hconj σ hσ d hmove
  have he : d.effectiveDenominator = frattini (simpleRemainder Q split j) := by
    rw [d.effectiveDenominator_eq]
    exact sup_bot_eq _
  change 2^(6*n) ≤ d.effectiveDenominator.index at hh
  rw [he] at hh
  exact hh
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
