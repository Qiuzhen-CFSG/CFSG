module

public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.Residuals.Endpoints
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Flags with stabilizer order divisible by five

Cauchy's theorem supplies a nontrivial five-subgroup of the flag stabilizer.
Its fixed vectors form a proper binary subspace whose order is congruent to
32 modulo five; hence it has exactly two vectors. On any invariant subspace,
the number of fixed vectors is between one and two, and is congruent to the
subspace order modulo five. This excludes dimensions two and three. An
invariant hyperplane has only one fixed vector, so it cannot contain an
invariant line. Thus the only nonempty flag types left are the two endpoints.

No Sylow-overgroup exhaustion or parabolic order formula is used.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), the parabolic
case A.3.12(5), printed pp.47–48, and the L₅(2) branch of 1.3.9, printed p.514.
-/

public section

open Subgroup
namespace BinaryLinear.FiveFlagGeometry
open OuterCyclic

private instance : Finite (LinearGroup 5) :=
  Finite.of_equiv (Matrix.GeneralLinearGroup (Fin 5) (ZMod 2)) (matrixEquivLinear 5).toEquiv

private theorem fixedSpace_card_two (Q : Subgroup (LinearGroup 5))
    (hQ : IsPGroup 5 Q) (hQ0 : Q ≠ ⊥) : Nat.card (fixedSpace Q) = 2 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have he : MulAction.fixedPoints Q (Space 5) = (fixedSpace Q : Set (Space 5)) := by
    ext v
    rw [MulAction.mem_fixedPoints]
    change (∀ q : Q, q.val v = v) ↔ ∀ q ∈ Q, q v = v
    exact ⟨fun h q hq => h ⟨q, hq⟩, fun h q => h q.val q.property⟩
  have hc := hQ.card_modEq_card_fixedPoints (Space 5)
  rw [he] at hc
  change Nat.card (Space 5) ≡ Nat.card (fixedSpace Q) [MOD 5] at hc
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Space 5),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace Q)] at hc
  norm_num [Space] at hc
  have hd := Submodule.finrank_lt (fixedSpace_ne_top hQ0)
  norm_num [Space] at hd
  have hd1 : Module.finrank (ZMod 2) (fixedSpace Q) = 1 := by
    interval_cases hh : Module.finrank (ZMod 2) (fixedSpace Q) <;>
      first | rfl | norm_num [Nat.ModEq, hh] at hc
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hd1]
  norm_num

private abbrev invariantAction (Q : Subgroup (LinearGroup 5))
    (W : Submodule (ZMod 2) (Space 5)) (hW : Q ≤ parabolic W) : MulAction Q W where
  smul q w := ⟨q.val w.val, (hW q.property w.val).mpr w.property⟩
  one_smul _ := Subtype.ext rfl
  mul_smul _ _ _ := Subtype.ext rfl

private theorem invariant_card_residue (Q : Subgroup (LinearGroup 5))
    (hQ : IsPGroup 5 Q) (hc : Nat.card (fixedSpace Q) = 2)
    (W : Submodule (ZMod 2) (Space 5)) (hW : Q ≤ parabolic W) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ 2 ∧ Nat.card W ≡ n [MOD 5] ∧
      (fixedSpace Q ≤ W → n = 2) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : MulAction Q W := invariantAction Q W hW
  let toFixed : MulAction.fixedPoints Q W → fixedSpace Q := fun x =>
    ⟨x.val.val, fun q hq => congrArg Subtype.val
      ((MulAction.mem_fixedPoints.mp x.property) ⟨q, hq⟩)⟩
  have hinj : Function.Injective toFixed := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : fixedSpace Q => x.val) he
  have hle := Nat.card_le_card_of_injective toFixed hinj
  rw [hc] at hle
  have hz : (0 : W) ∈ MulAction.fixedPoints Q W := by
    rw [MulAction.mem_fixedPoints]
    intro q
    apply Subtype.ext
    exact q.val.map_zero
  let : Nonempty (MulAction.fixedPoints Q W) := ⟨⟨0, hz⟩⟩
  refine ⟨Nat.card (MulAction.fixedPoints Q W), Nat.card_pos, hle,
    hQ.card_modEq_card_fixedPoints W, ?_⟩
  intro hcontain
  let fromFixed : fixedSpace Q → MulAction.fixedPoints Q W := fun x =>
    ⟨⟨x.val, hcontain x.property⟩, MulAction.mem_fixedPoints.mpr (fun q =>
      Subtype.ext (x.property q.val q.property))⟩
  have hinj' : Function.Injective fromFixed := by
    intro x y he
    apply Subtype.ext
    exact congrArg (fun x : MulAction.fixedPoints Q W => x.val.val) he
  have hge := Nat.card_le_card_of_injective fromFixed hinj'
  rw [hc] at hge
  omega

/-- The cut index records the dimension minus one. -/
theorem finrank_flagSpace (b : FiveBasis) (i : Fin 4) :
    Module.finrank (ZMod 2) (flagSpace b i) = i.val + 1 := by
  classical
  have he : b '' {j : Fin 5 | j.val ≤ i.val} =
      Set.range (fun j : {j : Fin 5 // j.val ≤ i.val} => b j.val) := by
    ext x
    simp
  have hlin : LinearIndependent (ZMod 2)
      (fun j : {j : Fin 5 // j.val ≤ i.val} => b j.val) :=
    b.linearIndependent.comp _ Subtype.val_injective
  rw [flagSpace, he, finrank_span_eq_card hlin]
  fin_cases i <;> decide

/-- The subspace at cut `i` has exactly `2 ^ (i + 1)` vectors. -/
theorem natCard_flagSpace (b : FiveBasis) (i : Fin 4) :
    Nat.card (flagSpace b i) = 2 ^ (i.val + 1) := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), finrank_flagSpace]
  norm_num

/-- Divisibility by five excludes every proper flag type except a single endpoint. -/
theorem cuts_eq_singleton_end_of_five_dvd (b : FiveBasis) (cuts : Set (Fin 4))
    (hproper : flagStabilizer b cuts ≠ ⊤) (hfive : 5 ∣ Nat.card (flagStabilizer b cuts)) :
    cuts = {0} ∨ cuts = {3} := by
  classical
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 5 hfive
  let Q : Subgroup (LinearGroup 5) := zpowers g.val
  have hQc : Nat.card Q = 5 := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective (flagStabilizer b cuts).subtype Subtype.val_injective g).trans hg
  have hQ : IsPGroup 5 Q := IsPGroup.of_card (n := 1) (by simpa using hQc)
  have hQ0 : Q ≠ ⊥ := by
    intro he
    rw [he, Subgroup.card_bot] at hQc
    omega
  have hQP : Q ≤ flagStabilizer b cuts := zpowers_le.mpr g.property
  have hc := fixedSpace_card_two Q hQ hQ0
  have hQcut (i : Fin 4) (hi : i ∈ cuts) : Q ≤ parabolic (flagSpace b i) := by
    intro q hq
    exact (mem_flagStabilizer_iff b cuts q).mp (hQP hq) i hi
  have hends (i : Fin 4) (hi : i ∈ cuts) : i = 0 ∨ i = 3 := by
    obtain ⟨n, hn1, hn2, hn, _⟩ := invariant_card_residue Q hQ hc _ (hQcut i hi)
    rw [natCard_flagSpace] at hn
    fin_cases i
    · exact Or.inl rfl
    · norm_num [Nat.ModEq] at hn
      omega
    · norm_num [Nat.ModEq] at hn
      omega
    · exact Or.inr rfl
  have hnotboth : ¬ (0 ∈ cuts ∧ 3 ∈ cuts) := by
    rintro ⟨h0, h3⟩
    have hline : Submodule.span (ZMod 2) {b 0} ≤ fixedSpace Q := by
      rw [Submodule.span_singleton_le_iff_mem]
      intro q hq
      have hp := hQcut 0 h0 hq
      rw [flagSpace_zero, pointParabolic_eq_stabilizer (b.ne_zero 0)] at hp
      exact hp
    have hlineeq : fixedSpace Q = Submodule.span (ZMod 2) {b 0} := by
      symm
      apply Submodule.eq_of_le_of_finrank_le hline
      have hcard := hc
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2)] at hcard
      norm_num at hcard
      have hd : Module.finrank (ZMod 2) (fixedSpace Q) = 1 := by
        apply Nat.pow_right_injective (by decide : 1 < 2)
        simpa using hcard
      rw [hd, finrank_span_singleton (b.ne_zero 0)]
    have hcontain : fixedSpace Q ≤ flagSpace b 3 := by
      rw [hlineeq, Submodule.span_singleton_le_iff_mem, basis_mem_flagSpace_iff]
      decide
    obtain ⟨n, _, _, hn, hne⟩ := invariant_card_residue Q hQ hc _ (hQcut 3 h3)
    rw [hne hcontain, natCard_flagSpace] at hn
    norm_num [Nat.ModEq] at hn
  have hnonempty : cuts.Nonempty := by
    by_contra hn
    have he : cuts = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    exact hproper (he ▸ flagStabilizer_empty b)
  obtain ⟨i, hi⟩ := hnonempty
  rcases hends i hi with rfl | rfl
  · left
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨hi, fun j hj => ?_⟩
    rcases hends j hj with he | rfl
    · exact he
    · exact (hnotboth ⟨hi, hj⟩).elim
  · right
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨hi, fun j hj => ?_⟩
    rcases hends j hj with rfl | he
    · exact (hnotboth ⟨hj, hi⟩).elim
    · exact he

end BinaryLinear.FiveFlagGeometry
