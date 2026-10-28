module
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourSingular
public import Theory.GroupAction.FiveActionMinimalOrder
public import Theory.Representation.BinaryGroupAction
/-!
# A singular plane excludes order-five isometries in binary dimension four

A nontrivial five-action on the sixteen-element additive group fixes only
zero. Its action on the ten zeros of the original form therefore contradicts
orbit counting modulo five. The representation and singular plane are the
caller's actual ones. Source application: Aschbacher--Smith 14.3.15.
-/
public section
open Module
namespace QuadraticForm.BinaryFour
variable {V A : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] [Group A] [Finite A]

/-- A faithful order-five action cannot preserve a nondegenerate four-form
with a singular plane. -/
theorem false_of_card_five (ρ : Representation (ZMod 2) A V)
    (hf : Function.Injective ρ) (hA : Nat.card A = 5)
    (Q : QuadraticForm (ZMod 2) V) (hQ : Q.polarBilin.Nondegenerate)
    (hd : finrank (ZMod 2) V = 4) (E : Submodule (ZMod 2) V)
    (hE : finrank (ZMod 2) E = 2) (hs : ∀ e ∈ E, Q e = 0)
    (hi : ∀ a v, Q (ρ a v) = Q v) : False := by
  classical
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : MulDistribMulAction A (Multiplicative V) := Representation.BinaryGroupAction.action ρ
  have hcard : Nat.card (Multiplicative V) = 16 := by
    change Nat.card V = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd]
    decide
  have hmove : FixedPoints.subgroup A (Multiplicative V) ≠ ⊤ := by
    intro ht
    have hg (a : A) : a = 1 := by
      apply hf
      ext v
      have hv : Multiplicative.ofAdd v ∈ FixedPoints.subgroup A (Multiplicative V) :=
        ht ▸ Subgroup.mem_top _
      have hh : ρ a v = v := congrArg Multiplicative.toAdd (hv a)
      simpa using hh
    have hc := Nat.card_eq_one_iff_exists.mpr ⟨(1 : A),hg⟩
    omega
  have hfixed := Theory.GroupAction.fixed_eq_bot_of_five_action_card_sixteen hA hcard hmove
  let Z := {v : V // Q v = 0}
  let : MulAction A Z := {
    smul := fun (a : A) (v : Z) => ⟨ρ a v, (hi a v).trans v.property⟩
    one_smul := by
      intro v
      apply Subtype.ext
      change ρ 1 v.val = v.val
      simp
    mul_smul := by
      intro a b v
      apply Subtype.ext
      change ρ (a * b) v.val = ρ a (ρ b v.val)
      rw [ρ.map_mul,Module.End.mul_apply] }
  have hzero : (⟨0, Q.map_zero⟩ : Z) ∈ MulAction.fixedPoints A Z := by
    intro a
    exact Subtype.ext ((ρ a).map_zero)
  have hz (x : MulAction.fixedPoints A Z) : x = ⟨⟨0,Q.map_zero⟩,hzero⟩ := by
    apply Subtype.ext
    apply Subtype.ext
    have hx : Multiplicative.ofAdd x.val.val ∈ FixedPoints.subgroup A (Multiplicative V) := by
      intro a
      exact congrArg (fun z : Z => Multiplicative.ofAdd z.val) (x.property a)
    rw [hfixed] at hx
    exact congrArg Multiplicative.toAdd (Subgroup.mem_bot.mp hx)
  have hc : Nat.card (MulAction.fixedPoints A Z) = 1 :=
    Nat.card_eq_one_iff_exists.mpr ⟨⟨⟨0,Q.map_zero⟩,hzero⟩,hz⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hp : IsPGroup 5 A := IsPGroup.of_card (p := 5) (n := 1) (by simpa using hA)
  have hm := hp.card_modEq_card_fixedPoints Z
  rw [hc,card_zero_of_singular_plane Q hQ hd E hE hs] at hm
  norm_num [Nat.ModEq] at hm

/-- An actor preserving such a form has order prime to five. -/
theorem not_five_dvd_card (ρ : Representation (ZMod 2) A V)
    (hf : Function.Injective ρ)
    (Q : QuadraticForm (ZMod 2) V) (hQ : Q.polarBilin.Nondegenerate)
    (hd : finrank (ZMod 2) V = 4) (E : Submodule (ZMod 2) V)
    (hE : finrank (ZMod 2) E = 2) (hs : ∀ e ∈ E, Q e = 0)
    (hi : ∀ a v, Q (ρ a v) = Q v) : ¬5 ∣ Nat.card A := by
  intro hh
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 5 hh
  exact false_of_card_five (ρ.comp (Subgroup.zpowers a).subtype)
    (hf.comp (Subgroup.zpowers a).subtype_injective)
    ((Nat.card_zpowers a).trans ha) Q hQ hd E hE hs (fun b v => hi b v)
end QuadraticForm.BinaryFour
