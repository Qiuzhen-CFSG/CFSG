module

public import Theory.SpecificGroups.Tits.AtlasRepresentation
public import Theory.SpecificGroups.Tits.FiniteSimple
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.Tactic.Group
/-!
# An elementary eight in the actual Tits presentation

Parrott's involutions s₂,s₄,s₆ commute: two relations say this directly,
and conjugation by r₈ gives the third pair. Their eight products are
independent, as detected by the images of point zero under the existing
ATLAS representation. Only this eight-element point calculation is reduced;
all group relations come from the checked presentation.
Source: Parrott (1972), §5, p.683; Aschbacher–Smith A.2.12, printed p.36.
-/

namespace Tits.TwoRank
private abbrev C2 := Multiplicative (ZMod 2)
private abbrev E := (C2 × C2) × C2

private def binaryHom {H : Type*} [Group H] (g : H) (hg : g ^ 2 = 1) : C2 →* H where
  toFun a := if a = 1 then 1 else g
  map_one' := by simp
  map_mul' a b := by
    have cases2 : ∀ x : C2, x = 1 ∨ x = Multiplicative.ofAdd 1 := by decide +kernel
    have hsum : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := rfl
    have hone : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide +kernel
    rcases cases2 a with rfl | rfl <;> rcases cases2 b with rfl | rfl <;>
      simp [hsum, hone, ← pow_two, hg]

private theorem binary_commute {H : Type*} [Group H] {a b : H}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : Commute a b) (x y : C2) :
    Commute (binaryHom a ha x) (binaryHom b hb y) := by
  change Commute (if x = 1 then 1 else a) (if y = 1 then 1 else b)
  split_ifs <;> simp [hab]

private def tripleHom {H : Type*} [Group H] (a b c : H)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1)
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c) : E →* H :=
  ((binaryHom a ha).noncommCoprod (binaryHom b hb) (binary_commute ha hb hab)).noncommCoprod
    (binaryHom c hc) (fun x y =>
      (binary_commute ha hc hac x.1 y).mul_left (binary_commute hb hc hbc x.2 y))


private abbrev a := parrottGenerator .s2
private abbrev b := parrottGenerator .s4
private abbrev c := parrottGenerator .s6
private theorem a_sq : a ^ 2 = 1 := by
  simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of] using
    parrott_generators_satisfy_relations .i_s2
private theorem b_sq : b ^ 2 = 1 := by
  simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of] using
    parrott_generators_satisfy_relations .i_s4
private theorem c_sq : c ^ 2 = 1 := by
  simpa only [parrottRelator, map_pow, FreeGroup.lift_apply_of] using
    parrott_generators_satisfy_relations .i_s6
private theorem commutes {G : Type*} [Group G] {x y : G}
    (h : x⁻¹ * y⁻¹ * x * y = 1) : Commute x y := by
  change x * y = y * x
  calc x * y = (y * x) * (x⁻¹ * y⁻¹ * x * y) := by group
       _ = y * x := by rw [h, mul_one]
private theorem ab : Commute a b := by
  apply commutes
  simpa only [parrottRelator, parrottCommutator, map_mul, map_inv,
    FreeGroup.lift_apply_of] using parrott_generators_satisfy_relations .iv_s2_s4
private theorem ac : Commute a c := by
  apply commutes
  simpa only [parrottRelator, parrottCommutator, map_mul, map_inv,
    FreeGroup.lift_apply_of] using parrott_generators_satisfy_relations .iv_s2_s6
private theorem bc : Commute b c := by
  let r := parrottGenerator .r8
  have hr : r ^ 2 = 1 := by
    simpa only [r, parrottRelator, map_pow, FreeGroup.lift_apply_of] using
      parrott_generators_satisfy_relations .i_r8
  have hi : r⁻¹ = r := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hr)
  have ha : r * a * r = c := by
    apply mul_inv_eq_one.mp
    simpa only [r, parrottRelator, map_mul, map_inv, FreeGroup.lift_apply_of] using
      parrott_generators_satisfy_relations .viii_s2
  have hb : r * b * r = b := by
    apply mul_inv_eq_one.mp
    simpa only [r, parrottRelator, map_mul, map_inv, FreeGroup.lift_apply_of] using
      parrott_generators_satisfy_relations .viii_s4
  have hc := ab.map (MulAut.conj r).toMonoidHom
  simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, hi, ha, hb]
    using hc.symm
private def embedding : E →* ParrottGroup := tripleHom a b c a_sq b_sq c_sq ab ac bc
private theorem image (x : E) :
    (parrottLift atlasParrottGenerator atlasParrottGenerator_satisfies_relations) (embedding x) =
      (if x.1.1 = 1 then 1 else atlasParrottGenerator .s2) *
      (if x.1.2 = 1 then 1 else atlasParrottGenerator .s4) *
      (if x.2 = 1 then 1 else atlasParrottGenerator .s6) := by
  simp only [embedding, tripleHom, MonoidHom.noncommCoprod_apply, binaryHom,
    MonoidHom.coe_mk, OneHom.coe_mk, map_mul]
  split_ifs <;> simp [a,b,c]
private theorem detected : ∀ x : E,
    ((if x.1.1 = 1 then 1 else atlasParrottGenerator .s2) *
      (if x.1.2 = 1 then 1 else atlasParrottGenerator .s4) *
      (if x.2 = 1 then 1 else atlasParrottGenerator .s6)) 0 = 0 → x = 1 := by
  decide +kernel
private theorem embedding_injective : Function.Injective embedding := by
  apply (MonoidHom.ker_eq_bot_iff embedding).mp
  apply eq_bot_iff.mpr
  intro x hx
  apply Subgroup.mem_bot.mpr
  apply detected
  have h := congrArg (fun g => (parrottLift atlasParrottGenerator atlasParrottGenerator_satisfies_relations) g 0) (MonoidHom.mem_ker.mp hx)
  simpa only [image, map_one, Equiv.Perm.one_apply] using h
/-- The literal Tits carrier contains an elementary abelian group of order eight. -/
public theorem three_le : 3 ≤ primeRank 2 ParrottGroup := by
  apply primeRank_ge_of_elementary_embedding (f := embedding)
  · exact (by decide +kernel : ∀ x : E, x ^ 2 = 1)
  · simp [E,C2,Nat.card_eq_fintype_card]
  · exact embedding_injective
end Tits.TwoRank
