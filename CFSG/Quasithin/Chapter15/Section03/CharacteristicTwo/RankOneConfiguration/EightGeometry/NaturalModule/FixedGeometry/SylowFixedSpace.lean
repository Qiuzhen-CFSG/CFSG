module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Basic
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Sylow
public import Theory.Representation.BinaryOffender.PermutationConjugacy

/-!
# The Sylow fixed line in the natural degree-eight module

The seven checked binary-tree generators force a fixed class to have a
representative constant on each four-point half. Modulo the all-one vector
there are at most two such classes. Sylow conjugacy transports this bound
to every Sylow two-subgroup of S₈.

This is the precise natural-module fact needed to exclude Z_S ≤ U_L in
the fixed-summand argument. All finite calculations use kernel reduction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.3.1–2 on
pp.83–84 and the fixed-space geometry in 15.3.32 on p.1133.
-/

@[expose] public section

open Subgroup BinaryPermutation
open Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.Offenders.Eight
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry

private theorem fixed_representative (f : Fin 8 → ZMod 2)
    (hf : ∀ i : Fin 7, ∃ c : ZMod 2, ∀ k,
      f ((sylowGenerators i)⁻¹ k) - f k = c) :
    ∀ k, f k = if k.val < 4 then f 0 else f 4 := by
  have h : ∀ f : Fin 8 → ZMod 2,
      (∀ i : Fin 7, ∃ c : ZMod 2, ∀ k,
        f ((sylowGenerators i)⁻¹ k) - f k = c) →
      ∀ k, f k = if k.val < 4 then f 0 else f 4 := by
    decide +kernel
  exact h f hf

private def halfVector : Full (Fin 8) := fun k => if k.val < 4 then 1 else 0

private theorem half_core : halfVector ∈ core (Fin 8) := by
  change (∑ i : Fin 8, halfVector i) = 0
  decide +kernel

private def halfNatural : natural (Fin 8) :=
  ⟨(constants (Fin 8)).mkQ halfVector, ⟨halfVector, half_core, rfl⟩⟩

private theorem canonical_fixed_cases (v : natural (Fin 8))
    (hv : v ∈ fixedSpace (naturalRepresentation (Fin 8)) (canonicalSylow : Subgroup _)) :
    v = 0 ∨ v = halfNatural := by
  obtain ⟨f, hf, hfv⟩ := v.property
  have hfix (i : Fin 7) :
      (constants (Fin 8)).mkQ (representation (Fin 8) (sylowGenerators i) f) =
        (constants (Fin 8)).mkQ f := by
    have h := congrArg Subtype.val (hv ⟨sylowGenerators i, sylowGenerators_mem i⟩)
    change (deletedRepresentation (Fin 8) (sylowGenerators i)) v.val = v.val at h
    rw [← hfv] at h
    exact h
  have hform := fixed_representative f (fun i => by
    have hh := (Submodule.Quotient.eq (p := constants (Fin 8))).mp (hfix i)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hh
    refine ⟨c, fun k => ?_⟩
    have hk := congrFun hc k
    simpa only [allOne, Pi.smul_apply, smul_eq_mul, mul_one, Pi.sub_apply,
      representation_apply, Equiv.Perm.inv_def] using hk.symm)
  have hb : ∀ a b : ZMod 2, a = b ∨ a = b + 1 := by decide
  rcases hb (f 0) (f 4) with h | h
  · left
    apply Subtype.ext
    rw [← hfv]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.mem_span_singleton.mpr ⟨f 4, funext fun k => by
      simp only [Pi.smul_apply, allOne, smul_eq_mul, mul_one]
      rw [hform k, h]
      split_ifs <;> rfl⟩
  · right
    apply Subtype.ext
    rw [← hfv]
    apply (Submodule.Quotient.eq (p := constants (Fin 8))).mpr
    exact Submodule.mem_span_singleton.mpr ⟨f 4, funext fun k => by
      simp only [Pi.smul_apply, allOne, smul_eq_mul, mul_one, Pi.sub_apply, halfVector]
      rw [hform k, h]
      split_ifs <;> ring⟩

private theorem canonical_fixed_card_le_two :
    Nat.card (fixedSpace (naturalRepresentation (Fin 8)) (canonicalSylow : Subgroup _)) ≤ 2 := by
  classical
  let f : fixedSpace (naturalRepresentation (Fin 8)) (canonicalSylow : Subgroup _) → Bool :=
    fun v => decide (v.val = 0)
  have hi : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    rcases canonical_fixed_cases v.val v.property with hv | hv <;>
      rcases canonical_fixed_cases w.val w.property with hw | hw
    · exact hv.trans hw.symm
    · have hz : w.val = 0 := of_decide_eq_true (by simpa only [f, hv, decide_true] using he.symm)
      exact hv.trans hz.symm
    · have hz : v.val = 0 := of_decide_eq_true (by simpa only [f, hw, decide_true] using he)
      exact hz.trans hw.symm
    · exact hv.trans hw.symm
  simpa using Nat.card_le_card_of_injective f hi

/-- Every Sylow two-subgroup fixes at most one binary dimension in the natural S₈-module. -/
theorem natural_sylow_fixed_card_le_two (P : Sylow 2 (Equiv.Perm (Fin 8))) :
    Nat.card (fixedSpace (naturalRepresentation (Fin 8)) (P : Subgroup _)) ≤ 2 := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Equiv.Perm (Fin 8)) canonicalSylow P
  have he : (P : Subgroup (Equiv.Perm (Fin 8))) =
      (canonicalSylow : Subgroup _).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rfl
  rw [he, ← Nat.card_congr (fixedSpaceConjEquiv (naturalRepresentation (Fin 8))
    (canonicalSylow : Subgroup _) g).toEquiv]
  exact canonical_fixed_card_le_two

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry

end
