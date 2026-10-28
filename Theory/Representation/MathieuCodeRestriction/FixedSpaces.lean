module

public import Theory.Representation.MathieuCodeRestriction.CycleNorm
public import Theory.Mathieu.M24.Properties.Simplicity
public import Theory.Representation.BinaryOffender.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finiteness

/-!
# Faithfulness and fixed spaces of the Mathieu quotients

The odd norm from a native 23-cycle vanishes on both eleven-dimensional
quotients. Hence their global fixed spaces are zero. Simplicity of the native
M₂₄ makes each nontrivial action faithful, and the fixed-point congruence for
a two-group gives a nonzero Sylow fixed vector on each binary space.

These are precisely the module inputs for E.4.3(2), independent of the
irreducibility and parameter tables in Chapter H.

Source: Aschbacher–Smith, E.4.3 (printed p.241), H.13.1 (printed p.395).
-/

public section
noncomputable section
open Sporadic.Mathieu
open scoped BigOperators
open Representation.BinaryOffender
namespace MathieuCode

instance code_finite : Finite Code := Finite.of_surjective _ codeLine.mkQ_surjective

instance cocode_finite : Finite Cocode := Finite.of_surjective _ codeInCore.mkQ_surjective

instance code_nontrivial : Nontrivial Code :=
  Module.nontrivial_of_finrank_pos (by rw [finrank_code]; decide)

instance cocode_nontrivial : Nontrivial Cocode :=
  Module.nontrivial_of_finrank_pos (by rw [finrank_cocode]; decide)

theorem code_sum_cycle (v : Code) :
    (∑ k : Fin 23, codeRepresentation (cycle23 ^ k.val) v) = 0 := by
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    change (∑ k : Fin 23, codeRepresentation (cycle23 ^ k.val) (codeLine.mkQ v)) = 0
    simp only [codeRepresentation_mk, ← map_sum]
    apply (Submodule.Quotient.mk_eq_zero codeLine).mpr
    change (∑ k : Fin 23, golayRepresentation (cycle23 ^ k.val) v).val ∈
      BinaryPermutation.constants (Fin 24)
    have he : (∑ k : Fin 23, golayRepresentation (cycle23 ^ k.val) v).val =
        cycleNorm v := by
      change golay.subtype (∑ k : Fin 23, golayRepresentation (cycle23 ^ k.val) v) = _
      rw [map_sum]
      rfl
    rw [he, cycleNorm_core ⟨v.val, golay_le_core v.property⟩]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

theorem cocode_sum_cycle (v : Cocode) :
    (∑ k : Fin 23, cocodeRepresentation (cycle23 ^ k.val) v) = 0 := by
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    change (∑ k : Fin 23, cocodeRepresentation (cycle23 ^ k.val) (codeInCore.mkQ v)) = 0
    simp only [cocodeRepresentation_mk, ← map_sum]
    apply (Submodule.Quotient.mk_eq_zero codeInCore).mpr
    change (∑ k : Fin 23, coreRepresentation (cycle23 ^ k.val) v).val ∈ golay
    have he : (∑ k : Fin 23, coreRepresentation (cycle23 ^ k.val) v).val =
        cycleNorm v := by
      change Core.subtype (∑ k : Fin 23, coreRepresentation (cycle23 ^ k.val) v) = _
      rw [map_sum]
      rfl
    rw [he, cycleNorm_core v]
    exact golay.smul_mem _ allOne_mem

private theorem invariants_eq_bot_of_sum_cycle
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) M24 V)
    (hn : ∀ v, (∑ k : Fin 23, ρ (cycle23 ^ k.val) v) = 0) :
    ρ.invariants = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  have h := hn v
  simp only [hv _, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2)] at h
  have h23 : (23 : ZMod 2) = 1 := by decide
  change (23 : ZMod 2) • v = 0 at h
  rw [h23, one_smul] at h
  exact h

theorem code_invariants_eq_bot : codeRepresentation.invariants = ⊥ :=
  invariants_eq_bot_of_sum_cycle codeRepresentation code_sum_cycle

theorem cocode_invariants_eq_bot : cocodeRepresentation.invariants = ⊥ :=
  invariants_eq_bot_of_sum_cycle cocodeRepresentation cocode_sum_cycle

private theorem faithful_of_invariants_eq_bot
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Nontrivial V]
    (ρ : Representation (ZMod 2) M24 V) (hz : ρ.invariants = ⊥) :
    Function.Injective ρ := by
  let : IsSimpleGroup M24 := m24_isSimpleGroup
  rcases ρ.normal_ker.eq_bot_or_eq_top with h | h
  · exact ρ.ker_eq_bot_iff.mp h
  · have he : ρ = 1 := MonoidHom.ker_eq_top_iff.mp h
    have ht : ρ.invariants = ⊤ := by
      ext v
      simp [he, Representation.mem_invariants]
    exact (bot_ne_top (hz.symm.trans ht)).elim

theorem code_faithful : Function.Injective codeRepresentation :=
  faithful_of_invariants_eq_bot codeRepresentation code_invariants_eq_bot

theorem cocode_faithful : Function.Injective cocodeRepresentation :=
  faithful_of_invariants_eq_bot cocodeRepresentation cocode_invariants_eq_bot

private theorem fixedSpace_sylow_ne_bot
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) M24 V) (hc : 2 ∣ Nat.card V) (S : Sylow 2 M24) :
    fixedSpace ρ (S : Subgroup M24) ≠ ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : MulAction S V := {
    smul s v := ρ s.val v
    one_smul v := by change ρ 1 v = v; simp
    mul_smul s t v := by change ρ (s.val * t.val) v = ρ s.val (ρ t.val v); simp
  }
  have hzero : (0 : V) ∈ MulAction.fixedPoints S V := by
    intro s
    exact map_zero (ρ s.val)
  obtain ⟨v, hv, hne⟩ :=
    S.isPGroup'.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hc hzero
  intro hb
  have hmem : v ∈ fixedSpace ρ (S : Subgroup M24) := hv
  rw [hb, Submodule.mem_bot] at hmem
  exact hne hmem.symm

private theorem fixedSpace_top_eq_bot
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) M24 V) (hz : ρ.invariants = ⊥) :
    fixedSpace ρ ⊤ = ⊥ := by
  have he : fixedSpace ρ ⊤ = ρ.invariants := by
    ext v
    change (∀ g : (⊤ : Subgroup M24), ρ g.val v = v) ↔ ∀ g : M24, ρ g v = v
    exact ⟨fun h g => h ⟨g, Subgroup.mem_top g⟩, fun h g => h g.val⟩
  exact he.trans hz

theorem code_fixedSpace_lt_sylow (S : Sylow 2 M24) :
    fixedSpace codeRepresentation ⊤ < fixedSpace codeRepresentation (S : Subgroup M24) := by
  rw [fixedSpace_top_eq_bot codeRepresentation code_invariants_eq_bot]
  apply bot_lt_iff_ne_bot.mpr
  apply fixedSpace_sylow_ne_bot codeRepresentation _ S
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, finrank_code]
  decide

theorem cocode_fixedSpace_lt_sylow (S : Sylow 2 M24) :
    fixedSpace cocodeRepresentation ⊤ < fixedSpace cocodeRepresentation (S : Subgroup M24) := by
  rw [fixedSpace_top_eq_bot cocodeRepresentation cocode_invariants_eq_bot]
  apply bot_lt_iff_ne_bot.mpr
  apply fixedSpace_sylow_ne_bot cocodeRepresentation _ S
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, finrank_cocode]
  decide
end MathieuCode
