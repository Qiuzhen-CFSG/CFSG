module

public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.FinCases

/-!
# The full binary transvection image

An action whose displacements lie in a fixed nonzero line has a linear
functional attached to each actor. These functionals form a binary subspace
of the dual. If the common fixed space is exactly the line, their common
annihilator is that line, so finite duality proves that every functional
vanishing on the line occurs. Thus each entire transvection is realized by
one actor, not just its value at a chosen vector.

This supplies the full-image step in Aschbacher–Smith, *The Classification
of Quasithin Groups*, combined manuscript (1 March 2004), Lemma 12.8.11(3),
printed p.854. The ambient group and quotient geometry are handled by its
source consumer.
-/

public section
namespace BinaryTransvection
variable {A M : Type*} [Group A] [AddCommGroup M] [Module (ZMod 2) M]

/-- Finite binary duality upgrades the common fixed-space calculation to the
whole transvection group, with one actor realizing each entire functional. -/
theorem full_action_of_fixed_space
    (ρ : A →* (M ≃ₗ[ZMod 2] M)) (E : Submodule (ZMod 2) M)
    [FiniteDimensional (ZMod 2) E]
    (v : E) (hv : (v : M) ≠ 0)
    (hmove : ∀ (a : A) (e : E), ρ a e - e ∈ Submodule.span (ZMod 2) {(v : M)})
    (hfixed : ∀ e : E, (∀ a : A, ρ a e = (e : M)) ↔
      e ∈ Submodule.span (ZMod 2) {v}) :
    (∀ a : A, ∃ φ : Module.Dual (ZMod 2) E, φ v = 0 ∧
      ∀ e : E, ρ a e = (e : M) + φ e • (v : M)) ∧
    (∀ φ : Module.Dual (ZMod 2) E, φ v = 0 →
      ∃ a : A, ∀ e : E, ρ a e = (e : M) + φ e • (v : M)) := by
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hv
  let c (a : A) : Module.Dual (ZMod 2) E :=
    l.comp (((ρ a).toLinearMap.comp E.subtype) - E.subtype)
  have ceval (a : A) (e : E) : c a e = l (ρ a e - e) := rfl
  have heval (a : A) (e : E) : ρ a e = (e : M) + c a e • (v : M) := by
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (hmove a e)
    have hc : c a e = t := by rw [ceval, ← ht, map_smul, hl, smul_eq_mul, mul_one]
    rw [hc, ht]
    abel
  have hvfix (a : A) : ρ a v = (v : M) :=
    (hfixed v).mpr (Submodule.mem_span_singleton_self v) a
  have cv (a : A) : c a v = 0 := by rw [ceval, hvfix, sub_self, map_zero]
  have cone : c 1 = 0 := by ext e; simp [ceval]
  have cmul (a b : A) : c (a*b) = c a + c b := by
    ext e
    rw [ceval, map_mul]
    change l (ρ a (ρ b e) - e) = _
    rw [heval b e, map_add, map_smul, hvfix, heval a e]
    have he : ((e : M) + c a e • (v : M) + c b e • (v : M)) - e =
        c a e • (v : M) + c b e • (v : M) := by abel
    rw [he, map_add, map_smul, map_smul, hl]
    simp only [smul_eq_mul, mul_one, LinearMap.add_apply]
  let C : Submodule (ZMod 2) (Module.Dual (ZMod 2) E) := {
    carrier := Set.range c
    zero_mem' := ⟨1, cone⟩
    add_mem' := by
      rintro f g ⟨a, rfl⟩ ⟨b, rfl⟩
      exact ⟨a*b, cmul a b⟩
    smul_mem' := by
      rintro t f ⟨a, rfl⟩
      fin_cases t
      · refine ⟨1, ?_⟩
        change c 1 = (0 : ZMod 2) • c a
        simpa only [zero_smul] using cone
      · refine ⟨a, ?_⟩
        change c a = (1 : ZMod 2) • c a
        rw [one_smul] }
  have hC : C.dualCoannihilator = Submodule.span (ZMod 2) {v} := by
    ext e
    rw [Submodule.mem_dualCoannihilator]
    rw [← hfixed]
    constructor
    · intro he a
      rw [heval, he (c a) ⟨a, rfl⟩, zero_smul, add_zero]
    · intro he f hf
      obtain ⟨a, rfl⟩ := hf
      rw [ceval, he, sub_self, map_zero]
  constructor
  · intro a
    exact ⟨c a, cv a, heval a⟩
  · intro φ hφ
    have hmem : φ ∈ C := by
      rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := C), hC]
      rw [Submodule.mem_dualAnnihilator]
      intro e he
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp he
      rw [map_smul, hφ, smul_zero]
    obtain ⟨a, ha⟩ := hmem
    exact ⟨a, fun e => by rw [← ha]; exact heval a e⟩

end BinaryTransvection
