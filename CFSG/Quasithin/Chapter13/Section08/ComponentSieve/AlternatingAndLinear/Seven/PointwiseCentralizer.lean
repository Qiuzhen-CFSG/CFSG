module

public import Theory.Representation.BinaryPermutation.OffenderFixedSpace
public import Theory.Representation.BinaryOffender.SubspaceAction
import Mathlib.Tactic

/-!
# Pointwise centralizers of transvection fixed spaces on seven points

A permutation fixing every vector with equal coordinates at `a,b` fixes
all other points and can only exchange `a,b`. Since seven is odd, subtracting
the augmentation times the all-one vector transports this test to the core.
An injective equivariant copy of that core in a module therefore proves the
actual identity `C_H(C_E(a)) = ⟨a⟩` whenever the seven-point image of `a` is a
transposition. No group-family label or assumed centralizer identity is used.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.24, printed p.958 (1 March 2004 manuscript).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven
open BinaryPermutation Representation.BinaryOffender Subgroup

private theorem fixes_axis {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (a b : Ω) (g : Equiv.Perm Ω)
    (h : ∀ v : Full Ω, v a = v b → representation Ω g v = v) :
    g = 1 ∨ g = Equiv.swap a b := by
  have hout (i : Ω) (hia : i ≠ a) (hib : i ≠ b) : g i = i := by
    have he := congrFun (h (Pi.single i 1) (by simp [hia.symm, hib.symm])) (g i)
    simp only [representation_apply, Equiv.symm_apply_apply, Pi.single_eq_same] at he
    by_contra hn
    simp [hn] at he
  have ha : g a = a ∨ g a = b := by
    by_contra hn
    push Not at hn
    exact hn.1 (g.injective (hout (g a) hn.1 hn.2))
  rcases ha with ha | ha
  · left
    have hb : g b = b := by
      by_contra hb
      have hba : g b ≠ a := fun he => hb (he.trans (g.injective (he.trans ha.symm)).symm)
      exact hb (g.injective (hout (g b) hba hb))
    ext i
    by_cases hia : i = a
    · subst i; exact ha
    by_cases hib : i = b
    · subst i; exact hb
    exact hout i hia hib
  · right
    have hb : g b = a := by
      by_cases hab : a = b
      · simpa only [hab] using ha
      by_contra hb
      have hbb : g b ≠ b := fun he => hab (g.injective (ha.trans he.symm))
      exact hbb (g.injective (hout (g b) hb hbb))
    ext i
    by_cases hia : i = a
    · subst i; simpa using ha
    by_cases hib : i = b
    · subst i; simpa using hb
    simpa [Equiv.swap_apply_of_ne_of_ne hia hib] using hout i hia hib

private theorem fixes_core_axis (a b : Fin 7) (g : Equiv.Perm (Fin 7))
    (h : ∀ v : core (Fin 7), coreRepresentation _ (Equiv.swap a b) v = v →
      coreRepresentation _ g v = v) : g = 1 ∨ g = Equiv.swap a b := by
  apply fixes_axis a b g
  intro v hv
  let c := augmentation (Fin 7) v
  let u : core (Fin 7) := ⟨v - c • allOne (Fin 7), by
    change augmentation (Fin 7) _ = 0
    simp only [map_sub, map_smul, augmentation_allOne, Fintype.card_fin,
      show ((7 : ℕ) : ZMod 2) = 1 by decide, smul_eq_mul, mul_one, c, sub_self]⟩
  have hu : coreRepresentation _ (Equiv.swap a b) u = u := by
    apply Subtype.ext
    change representation _ (Equiv.swap a b) u.val = u.val
    apply (swap_fixed_iff a b _).mpr
    change v a - c * 1 = v b - c * 1
    rw [hv]
  have hg := congrArg Subtype.val (h u hu)
  change representation _ g (v - c • allOne _) = v - c • allOne _ at hg
  simpa only [map_sub, map_smul, permute_allOne, sub_left_inj] using hg


section
variable {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
  (ρ : Representation (ZMod 2) H E)

private theorem mem_cyclic_fixed (a : H) (v : E) :
    v ∈ fixedSpace ρ (zpowers a) ↔ ρ a v = v := by
  rw [zpowers_eq_closure, mem_fixedSpace_closure_iff]
  simp

/-- The pointwise centralizer identity for a module containing an actual
seven-point natural submodule, transported along the faithful group map. -/
theorem embedded_core_fixed_centralizer
    (φ : H →* Equiv.Perm (Fin 7)) (hφ : Function.Injective φ)
    (j : core (Fin 7) →ₗ[ZMod 2] E) (hj : Function.Injective j)
    (heq : ∀ g v, j (coreRepresentation _ (φ g) v) = ρ g (j v))
    (a : H) (ha : (φ a).IsSwap) :
    subspaceKernel ρ (fixedSpace ρ (zpowers a)) ⊤ = zpowers a := by
  obtain ⟨x, y, _, hxy⟩ := ha
  apply le_antisymm
  · intro g hg
    have hfix (v : core (Fin 7))
        (hv : coreRepresentation _ (Equiv.swap x y) v = v) :
        coreRepresentation _ (φ g) v = v := by
      apply hj
      rw [heq]
      apply hg.2
      apply (mem_cyclic_fixed ρ a _).mpr
      rw [← heq, hxy, hv]
    rcases fixes_core_axis x y (φ g) hfix with hg1 | hga
    · have : g = 1 := hφ (hg1.trans φ.map_one.symm)
      simp [this]
    · have : g = a := hφ (hga.trans hxy.symm)
      simp [this]
  · intro g hg
    exact ⟨mem_top _, fun v hv => hv ⟨g, hg⟩⟩

end

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven
