module

public import CFSG.Quasithin.Defs
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Field sizes and fixed-group conventions for the PSL₂ branch

The field-size predicate retains exactly the numeric restrictions in F.6.18
(3)–(6) and (8): primes congruent to ±11 modulo 24, prime powers of degree
one or two congruent to ±7 modulo 16, and squares of primes congruent to
3 modulo 8. It records only field sizes; the actual component and extension
identifications are separate mathematical inputs.

The fixed-group condition uses the equalizer subgroup of each actual
automorphism and its own self-centralizing two-core. It transports across
group isomorphisms, including isomorphisms between different universes.
The elementary arithmetic reduction leaves prime fields and square fields
of residue nine modulo sixteen.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, F.6.18, printed
pp.309–310, and the component paragraph of 15.4.18, printed pp.1162–1163.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.LinearModels

/-- Only the field-size restrictions in the PSL₂ alternatives of F.6.18.
This predicate does not identify a group or an extension: case (8) of that
theorem separately requires its actual field automorphism. -/
def SourceFieldSize (q : ℕ) : Prop :=
  (q.Prime ∧ (q % 24 = 11 ∨ q % 24 = 13)) ∨
  (∃ p e : ℕ, p.Prime ∧ 1 ≤ e ∧ e ≤ 2 ∧ q = p ^ e ∧
    (q % 16 = 7 ∨ q % 16 = 9)) ∨
  (∃ p : ℕ, p.Prime ∧ p % 8 = 3 ∧ q = p ^ 2)

/-- The source's fixed-group condition, inside the actual fixed subgroup. -/
def CharacteristicTwoFixed {K A : Type*} [Group K] [Group A]
    (ρ : A →* MulAut K) : Prop :=
  ∀ a : A, a ≠ 1 → HasCharacteristicTwo (ρ a).fixedSubgroup

theorem characteristicTwoFixed_congr {K L A : Type*}
    [Group K] [Group L] [Group A] (e : K ≃* L) (ρ : A →* MulAut K)
    (h : CharacteristicTwoFixed ρ) :
    CharacteristicTwoFixed ((MulAut.congr e).toMonoidHom.comp ρ) := by
  intro a ha
  change HasCharacteristicTwo (MulAut.congr e (ρ a)).fixedSubgroup
  let f := MulAut.fixedSubgroupCongr e (ρ a)
  intro y hy
  have hx : f.symm y ∈ Subgroup.centralizer (pCore 2 (ρ a).fixedSubgroup : Set _) := by
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro x hx
    apply f.injective
    simpa only [map_mul, f.apply_symm_apply] using
      hy (f x) (pCore_map_iso 2 f ▸ Subgroup.mem_map_of_mem f.toMonoidHom hx)
  have hh := Subgroup.mem_map_of_mem f.toMonoidHom (h a ha hx)
  simpa only [pCore_map_iso, MulEquiv.coe_toMonoidHom, f.apply_symm_apply] using hh

/-- The retained exponent bounds reduce the numeric cases to prime fields or
square fields of residue nine. All group-extension data remains separate. -/
theorem sourceFieldSize_prime_or_square {q : ℕ} (h : SourceFieldSize q) :
    (q.Prime ∧ ((q % 24 = 11 ∨ q % 24 = 13) ∨ (q % 16 = 7 ∨ q % 16 = 9))) ∨
    ∃ p : ℕ, p.Prime ∧ q = p ^ 2 ∧ q % 16 = 9 := by
  rcases h with h | ⟨p, e, hp, he1, he2, hq, hm⟩ | ⟨p, hp, hm, hq⟩
  · exact Or.inl ⟨h.1, Or.inl h.2⟩
  · have he : e = 1 ∨ e = 2 := by omega
    rcases he with rfl | rfl
    · simp only [pow_one] at hq
      exact Or.inl ⟨by simpa [hq] using hp, Or.inr hm⟩
    · refine Or.inr ⟨p, hp, hq, ?_⟩
      rcases hm with h7 | h9
      · rw [hq, Nat.pow_mod] at h7
        have hb : p % 16 < 16 := Nat.mod_lt p (by decide)
        interval_cases h : p % 16 <;> simp at h7
      · exact h9
  · refine Or.inr ⟨p, hp, hq, ?_⟩
    have hm16 : p % 16 = 3 ∨ p % 16 = 11 := by omega
    rcases hm16 with h | h <;> rw [hq, Nat.pow_mod, h]

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.LinearModels
