module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.OrderData
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.SecondOrbits.Coverage
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion.Orbit
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.Seed
import Mathlib.Tactic.FinCases

/-!
# Order of the fixed first Hall--Janko parabolic

The existing normal forms are proved to be carrier elements, using checked
words for the strong generators. Successive evaluation at points 0, 1, 2,
and 3 proves uniqueness. Together with the existing coverage theorem this
gives a bijection of the actual ATLAS carrier with 100 × 63 × 24 × 4 indices.
The already certified centralizer index 315 then gives order 1920 for the
literal subgroup `Seed.l₁`. No comparison with the icosian model is used.

Source: retained ATLAS J2G1-p100B0 data, the certified SecondOrbits normal
forms and FirstFusion conjugacy orbit; Aschbacher--Smith F.1.12(I)(10), p.263.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic
open Theory.GroupTheory GeneratorPair GeneratorPair.SecondOrbitCertificate OrderData

private theorem localWord_inclusion (w : List (Fin 3)) :
    inclusion (Seed.localWord w) = evalWord ![tableA, tableB, tableB⁻¹] w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change inclusion (![a, b, b⁻¹] i * Seed.localWord w) = _
    rw [map_mul, ih]
    congr 1
    fin_cases i <;> simp [a, b, inclusion, generatorA_eq_table, generatorB_eq_table]

private theorem gen0_mem (i : Fin 13) : gen0 i ∈ generated := by
  have h : inclusion (Seed.localWord (strongWord i)) = gen0 i :=
    (localWord_inclusion _).trans (Equiv.ext (strongWord_check i))
  exact h ▸ (Seed.localWord (strongWord i)).property

private theorem word_mem {n : Nat} (gs : Fin n → Equiv.Perm (Fin 100))
    (hg : ∀ i, gs i ∈ generated) (w : List (Fin n)) : evalWord gs w ∈ generated := by
  induction w with
  | nil => exact generated.one_mem
  | cons i w ih => exact generated.mul_mem (hg i) ih

theorem normalForm_mem (i : Index) : normalForm i ∈ generated := by
  apply generated.mul_mem
  · apply generated.mul_mem
    · apply generated.mul_mem
      · rw [rep0_eq_word]
        exact word_mem gen0 gen0_mem _
      · rw [rep1_eq_word]
        exact word_mem gen1 (fun j => gen1_eq_gen0 j ▸ gen0_mem _) _
    · rw [rep2_eq_word]
      exact word_mem gen2 (fun j => gen2_eq_gen0 j ▸ gen0_mem _) _
  · rw [rep3_eq_word]
    exact word_mem gen3 (fun j => gen3_eq_gen0 j ▸ gen0_mem _) _

theorem normalForm_injective : Function.Injective normalForm := by
  rintro ⟨i₀, i₁, i₂, i₃⟩ ⟨j₀, j₁, j₂, j₃⟩ h
  have h₀ := congrArg (fun p : Equiv.Perm (Fin 100) => decode0 (p 0)) h
  simp only [normalForm, Equiv.Perm.mul_apply, rep3_fix0, rep2_fix0, rep1_fix0,
    decode0_spec] at h₀
  subst j₀
  change rep0 i₀ * rep1 i₁ * rep2 i₂ * rep3 i₃ =
    rep0 i₀ * rep1 j₁ * rep2 j₂ * rep3 j₃ at h
  simp only [mul_assoc] at h
  have h := mul_left_cancel h
  have h₁ := congrArg (fun p : Equiv.Perm (Fin 100) => decode1 (p 1)) h
  simp only [Equiv.Perm.mul_apply, rep3_fix1, rep2_fix1, decode1_spec] at h₁
  subst j₁
  have h := mul_left_cancel h
  have h₂ := congrArg (fun p : Equiv.Perm (Fin 100) => decode2 (p 2)) h
  simp only [Equiv.Perm.mul_apply, rep3_fix2, decode2_spec] at h₂
  subst j₂
  have h := mul_left_cancel h
  have h₃ := congrArg (fun p : Equiv.Perm (Fin 100) => decode3 (p 3)) h
  simp only [decode3_spec] at h₃
  subst j₃
  rfl

noncomputable def carrierEquivNormalForms : Carrier ≃ Index :=
  (Equiv.ofBijective (fun i => (⟨normalForm i, normalForm_mem i⟩ : Carrier))
    ⟨fun _ _ h => normalForm_injective (congrArg Subtype.val h), fun x => by
      obtain ⟨i, hi⟩ := normalForm_cover x
      exact ⟨i, Subtype.ext hi.symm⟩⟩).symm

theorem card_carrier : Nat.card Carrier = 604800 := by
  rw [Nat.card_congr carrierEquivNormalForms]
  simp

set_option maxRecDepth 4000 in
theorem card_l₁ : Nat.card Seed.l₁ = 1920 := by
  have h := Seed.l₁.card_mul_index
  have hi : Seed.l₁.index = 315 := FirstFusion.centralizer_index
  rw [hi, card_carrier] at h
  omega

end Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic
