module
public import Theory.SpecificGroups.ONan.MatrixModel
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Int.GCD

/-!
# Normal-generation reductions for the concrete O'Nan model

A subgroup containing both defining generators is the whole matrix subgroup.
Cauchy's theorem then reduces simplicity to conjugate-power coverage of
prime-order elements and normal generation of the chosen representatives.
Finally, the relations b⁴ = (ab)¹¹ = 1 imply that killing a kills b.

The finite-group argument is also used in the existing Janko₄ simplicity
reduction; no order recognition or presentation-completeness assertion is used.
-/

namespace ONan

/-- Containing the two defining generators suffices for equality with the model. -/
public theorem subgroup_eq_top_of_generators_mem (H : Subgroup Model)
    (ha : generatorA ∈ H) (hb : generatorB ∈ H) : H = ⊤ := by
  have hmap : matrixSubgroup ≤ H.map matrixSubgroup.subtype := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases hx with hx | hx
    · exact hx ▸ ⟨generatorA, ha, rfl⟩
    · exact (Set.mem_singleton_iff.mp hx) ▸ ⟨generatorB, hb, rfl⟩
  apply top_unique
  intro x _
  obtain ⟨y, hy, hyx⟩ := hmap x.property
  exact (Subtype.ext hyx : y = x) ▸ hy

/-- The witnessed noncommutativity makes the model nontrivial. -/
public theorem model_nontrivial : Nontrivial Model := by
  obtain ⟨g, h, hne⟩ := exists_mul_ne_mul
  exact ⟨⟨g * h, h * g, hne⟩⟩

/-- Prime-order coverage and normal generation imply simplicity of this model. -/
public theorem simple_of_prime_representatives {ι : Type*} (r : ι → Model)
    (hcover : ∀ x : Model, (orderOf x).Prime →
      ∃ i k g, r i = g * x ^ k * g⁻¹)
    (hgenerate : ∀ i, Subgroup.normalClosure ({r i} : Set Model) = ⊤) :
    IsSimpleGroup Model := by
  let := model_nontrivial
  constructor
  intro N hN
  let : N.Normal := hN
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  right
  have : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hbot
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd
    (ne_of_gt (Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial N)))
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) p hpdvd
  have hxprime : (orderOf (x : Model)).Prime := by simpa using hx ▸ hp
  obtain ⟨i, k, g, hi⟩ := hcover x hxprime
  have hiN : r i ∈ N := hi ▸ hN.conj_mem _ (N.pow_mem x.property k) g
  have hle : Subgroup.normalClosure ({r i} : Set Model) ≤ N :=
    Subgroup.normalClosure_le_normal (by simpa using hiN)
  rw [hgenerate i] at hle
  exact top_unique hle

/-- Coprime quotient orders prove normal generation by the first generator. -/
public theorem normalClosure_generatorA_of_relations
    (hb4 : generatorB ^ 4 = 1) (hab11 : (generatorA * generatorB) ^ 11 = 1) :
    Subgroup.normalClosure ({generatorA} : Set Model) = ⊤ := by
  let N := Subgroup.normalClosure ({generatorA} : Set Model)
  have haN : generatorA ∈ N := Subgroup.subset_normalClosure (Set.mem_singleton _)
  apply subgroup_eq_top_of_generators_mem N haN
  let q := QuotientGroup.mk' N
  have hqa : q generatorA = 1 := (QuotientGroup.eq_one_iff _).mpr haN
  have hqb4 : q generatorB ^ 4 = 1 := by simpa using congrArg q hb4
  have hqb11 : q generatorB ^ 11 = 1 := by simpa [hqa] using congrArg q hab11
  exact (QuotientGroup.eq_one_iff _).mp
    ((pow_eq_one_iff_of_coprime (by decide : Nat.Coprime 4 11)).mp ⟨hqb4, hqb11⟩)

end ONan
