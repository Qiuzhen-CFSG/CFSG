module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.Contracts
public import Theory.Representation.PSL3Three.AbsoluteDegrees.Saturation
import Lean.Elab.Tactic.Omega

/-!
# Completeness reduction for the absolute M₂₄ spectrum through degree 48

Adjoin the trivial representation to four small and eight larger pairwise
inequivalent simple modules. Dimension separates the three families. The
modular trace-independence bound then proves exhaustion from an upper bound
of thirteen on the actual odd-order conjugacy classes. Faithfulness excludes
degree one: the two native standard generators do not commute.

For the finite-field consumer, genuine scalar extension to an algebraic
closure preserves degree and faithfulness. Absolute irreducibility gives
irreducibility there. This discharges the transfer and completeness argument;
the two model constructions and the conjugacy-class bound remain explicit
unproved inputs. In particular this file does not yet assert
`absoluteSmallSpectrum`.

Source: Guralnick–Malle, Classification of 2F-modules I, Proposition 5.1,
M₂₄ paragraph, manuscript p.17; James, The modular characters of the
Mathieu groups, J. Algebra 27 (1973), 57–111.
-/

public section
open scoped TensorProduct
namespace Representation.Mathieu.M24DegreeSpectrum
open Sporadic.Mathieu
universe v

namespace AbsoluteSpectrum

/-- Degree one is incompatible with faithfulness on the actual M₂₄ carrier.
Only the two certified native generators are needed. -/
theorem faithful_finrank_ne_one
    {F W : Type*} [Field F] [AddCommGroup W] [Module F W]
    (σ : Representation F M24 W) (hf : Function.Injective σ) :
    Module.finrank F W ≠ 1 := by
  intro hd
  let x : M24 := ⟨m24GeneratorA, m24GeneratorA_mem⟩
  let y : M24 := ⟨m24GeneratorB, m24GeneratorB_mem⟩
  obtain ⟨a, ha, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hd (σ x)
  obtain ⟨b, hb, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hd (σ y)
  have he : σ (y * x) = σ (x * y) := by
    rw [map_mul, map_mul, ha, hb]
    simp [smul_smul, mul_comm]
  have hp := congrArg (fun g : M24 => g.val 1) (hf he)
  exact (by decide +kernel :
    (m24GeneratorB * m24GeneratorA) (1 : Fin 24) ≠
      (m24GeneratorA * m24GeneratorB) (1 : Fin 24)) hp

private abbrev CandidateIndex := Option (Fin 4 ⊕ Fin 8)

/-- Concrete simple families and the odd-order class bound imply the entire
closed-field small spectrum. Exhaustion is proved, not assumed. -/
theorem small_degree_of_families
    {F W : Type v} [Field F] [IsAlgClosed F] [CharP F 2]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (d : Fin 4 → ℕ) (e : Fin 8 → ℕ)
    (ρ : ∀ i, Representation F M24 (Fin (d i) → F))
    (π : ∀ i, Representation F M24 (Fin (e i) → F))
    [∀ i, IsIrreducible (ρ i)] [∀ i, IsIrreducible (π i)]
    (hρ : Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j)))
    (hπ : Pairwise fun i j => IsEmpty ((π i).Equiv (π j)))
    (hd : ∀ i, d i = 11 ∨ d i = 44) (he : ∀ i, 48 < e i)
    (hclasses : OddClassBound)
    (σ : Representation F M24 W) [σ.IsIrreducible]
    (hf : Function.Injective σ) (hW : Module.finrank F W ≤ 48) :
    Module.finrank F W = 11 ∨ Module.finrank F W = 44 := by
  classical
  let V : CandidateIndex → Type v := fun i =>
    match i with
    | none => F
    | some (.inl j) => Fin (d j) → F
    | some (.inr j) => Fin (e j) → F
  let addV : ∀ i, AddCommGroup (V i) := fun i => by
    rcases i with _ | (i | i) <;> dsimp [V] <;> infer_instance
  let modV : ∀ i, Module F (V i) := fun i => by
    rcases i with _ | (i | i) <;> dsimp [V] <;> infer_instance
  let rep : ∀ i, Representation F M24 (V i) := fun i =>
    match i with
    | none => Representation.trivial F M24 F
    | some (.inl j) => ρ j
    | some (.inr j) => π j
  have finV : ∀ i, FiniteDimensional F (V i) := by
    intro i
    rcases i with _ | (i | i) <;> dsimp [V] <;> infer_instance
  have irr : ∀ i, IsIrreducible (rep i) := by
    intro i
    rcases i with _ | (i | i)
    · change IsIrreducible (Representation.trivial F M24 F)
      constructor
      intro S
      rcases IsSimpleOrder.eq_bot_or_eq_top S.toSubmodule with h | h
      · exact Or.inl (Subrepresentation.toSubmodule_injective h)
      · exact Or.inr (Subrepresentation.toSubmodule_injective h)
    all_goals dsimp [rep]; infer_instance
  have hdistinct : Pairwise fun i j => IsEmpty ((rep i).Equiv (rep j)) := by
    intro i j hij
    constructor
    intro E
    have hdim := E.toLinearEquiv.finrank_eq
    rcases i with _ | (i | i) <;> rcases j with _ | (j | j)
    · exact hij rfl
    · simp only [V, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
        Fintype.card_fin] at hdim
      have := hd j
      omega
    · simp only [V, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
        Fintype.card_fin] at hdim
      have := he j
      omega
    · simp only [V, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
        Fintype.card_fin] at hdim
      have := hd i
      omega
    · exact (hρ (fun h => hij (congrArg (fun k => some (Sum.inl k)) h))).false E
    · simp only [V, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdim
      have := hd i
      have := he j
      omega
    · simp only [V, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
        Fintype.card_fin] at hdim
      have := he i
      omega
    · simp only [V, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdim
      have := he i
      have := hd j
      omega
    · exact (hπ (fun h => hij (congrArg (fun k => some (Sum.inr k)) h))).false E
  have hc : Nat.card CandidateIndex = 13 := by
    simp [CandidateIndex, Nat.card_eq_fintype_card]
  obtain ⟨i, ⟨E⟩⟩ := exists_equiv_of_pRegular_class_bound V rep 2 hdistinct
    (hc ▸ hclasses) σ
  have hdim := E.toLinearEquiv.finrank_eq
  rcases i with _ | (i | i)
  · simp only [V, Module.finrank_self] at hdim
    exact (faithful_finrank_ne_one σ hf hdim).elim
  · simp only [V, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdim
    exact hdim ▸ hd i
  · simp only [V, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdim
    have := he i
    omega

end AbsoluteSpectrum

/-- The actual finite-field contract follows by genuine scalar extension from
the two independent model constructions and the odd-order class bound.
Final assembly must still supply all three inputs. -/
theorem absoluteSmallSpectrum_of_models
    (hsmall : AbsoluteSpectrum.SmallModelsExist.{v})
    (hlarge : AbsoluteSpectrum.LargeModelsExist.{v})
    (hclasses : AbsoluteSpectrum.OddClassBound) : AbsoluteSmallSpectrum.{v} := by
  intro K _ _ _ W _ _ _ σ hf ha hd
  let F := AlgebraicClosure K
  obtain ⟨d, ρ, hirrρ, hρ, hdρ⟩ := hsmall F
  obtain ⟨e, π, hirrπ, hπ, hdπ⟩ := hlarge F
  let := hirrρ
  let := hirrπ
  let := ha.irreducible_of_closure
  have hf' := (extendScalars_faithful_iff F σ).mp hf
  have hd' : Module.finrank F (F ⊗[K] W) ≤ 48 := by
    simpa only [Module.finrank_baseChange] using hd
  have h := AbsoluteSpectrum.small_degree_of_families d e ρ π hρ hπ hdρ hdπ
    hclasses (extendScalars F σ) hf' hd'
  simpa only [Module.finrank_baseChange] using h

end Representation.Mathieu.M24DegreeSpectrum
