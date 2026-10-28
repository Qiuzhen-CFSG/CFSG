module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.Degree.SmallSpectrum.Inputs
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.Degree.SmallSpectrum.SmallModels
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.Degree.SmallSpectrum.LargeModels
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.Degree.SmallSpectrum.OddClasses
public import Theory.Representation.SplitSimpleCatalogue

/-!
# Assembly of the bounded binary A₇ degree spectrum

The six actual candidate modules have dimensions 1, 4, 4, 6, 14, and 20.
Absolute irreducibility and the bound of six odd-order conjugacy classes make
them exhaustive after scalar extension. The split-family descent theorem then
classifies every irreducible module over F₂ itself. Faithfulness excludes degree
one and the bound eighteen excludes degree twenty.

The independently proved model constructions and odd-order class count discharge
all premises in `sevenSmallDegreeSpectrum`. No cubic-ratio hypothesis,
module-recognition theorem, or B.4.2 is used.

Source: Aschbacher–Smith, K.1.2, printed p.452/PDF p.463, invoking
Guralnick–Malle (2002), Theorem 6.2 and Table 6.3; the RWTH A₇ decomposition
matrix in characteristic two supplies the supporting candidate degree data.
-/

public section

open Representation
namespace CFSG.Quasithin.ChapterK.Alternating
namespace SevenSmallSpectrum

private abbrev CandidateIndex := Option (Option (Option (Option (Fin 2))))

private theorem trivial_absolute : IsAbsolutelyIrreducible
    (Representation.trivial (ZMod 2) (alternatingGroup (Fin 7)) (ZMod 2)) := by
  refine ⟨?_⟩
  let E := AlgebraicClosure (ZMod 2)
  let : IsSimpleOrder (Submodule E (TensorProduct (ZMod 2) E (ZMod 2))) :=
    is_simple_module_of_finrank_eq_one (K := E) (by simp)
  constructor
  intro S
  rcases IsSimpleOrder.eq_bot_or_eq_top S.toSubmodule with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

/-- The genuine A₇ has no faithful one-dimensional representation. -/
theorem faithful_finrank_ne_one
    {F W : Type*} [Field F] [AddCommGroup W] [Module F W]
    (σ : Representation F (alternatingGroup (Fin 7)) W)
    (hf : Function.Injective σ) : Module.finrank F W ≠ 1 := by
  intro hd
  let x : alternatingGroup (Fin 7) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by
      rw [Equiv.Perm.mem_alternatingGroup]
      decide⟩
  let y : alternatingGroup (Fin 7) :=
    ⟨Equiv.swap 0 3 * Equiv.swap 3 4, by
      rw [Equiv.Perm.mem_alternatingGroup]
      decide⟩
  have hxy : x * y ≠ y * x := by decide
  apply hxy
  apply hf
  obtain ⟨a, ha, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hd (σ x)
  obtain ⟨b, hb, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hd (σ y)
  rw [map_mul, map_mul, ha, hb]
  simp [smul_smul, mul_comm]

/-- Concrete candidates and a class count give the bounded binary spectrum.
The representation being classified is only assumed irreducible over F₂. -/
theorem small_degree_of_models
    (ρ₄ : Fin 2 → Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 4 → ZMod 2))
    (ρ₆ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 6 → ZMod 2))
    (ρ₁₄ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 14 → ZMod 2))
    (ρ₂₀ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 20 → ZMod 2))
    [∀ i, IsAbsolutelyIrreducible (ρ₄ i)] [IsAbsolutelyIrreducible ρ₆]
    [IsAbsolutelyIrreducible ρ₁₄] [IsAbsolutelyIrreducible ρ₂₀]
    (hne : Pairwise fun i j => IsEmpty ((ρ₄ i).Equiv (ρ₄ j)))
    (hclasses : Nat.card (ConjClasses.mk ''
      {g : alternatingGroup (Fin 7) | ¬ 2 ∣ orderOf g}) ≤ 6)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) W) [IsIrreducible σ]
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) W ≤ 18) :
    Module.finrank (ZMod 2) W = 4 ∨ Module.finrank (ZMod 2) W = 6 ∨
      Module.finrank (ZMod 2) W = 14 := by
  classical
  let V : CandidateIndex → Type := fun i =>
    match i with
    | none => ZMod 2
    | some none => Fin 6 → ZMod 2
    | some (some none) => Fin 14 → ZMod 2
    | some (some (some none)) => Fin 20 → ZMod 2
    | some (some (some (some _))) => Fin 4 → ZMod 2
  let addV : ∀ i, AddCommGroup (V i) := fun i => by
    rcases i with _ | (_ | (_ | (_ | i))) <;> dsimp [V] <;> infer_instance
  let modV : ∀ i, Module (ZMod 2) (V i) := fun i => by
    rcases i with _ | (_ | (_ | (_ | i))) <;> dsimp [V] <;> infer_instance
  let rep : ∀ i, Representation (ZMod 2) (alternatingGroup (Fin 7)) (V i) := fun i =>
    match i with
    | none => Representation.trivial _ _ _
    | some none => ρ₆
    | some (some none) => ρ₁₄
    | some (some (some none)) => ρ₂₀
    | some (some (some (some j))) => ρ₄ j
  have finV : ∀ i, FiniteDimensional (ZMod 2) (V i) := by
    intro i
    rcases i with _ | (_ | (_ | (_ | i))) <;> dsimp [V] <;> infer_instance
  have irr : ∀ i, IsAbsolutelyIrreducible (rep i) := by
    intro i
    rcases i with _ | (_ | (_ | (_ | i)))
    · exact trivial_absolute
    all_goals dsimp [rep]; infer_instance
  have hdistinct : Pairwise fun i j => IsEmpty ((rep i).Equiv (rep j)) := by
    intro i j hij
    constructor
    intro e
    rcases i with _ | (_ | (_ | (_ | i))) <;> rcases j with _ | (_ | (_ | (_ | j)))
    all_goals first
      | exact hij rfl
      | exact (hne (fun h => hij (by simp [h]))).false e
      | have he := e.toLinearEquiv.finrank_eq
        norm_num [V] at he
  have hc : Nat.card CandidateIndex = 6 := by
    simp [CandidateIndex, Nat.card_eq_fintype_card]
  obtain ⟨i, ⟨e⟩⟩ := SplitSimpleCatalogue.exists_equiv V rep 2 hdistinct
    (hc ▸ hclasses) σ
  have he := e.toLinearEquiv.finrank_eq
  rcases i with _ | (_ | (_ | (_ | i))) <;> simp only [V, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at he
  · exact (faithful_finrank_ne_one σ hf he).elim
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr he)
  · omega
  · exact Or.inl he

end SevenSmallSpectrum

universe v

/-- Conditional assembly of the exact K.1.2 spectrum obligation from concrete
model constructions and the group-specific class count. -/
theorem sevenSmallDegreeSpectrum_of_constructions
    (hsmall : SevenSmallSpectrum.SmallModelsExist)
    (hlarge : SevenSmallSpectrum.LargeModelsExist)
    (hclasses : Nat.card (ConjClasses.mk ''
      {g : alternatingGroup (Fin 7) | ¬ 2 ∣ orderOf g}) ≤ 6) :
    RecognitionInputs.Seven.Degree.SmallSpectrum.{v} := by
  obtain ⟨ρ₄, ρ₆, h₄, h₆, hne⟩ := hsmall
  obtain ⟨ρ₁₄, ρ₂₀, h₁₄, h₂₀⟩ := hlarge
  let := h₄
  let := h₆
  let := h₁₄
  let := h₂₀
  intro W _ _ _ σ hf hi hd
  let := hi
  exact SevenSmallSpectrum.small_degree_of_models ρ₄ ρ₆ ρ₁₄ ρ₂₀ hne hclasses σ hf hd

/-- Every faithful irreducible binary representation of the actual A₇ of degree
at most eighteen has degree four, six, or fourteen. Absolute irreducibility of
the representation being classified is not assumed. -/
theorem sevenSmallDegreeSpectrum : RecognitionInputs.Seven.Degree.SmallSpectrum.{v} :=
  sevenSmallDegreeSpectrum_of_constructions SevenSmallSpectrum.smallModelsExist
    SevenSmallSpectrum.largeModelsExist SevenSmallSpectrum.odd_class_count_le_six

end CFSG.Quasithin.ChapterK.Alternating
