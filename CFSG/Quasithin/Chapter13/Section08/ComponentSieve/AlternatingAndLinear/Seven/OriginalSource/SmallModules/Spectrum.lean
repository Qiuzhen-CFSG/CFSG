module
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.Degree.SmallSpectrum
/-!
# The marked small binary A₇ simple modules

The six constructed split simple modules exhaust the binary simple catalogue. The bound twelve leaves precisely the two concrete four-spaces and the literal natural core. Unlike the numerical degree result, these equivalences retain the given A₇ action.

Source: Aschbacher–Smith 13.8.24, printed pp.958–959; the candidate exhaustion is the existing Chapter K small-spectrum proof.
-/

public section
open Representation
namespace Representation.AlternatingSevenSmallQuadratic
open AlternatingSevenBinarySmallModels
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


/-- Every faithful simple binary A₇-module of dimension at most twelve is
one of the two specified four-spaces or the literal six-dimensional core.
All three equivalences preserve the given A₇ actor. -/
theorem small_simple_equiv
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) W) [IsIrreducible σ]
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) W ≤ 12) :
    Nonempty (σ.Equiv AlternatingSevenConjugatePair.Model.natural) ∨
      Nonempty (σ.Equiv AlternatingSevenConjugatePair.Model.outerNatural) ∨
      Nonempty (σ.Equiv (BinaryPermutation.alternatingCoreRepresentation (Fin 7))) := by
  classical
  let ρ₄ := ![AlternatingSevenConjugatePair.Model.natural,
    AlternatingSevenConjugatePair.Model.outerNatural]
  let ρ₆ := six
  have h₄ : ∀ i, IsAbsolutelyIrreducible (ρ₄ i) := by
    intro i
    fin_cases i
    · exact four_absolute
    · exact outerFour_absolute
  have h₆ : IsAbsolutelyIrreducible ρ₆ := six_absolute
  obtain ⟨ρ₁₄, ρ₂₀, h₁₄, h₂₀⟩ :=
    CFSG.Quasithin.ChapterK.Alternating.SevenSmallSpectrum.largeModelsExist
  have hne : Pairwise fun i j => IsEmpty ((ρ₄ i).Equiv (ρ₄ j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact ⟨fun e => AlternatingSevenConjugatePair.Model.natural_not_equiv_outerNatural
        ⟨e⟩⟩
    · exact ⟨fun e => AlternatingSevenConjugatePair.Model.natural_not_equiv_outerNatural
        ⟨e.symm⟩⟩
    · exact (hij rfl).elim
  have hclasses := CFSG.Quasithin.ChapterK.Alternating.SevenSmallSpectrum.odd_class_count_le_six
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
  · exact (CFSG.Quasithin.ChapterK.Alternating.SevenSmallSpectrum.faithful_finrank_ne_one σ hf he).elim
  · right; right
    exact ⟨e.trans naturalSixEquiv.symm.toRepresentationEquiv |>.trans
      coreNaturalEquiv.symm.toRepresentationEquiv⟩
  · omega
  · omega
  · fin_cases i
    · exact Or.inl ⟨e⟩
    · exact Or.inr (Or.inl ⟨e⟩)

end Representation.AlternatingSevenSmallQuadratic
