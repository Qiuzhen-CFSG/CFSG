module

public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.LocalCentralizer.Presentation
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.CoverSquareOrbit
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order

/-!
# Checking the presentation against the literal J₂ centralizer

The seven base words and the two commutator expressions are checked on all
100 points of the faithful permutation action. Existing generator coverage
then proves surjectivity for any homomorphism whose range contains the two
marked generators. No presentation faithfulness or group-order computation
is inferred from these permutation checks.

Source: ATLAS J2G1-p100B0, with the existing left-action convention; the
commutator expressions are those of `FirstParabolic/CoverSquareOrbit.lean`.
-/

@[expose] public section
namespace Theory.SpecificGroups.J2HSMultipliers.J2.LocalCentralizerPresentation
open Sporadic.LeechRelated.J2 GeneratorPair FirstFusion
open ExceptionalParabolics ExceptionalParabolics.Seed Subgroup

abbrev Local := l₁

def localGenerator (i : Bool) : Local :=
  ⟨letter a c i, by cases i; exact a_mem_centralizer; exact c_mem_centralizer⟩

def localInclusion : Local →* Equiv.Perm (Fin 100) := inclusion.comp l₁.subtype

theorem localInclusion_injective : Function.Injective localInclusion :=
  inclusion_injective.comp Subtype.val_injective

private def packedGenerator (i : Bool) : Equiv.Perm (Fin 100) where
  toFun := LocalCertificate.localLetterValue (if i then 1 else 0)
  invFun := LocalCertificate.localLetterValue (if i then 2 else 0)
  left_inv := by cases i <;> decide +kernel
  right_inv := by cases i <;> decide +kernel

private theorem localInclusion_generator (i : Bool) :
    localInclusion (localGenerator i) = packedGenerator i := by
  apply Equiv.ext
  intro p
  cases i
  · exact (LocalCertificate.localLetterValue_eq 0 p).symm
  · exact (LocalCertificate.localLetterValue_eq 1 p).symm

set_option maxRecDepth 100000 in
private theorem base_check : ∀ (i : Fin 7) (p : Fin 100),
    baseValue (packedGenerator false) (packedGenerator true) i p = p := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem normalization_check : ∀ (i : Bool) (p : Fin 100),
    normalize (packedGenerator false) (packedGenerator true) i p = packedGenerator i p := by
  decide +kernel

/-- All seven words are actual relations in the marked order-1920 subgroup. -/
theorem local_baseValue (i : Fin 7) :
    baseValue (localGenerator false) (localGenerator true) i = 1 := by
  apply localInclusion_injective
  rw [map_baseValue, localInclusion_generator, localInclusion_generator, map_one]
  exact Equiv.ext (base_check i)

/-- The commutator words recover the literal local generators. -/
theorem local_normalize (i : Bool) :
    normalize (localGenerator false) (localGenerator true) i = localGenerator i := by
  apply localInclusion_injective
  rw [map_normalize, localInclusion_generator, localInclusion_generator,
    localInclusion_generator]
  exact Equiv.ext (normalization_check i)

theorem local_relations (i : Fin 16) :
    relationValue (localGenerator false) (localGenerator true) i = 1 := by
  fin_cases i <;> simp [relationValue, local_baseValue, local_normalize]

/-- A range containing both marked generators is the whole literal centralizer. -/
theorem surjective_of_local_generators {G : Type*} [Group G] (f : G →* Local)
    (h : ∀ i, localGenerator i ∈ f.range) : Function.Surjective f := by
  have hL : l₁ ≤ f.range.map l₁.subtype := by
    change centralizer ≤ f.range.map l₁.subtype
    rw [LocalCertificate.centralizer_eq_closure_letters]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    have ha : a ∈ f.range.map l₁.subtype :=
      ⟨localGenerator false, h false, rfl⟩
    have hc : c ∈ f.range.map l₁.subtype :=
      ⟨localGenerator true, h true, rfl⟩
    fin_cases i
    · exact ha
    · exact hc
    · exact (f.range.map l₁.subtype).inv_mem hc
  intro x
  obtain ⟨y, ⟨g, hg⟩, hy⟩ := hL x.property
  exact ⟨g, hg.trans (Subtype.ext hy)⟩

/-- The specified presentation maps onto the actual centralizer. -/
def localMap : Presentation →* Local :=
  evaluate (localGenerator false) (localGenerator true) local_relations

theorem localMap_generator (i : Bool) : localMap (generator i) = localGenerator i := by
  cases i <;> exact evaluate_generator _ _ _ _

theorem localMap_surjective : Function.Surjective localMap :=
  surjective_of_local_generators localMap fun i => ⟨generator i, localMap_generator i⟩

end Theory.SpecificGroups.J2HSMultipliers.J2.LocalCentralizerPresentation
