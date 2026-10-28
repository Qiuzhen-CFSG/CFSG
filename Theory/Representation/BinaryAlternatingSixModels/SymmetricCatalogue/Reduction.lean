module

public import Theory.Representation.BinaryAlternatingSixModels.SymmetricCatalogue.Building
public import Theory.Representation.BinaryAlternatingSixModels.Geometry

/-!
# Reduction of the binary S₆ catalogue to concrete incidence maps

Every irreducible binary module is a quotient of the flag module. Composing
with the vertex coboundary either gives a nonzero map from one of the two
fifteen-point modules, or vanishes and factors through top cohomology. Actual
model comparisons on these three modules therefore prove exhaustion.

The final application combines this reduction with the already proved marked
parabolic line exclusions to obtain an equivariant equivalence with the cycle
module. Both statements retain the unproved vertex quotient alternatives and
tensor/incidence equivalences explicitly. They are conditional assembly
lemmas, not completed assertions of G.5.1 or G.5.2. The permitted irreducibility
premise on the A₆ tensor is supplied to final source assembly independently.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), G.5.1–2,
printed pp.342–343 (PDF pp.353–354).
-/

@[expose] public section

open Theory.SpecificGroups.SymmetricSix BinaryPermutation Representation
namespace BinaryAlternatingSix.SymmetricCatalogue

/-- A nonzero map from the flag module survives on a vertex coboundary or
factors nontrivially through top cohomology. No simplicity is needed here. -/
theorem flag_map_cases
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) S6 V)
    (f : flagRepresentation.IntertwiningMap ρ) (hf : f ≠ 0) :
    (∃ q : BinaryDuadModule.pointAction.IntertwiningMap ρ, q ≠ 0) ∨
    (∃ q : lineRepresentation.IntertwiningMap ρ, q ≠ 0) ∨
      ∃ q : topCohomologyRepresentation.IntertwiningMap ρ, q ≠ 0 := by
  let p := (f.comp coboundary).comp
    (IntertwiningMap.inl (ZMod 2) BinaryDuadModule.pointAction lineRepresentation)
  let l := (f.comp coboundary).comp
    (IntertwiningMap.inr (ZMod 2) BinaryDuadModule.pointAction lineRepresentation)
  by_cases hp : p = 0
  · by_cases hl : l = 0
    · right; right
      have hk : coboundaries.toSubmodule ≤ f.toLinearMap.ker := by
        rintro _ ⟨v, rfl⟩
        have hpv : f (coboundary (v.1, 0)) = 0 :=
          congrArg (fun q : BinaryDuadModule.pointAction.IntertwiningMap ρ => q v.1) hp
        have hlv : f (coboundary (0, v.2)) = 0 :=
          congrArg (fun q : lineRepresentation.IntertwiningMap ρ => q v.2) hl
        change f (coboundary v) = 0
        have he : v = (v.1, 0) + (0, v.2) := by simp
        rw [he, map_add, map_add, hpv, hlv, add_zero]
      let q : topCohomologyRepresentation.IntertwiningMap ρ := {
        toLinearMap := coboundaries.toSubmodule.liftQ f.toLinearMap hk
        isIntertwining' := by
          intro g
          apply LinearMap.ext
          intro x
          induction x using Submodule.Quotient.induction_on with
          | H x => exact IntertwiningMap.isIntertwining flagRepresentation ρ f g x }
      refine ⟨q, fun hq => hf ?_⟩
      apply IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      exact congrArg (fun z : topCohomologyRepresentation.IntertwiningMap ρ =>
        z (coboundaries.toSubmodule.mkQ x)) hq
    · exact Or.inr (Or.inl ⟨l, hl⟩)
  · exact Or.inl ⟨p, hp⟩

/-- Irreducibility on the alternating subgroup implies irreducibility on S₆. -/
theorem tensor_irreducible_of_alternating
    (hTensor : IsIrreducible alternatingTensor) : IsIrreducible tensorAction := by
  let := hTensor
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun P => ?_⟩
  let Q : Subrepresentation alternatingTensor :=
    ⟨P.toSubmodule, fun g _ hv => P.apply_mem_toSubmodule g.val hv⟩
  rcases eq_bot_or_eq_top Q with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective
      (congrArg (fun T : Subrepresentation alternatingTensor => T.toSubmodule) h))
  · exact Or.inr (Subrepresentation.toSubmodule_injective
      (congrArg (fun T : Subrepresentation alternatingTensor => T.toSubmodule) h))

/-- The complete catalogue deduction from the two vertex quotient alternatives and the actual
incidence cohomology. These three concrete inputs remain to be constructed. -/
theorem classify_of_incidence_maps
    (hTensor : IsIrreducible alternatingTensor)
    (e : topCohomologyRepresentation.Equiv tensorAction)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) S6 V) [IsIrreducible ρ]
    (hPoint : ∀ f : BinaryDuadModule.pointAction.IntertwiningMap ρ, f ≠ 0 →
      Nonempty (ρ.Equiv trivialSymmetric) ∨ Nonempty (ρ.Equiv firstNatural) ∨
        Nonempty (ρ.Equiv secondNatural))
    (hLine : ∀ f : lineRepresentation.IntertwiningMap ρ, f ≠ 0 →
      Nonempty (ρ.Equiv trivialSymmetric) ∨ Nonempty (ρ.Equiv firstNatural) ∨
        Nonempty (ρ.Equiv secondNatural)) :
    IsSymmetricModel ρ := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨f, hf⟩ := irreducible_flag_quotient ρ
  have hfn : f ≠ 0 := by
    intro hz
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨x, hx⟩ := hf v
    exact hv (hx.symm.trans (congrArg (fun q => q x) hz))
  rcases flag_map_cases ρ f hfn with ⟨p, hp⟩ | ⟨l, hl⟩ | ⟨q, hq⟩
  · rcases hPoint p hp with ht | hn | hn
    · exact Or.inl ht
    · exact Or.inr (Or.inl hn)
    · exact Or.inr (Or.inr (Or.inl hn))
  · rcases hLine l hl with ht | hn | hn
    · exact Or.inl ht
    · exact Or.inr (Or.inl hn)
    · exact Or.inr (Or.inr (Or.inl hn))
  · let := tensor_irreducible_of_alternating hTensor
    let t := q.comp e.symm.toIntertwiningMap
    have ht : t ≠ 0 := by
      intro hz
      apply hq
      apply IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      have hx := congrArg (fun z : tensorAction.IntertwiningMap ρ => z (e x)) hz
      simpa [t] using hx
    exact Or.inr (Or.inr (Or.inr
      ⟨(t.ofBijective ((IsIrreducible.bijective_or_eq_zero t).resolve_right ht)).symm⟩))

/-- The source G.5.2 exclusion applied to the incidence reduction, retaining an
actual equivariant equivalence with the building cycle module. Its extra inputs
are the same concrete calculations required for the catalogue. -/
theorem homology_recognition_of_incidence_maps
    (hTensor : IsIrreducible alternatingTensor)
    (e : topCohomologyRepresentation.Equiv tensorAction)
    (eHomology : tensorAction.Equiv topHomologyRepresentation)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) S6 V) [IsIrreducible ρ]
    (hPoint : ∀ f : BinaryDuadModule.pointAction.IntertwiningMap ρ, f ≠ 0 →
      Nonempty (ρ.Equiv trivialSymmetric) ∨ Nonempty (ρ.Equiv firstNatural) ∨
        Nonempty (ρ.Equiv secondNatural))
    (hLine : ∀ f : lineRepresentation.IntertwiningMap ρ, f ≠ 0 →
      Nonempty (ρ.Equiv trivialSymmetric) ∨ Nonempty (ρ.Equiv firstNatural) ∨
        Nonempty (ρ.Equiv secondNatural))
    (h₁ : HasInvariantLine (ρ.comp A6.subtype) a6DuadStabilizer)
    (h₂ : HasInvariantLine (ρ.comp A6.subtype) a6SynthemeStabilizer) :
    Nonempty (ρ.Equiv topHomologyRepresentation) := by
  obtain ⟨eTensor⟩ := tensor_of_invariant_lines_of_model ρ
    (classify_of_incidence_maps hTensor e ρ hPoint hLine) h₁ h₂
  exact ⟨eTensor.trans eHomology⟩

end BinaryAlternatingSix.SymmetricCatalogue
