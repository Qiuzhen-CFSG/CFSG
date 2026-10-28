module
public import Theory.Representation.BinaryAlternatingSixModels.TensorIrreducibility
public import Theory.Representation.BinaryAlternatingSixModels.SymmetricCatalogue
public import Theory.Representation.FactorDegreeFiltration.FiniteDual
public import Theory.Representation.SimpleHeadQuotient
/-!
# Complete binary A₆ and S₆ catalogues on the actual models

The native alternating tensor irreducibility discharges the remaining input
of the flag-module classification for S₆. All four symmetric simple models
restrict irreducibly. A finite composition series therefore gives a literal
A₆ filtration with degrees 1, 4 and 16; induction on that series also retains
actual equivariant isomorphisms for every simple quotient. Every binary A₆
simple module is a quotient of the restricted incidence flag module, whose
stabilizer is the actual Sylow two-subgroup. Thus both model catalogues and
the degree gap are unconditional.

The companion Steinberg comparison is the original duad–syntheme building,
not an abstract representation of matching dimension. Scalar extension and
the two conjugate F₄ summands in G.5.1(3) are not asserted here.
Source: Aschbacher–Smith G.5.1–2, printed pp.342–343.
-/

public section
namespace BinaryAlternatingSix
open Theory.SpecificGroups.SymmetricSix Representation

/-- Unconditional catalogue for the literal symmetric action. -/
theorem symmetric_classify {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) S6 V)
    [IsIrreducible ρ] : IsSymmetricModel ρ :=
  SymmetricCatalogue.classify alternatingTensor_irreducible ρ

private def restrictEquiv {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) S6 V} {σ : Representation (ZMod 2) S6 W}
    (e : ρ.Equiv σ) : Representation.Equiv (ρ.comp A6.subtype) (σ.comp A6.subtype) :=
  .mk e.toLinearEquiv (fun g => e.isIntertwining' g.val)

theorem alternatingModel_of_symmetricModel {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) S6 V) (hm : IsSymmetricModel ρ) :
    IsAlternatingModel (ρ.comp A6.subtype) := by
  rcases hm with he | he | he | he
  all_goals obtain ⟨e⟩ := he
  · exact Or.inl ⟨restrictEquiv e⟩
  · exact Or.inr (Or.inl ⟨restrictEquiv e⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨restrictEquiv e⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨restrictEquiv e⟩))

theorem alternatingModel_irreducible {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) A6 V) (hm : IsAlternatingModel ρ) : IsIrreducible ρ := by
  rcases hm with he | he | he | he
  all_goals obtain ⟨e⟩ := he
  · exact (RepEquiv.ofRepresentationEquiv e).irreducible_of_euqiv trivialAlternating_irreducible
  · exact (RepEquiv.ofRepresentationEquiv e).irreducible_of_euqiv firstAlternating_irreducible
  · exact (RepEquiv.ofRepresentationEquiv e).irreducible_of_euqiv secondAlternating_irreducible
  · exact (RepEquiv.ofRepresentationEquiv e).irreducible_of_euqiv alternatingTensor_irreducible

theorem alternatingModel_degree {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) A6 V) (hm : IsAlternatingModel ρ) :
    Module.finrank (ZMod 2) V = 1 ∨ Module.finrank (ZMod 2) V = 4 ∨ Module.finrank (ZMod 2) V = 16 := by
  rcases hm with he | he | he | he
  all_goals obtain ⟨e⟩ := he
  · exact Or.inl (e.toLinearEquiv.finrank_eq.trans (by simp))
  · exact Or.inr (Or.inl (e.toLinearEquiv.finrank_eq.trans naturalModule_finrank))
  · exact Or.inr (Or.inl (e.toLinearEquiv.finrank_eq.trans naturalModule_finrank))
  · exact Or.inr (Or.inr (e.toLinearEquiv.finrank_eq.trans tensor_finrank))

universe u
private theorem restricted_filtration_aux (n : ℕ) :
    ∀ {V : Type u} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
      (ρ : Representation (ZMod 2) S6 V), Module.finrank (ZMod 2) V = n →
      FactorDegreeFiltration {d : ℕ | d = 1 ∨ d = 4 ∨ d = 16} (ρ.comp A6.subtype) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ _ ρ hn
    by_cases hz : n = 0
    · have hv : Module.finrank (ZMod 2) V = 0 := hn.trans hz
      let : Subsingleton V := Module.finrank_zero_iff.mp hv
      exact .zero _
    · let : Nontrivial V := Module.nontrivial_of_finrank_pos (show 0 < Module.finrank (ZMod 2) V by omega)
      let : IsCoatomic (Subrepresentation ρ) := SimpleHeadQuotient.subrepresentation_coatomic ρ
      obtain ⟨N,hN⟩ := IsCoatomic.exists_coatom (Subrepresentation ρ)
      let : IsIrreducible N.quotientRepresentation := SimpleHeadQuotient.irreducible_quotient_of_isCoatom N hN
      have hm := alternatingModel_of_symmetricModel N.quotientRepresentation
        (symmetric_classify N.quotientRepresentation)
      let T : Subrepresentation (ρ.comp A6.subtype) :=
        ⟨N.toSubmodule,fun g _ hv => N.apply_mem_toSubmodule g.val hv⟩
      have hlt : Module.finrank (ZMod 2) N.toSubmodule < n := by
        rw [← hn]
        exact Submodule.finrank_lt (fun he => hN.1 (Subrepresentation.toSubmodule_injective he))
      refine .step T (ih _ hlt N.toRepresentation rfl) ?_ ?_
      · exact alternatingModel_irreducible _ hm
      · exact alternatingModel_degree _ hm

/-- The actual restriction of every finite binary S₆ representation has a
finite filtration with irreducible factors of degrees 1, 4 and 16. -/
theorem restricted_factorDegreeFiltration {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) S6 V) :
    FactorDegreeFiltration {d : ℕ | d = 1 ∨ d = 4 ∨ d = 16} (ρ.comp A6.subtype) :=
  restricted_filtration_aux _ ρ rfl

theorem incidence_flag_filtration :
    FactorDegreeFiltration {d : ℕ | d = 1 ∨ d = 4 ∨ d = 16}
      (SymmetricCatalogue.flagRepresentation.comp A6.subtype) :=
  restricted_factorDegreeFiltration _

theorem alternating_degrees {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) A6 V) [IsIrreducible ρ] :
    Module.finrank (ZMod 2) V = 1 ∨ Module.finrank (ZMod 2) V = 4 ∨ Module.finrank (ZMod 2) V = 16 := by
  apply BinaryPermutation.finrank_mem_of_factorDegreeFiltration
    (SymmetricCatalogue.flagPerm.comp A6.subtype) SymmetricCatalogue.baseFlag
    a6Borel (IsPGroup.of_card (show Nat.card a6Borel = 2 ^ 3 from a6Borel_order))
    (fun g => SymmetricCatalogue.flag_stabilizer g.val) ?_
    incidence_flag_filtration ρ
  intro f
  obtain ⟨g,hg,hs⟩ := a6_flag_transitive 0 f.val.1 0 f.val.2 (by decide) f.property
  exact ⟨g,Subtype.ext (Prod.ext hg hs)⟩

end BinaryAlternatingSix

namespace BinaryAlternatingSix
open Theory.SpecificGroups.SymmetricSix Representation
universe u v

private theorem model_of_equiv {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) A6 V} {σ : Representation (ZMod 2) A6 W}
    (e : ρ.Equiv σ) (hm : IsAlternatingModel σ) : IsAlternatingModel ρ := by
  rcases hm with ha | ha | ha | ha
  all_goals obtain ⟨a⟩ := ha
  · exact Or.inl ⟨e.trans a⟩
  · exact Or.inr (Or.inl ⟨e.trans a⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨e.trans a⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨e.trans a⟩))

private theorem restricted_quotient_aux (n : ℕ) :
    ∀ {V : Type u} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
      (ρ : Representation (ZMod 2) S6 V), Module.finrank (ZMod 2) V = n →
      ∀ {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
        (σ : Representation (ZMod 2) A6 W) [IsIrreducible σ]
        (f : Representation.IntertwiningMap (ρ.comp A6.subtype) σ), f ≠ 0 → IsAlternatingModel σ := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ _ ρ hn W _ _ σ _ f hf
    have hv : Nontrivial V := by
      by_contra! h
      let := h
      apply hf
      ext x
      exact (congrArg f (Subsingleton.elim x 0)).trans (map_zero f)
    let := hv
    let : IsCoatomic (Subrepresentation ρ) := SimpleHeadQuotient.subrepresentation_coatomic ρ
    obtain ⟨N,hN⟩ := IsCoatomic.exists_coatom (Subrepresentation ρ)
    let r : Representation.IntertwiningMap (N.toRepresentation.comp A6.subtype) σ := {
      toLinearMap := f.toLinearMap.comp N.toSubmodule.subtype
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro x
        exact IntertwiningMap.isIntertwining _ _ f g x }
    by_cases hr : r = 0
    · have hk : N.toSubmodule ≤ f.toLinearMap.ker := by
        intro x hx
        exact congrArg (fun q : Representation.IntertwiningMap (N.toRepresentation.comp A6.subtype) σ => q ⟨x,hx⟩) hr
      let q : Representation.IntertwiningMap (N.quotientRepresentation.comp A6.subtype) σ := {
        toLinearMap := N.toSubmodule.liftQ f.toLinearMap hk
        isIntertwining' := by
          intro g
          apply LinearMap.ext
          intro x
          induction x using Submodule.Quotient.induction_on with
          | H x => exact IntertwiningMap.isIntertwining _ _ f g x }
      have hq : q ≠ 0 := by
        intro hz
        apply hf
        ext x
        exact congrArg (fun z : Representation.IntertwiningMap (N.quotientRepresentation.comp A6.subtype) σ =>
          z (N.toSubmodule.mkQ x)) hz
      let : IsIrreducible N.quotientRepresentation := SimpleHeadQuotient.irreducible_quotient_of_isCoatom N hN
      have hm := alternatingModel_of_symmetricModel _ (symmetric_classify N.quotientRepresentation)
      let : IsIrreducible (N.quotientRepresentation.comp A6.subtype) := alternatingModel_irreducible _ hm
      exact model_of_equiv
        (q.ofBijective ((IsIrreducible.bijective_or_eq_zero q).resolve_right hq)).symm hm
    · have hlt : Module.finrank (ZMod 2) N.toSubmodule < n := by
        rw [← hn]
        exact Submodule.finrank_lt (fun he => hN.1 (Subrepresentation.toSubmodule_injective he))
      exact ih _ hlt N.toRepresentation rfl σ r hr

/-- Every irreducible quotient of a restricted symmetric representation is
one of the four literal alternating models. -/
theorem restricted_simple_quotient_model {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) S6 V) (σ : Representation (ZMod 2) A6 W) [IsIrreducible σ]
    (f : Representation.IntertwiningMap (ρ.comp A6.subtype) σ) (hf : f ≠ 0) : IsAlternatingModel σ :=
  restricted_quotient_aux _ ρ rfl σ f hf

/-- The complete binary A₆ catalogue, with actual equivariant linear maps. -/
theorem alternating_classify {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) A6 V) [IsIrreducible ρ] :
    IsAlternatingModel ρ := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨f,hf⟩ := BinaryLinearThree.IrreducibleCatalogue.irreducible_permutation_quotient
    (SymmetricCatalogue.flagPerm.comp A6.subtype) SymmetricCatalogue.baseFlag a6Borel
    (IsPGroup.of_card (show Nat.card a6Borel = 2 ^ 3 from a6Borel_order))
    (fun g => SymmetricCatalogue.flag_stabilizer g.val)
    (by
      intro f
      obtain ⟨g,hg,hs⟩ := a6_flag_transitive 0 f.val.1 0 f.val.2 (by decide) f.property
      exact ⟨g,Subtype.ext (Prod.ext hg hs)⟩) ρ
  apply restricted_simple_quotient_model SymmetricCatalogue.flagRepresentation ρ f
  intro hz
  obtain ⟨v,hv⟩ := exists_ne (0 : V)
  obtain ⟨x,hx⟩ := hf v
  exact hv (hx.symm.trans (congrArg (fun q => q x) hz))
end BinaryAlternatingSix
