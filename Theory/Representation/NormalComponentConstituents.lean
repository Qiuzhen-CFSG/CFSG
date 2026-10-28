module
public import Theory.Representation.NormalInvariants
public import Theory.Representation.NormalConstituentDisplacement.FixedLine
public import Theory.Representation.BinaryOffender.SemisimpleIrrPlus
public import Theory.Representation.BinaryOffender.IrreducibleExistence
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.Representation.BinaryOffender.QuadraticHomogeneousOrbit
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Normal component-orbit constituents

A nontrivial normal subgroup of a faithful irreducible binary representation
has zero fixed space and generates the entire module by its displacements.
Clifford restriction makes each Irr-plus member an actual irreducible
subrepresentation, whose ambient conjugates span the original module.

This is the constituent reduction in Aschbacher--Smith G.10.7. The subgroup
used for a component is its literal ambient conjugate orbit.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Normality and ambient irreducibility force a nontrivial faithful actor to
have no fixed vectors. -/
theorem fixedSpace_eq_bot_of_normal_faithful_irreducible
    (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (H : Subgroup G) [H.Normal] (hne : H ≠ ⊥) : fixedSpace ρ H = ⊥ := by
  let := hi
  by_contra hn
  have hk := le_ker_of_normal_invariants_ne_bot ρ H hn
  apply hne
  apply le_bot_iff.mp
  intro x hx
  apply mem_bot.mpr
  apply hf
  exact (hk hx).trans (map_one ρ).symm

/-- Normality makes the displacement space an ambient subrepresentation. -/
theorem subspaceCommutator_top_eq_top_of_normal_faithful_irreducible
    (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (H : Subgroup G) [H.Normal] (hne : H ≠ ⊥) :
    subspaceCommutator ρ ⊤ H = ⊤ := by
  let D := subspaceCommutator ρ ⊤ H
  have hs : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ D :=
    subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
      (by rw [H.normalizer_eq_top])
  let R : Subrepresentation ρ :=
    ⟨D, fun g v hv => (hs (mem_top g) v).2 hv⟩
  rcases hi.eq_bot_or_eq_top R with hb | ht
  · have hd : D = ⊥ := congrArg Subrepresentation.toSubmodule hb
    have hfix := (subspaceCommutator_eq_bot_iff ρ ⊤ H).mp hd
    rw [fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hf hi H hne] at hfix
    let := hi
    let := Subrepresentation.irreducible_module_nontrivial ρ
    exact (top_ne_bot (α := Submodule (ZMod 2) V) (top_unique hfix).symm).elim
  · exact congrArg Subrepresentation.toSubmodule ht

variable [FiniteDimensional (ZMod 2) V]

/-- Every Irr-plus constituent of a normal restriction is irreducible before
taking its quotient by central vectors. -/
theorem IsIrrPlus.irreducible_of_normal_restriction (hi : ρ.IsIrreducible)
    (H : Subgroup G) [H.Normal] {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ H I) :
    IsIrreducible (invariantSubspace ρ H I hI.choose).toRepresentation := by
  let hs := NormalConstituentDisplacement.restriction_semisimple ρ hi H
  let : IsSemisimpleRepresentation (ρ.comp H.subtype) :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mpr hs
  exact hI.irreducible_of_semisimple ρ

/-- Conjugates of the literal constituent span the ambient module. -/
theorem IsIrrPlus.conjugates_span_of_normal_restriction (hi : ρ.IsIrreducible)
    (H : Subgroup G) [H.Normal] {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ H I) :
    (⨆ g : G, conjugateSubrepresentation ρ H
      (invariantSubspace ρ H I hI.choose) g) = ⊤ :=
  iSup_conjugateSubrepresentations_eq_top ρ H hi _
    (hI.irreducible_of_normal_restriction ρ hi H)

/-- Distinct ambient conjugates of a normal-restriction constituent have zero
intersection. This is the literal TI statement on submodules. -/
theorem IsIrrPlus.eq_or_disjoint_conjugate_of_normal_restriction
    (hi : ρ.IsIrreducible) (H : Subgroup G) [H.Normal]
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ H I) (g : G) :
    I.map (ρ g) = I ∨ Disjoint (I.map (ρ g)) I := by
  let J := invariantSubspace ρ H I hI.choose
  have ha : IsAtom J := (Subrepresentation.irreducible_iff_isAtom J).mp
    (hI.irreducible_of_normal_restriction ρ hi H)
  let Jg := conjugateSubrepresentationOrderIso ρ H g J
  have hag : IsAtom Jg := ((conjugateSubrepresentationOrderIso ρ H g).isAtom_iff J).mpr ha
  by_cases he : Jg = J
  · left
    simpa only [Jg, J, conjugateSubrepresentationOrderIso_toSubmodule, invariantSubspace] using
      congrArg Subrepresentation.toSubmodule he
  · right
    rw [disjoint_iff]
    have hz : Jg.toSubmodule ⊓ J.toSubmodule = ⊥ :=
      congrArg Subrepresentation.toSubmodule (hag.disjoint_of_ne ha he).eq_bot
    simpa only [Jg, J, conjugateSubrepresentationOrderIso_toSubmodule, invariantSubspace] using hz

/-- The restriction of an invariant alternating form to an actual irreducible
constituent is either zero or nondegenerate. -/
theorem IsIrrPlus.isotropic_or_nondegenerate_of_normal_restriction
    (hi : ρ.IsIrreducible) (H : Subgroup G) [H.Normal]
    (B : LinearMap.BilinForm (ZMod 2) V) (halt : B.IsAlt)
    (hpres : ∀ g v w, B (ρ g v) (ρ g w) = B v w)
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ H I) :
    (∀ v ∈ I, ∀ w ∈ I, B v w = 0) ∨ (B.restrict I).Nondegenerate := by
  let σ := (invariantSubspace ρ H I hI.choose).toRepresentation
  let : σ.IsIrreducible := hI.irreducible_of_normal_restriction ρ hi H
  let f : IntertwiningMap σ σ.dual :=
    { toLinearMap := B.restrict I
      isIntertwining' g := by
        ext v w
        change B (ρ g v.val) w.val = B v.val (ρ (g⁻¹ : H) w.val)
        simpa only [Subgroup.coe_inv, ρ.self_inv_apply] using
          hpres g v.val (ρ (g⁻¹ : H) w.val) }
  rcases IsIrreducible.injective_or_eq_zero f with hinj | hz
  · right
    have hl : (B.restrict I).SeparatingLeft := by
      intro v hv
      apply hinj
      ext w
      change B v.val w.val = B 0 w.val
      exact (hv w).trans (by simp)
    refine ⟨hl, fun w hw => hl w fun v => ?_⟩
    exact halt.isRefl _ _ (hw v)
  · left
    intro v hv w hw
    exact congrArg (fun f : IntertwiningMap σ σ.dual => f ⟨v,hv⟩ ⟨w,hw⟩) hz

end Representation.BinaryOffender

namespace Theory.GroupTheory
variable {G : Type*} [Group G] {L : Subgroup G}

/-- The orbit under the whole ambient group is normal in that group. -/
theorem componentOrbit_top_normal (L : Subgroup G) :
    (componentOrbit L ⊤).Normal :=
  normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_componentOrbit L ⊤))

/-- A component's ambient orbit is nontrivial. -/
theorem IsComponent.componentOrbit_top_ne_bot (hL : IsComponent G L) :
    componentOrbit L ⊤ ≠ ⊥ := by
  let := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  intro hb
  exact (nontrivial_iff_ne_bot L).mp inferInstance
    (le_bot_iff.mp ((le_componentOrbit L ⊤).trans hb.le))

end Theory.GroupTheory

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- The literal component orbit has an irreducible binary constituent with
spanning conjugates, trivial intersections, the alternating-form dichotomy,
and degree greater than two. The ambient zero-fixed-space and full-commutator
identities are retained for the later marked-submodule argument. -/
@[expose] def ComponentOrbitConstituents
    (B : LinearMap.BilinForm (ZMod 2) V) (L : Subgroup G) : Prop :=
  let H := componentOrbit L ⊤
  letI := componentOrbit_top_normal L
  fixedSpace ρ H = ⊥ ∧ subspaceCommutator ρ ⊤ H = ⊤ ∧
  ∃ I : Submodule (ZMod 2) V, ∃ hI : IsIrrPlus ρ H I,
    IsIrreducible (invariantSubspace ρ H I hI.choose).toRepresentation ∧
    (⨆ g : G, conjugateSubrepresentation ρ H
      (invariantSubspace ρ H I hI.choose) g) = ⊤ ∧
    (∀ g : G, I.map (ρ g) = I ∨ Disjoint (I.map (ρ g)) I) ∧
    ((∀ v ∈ I, ∀ w ∈ I, B v w = 0) ∨ (B.restrict I).Nondegenerate) ∧
    2 < Module.finrank (ZMod 2) I

/-- Construct the normal component-orbit constituent directly from the faithful
irreducible symplectic action. No representation classification is assumed. -/
theorem componentOrbit_constituents (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (B : LinearMap.BilinForm (ZMod 2) V) (halt : B.IsAlt)
    (hpres : ∀ g v w, B (ρ g v) (ρ g w) = B v w)
    {L : Subgroup G} (hL : IsComponent G L) :
    ComponentOrbitConstituents ρ B L := by
  let H := componentOrbit L ⊤
  let := componentOrbit_top_normal L
  let : Group.IsPerfect H := hL.orbit_isPerfect ⊤
  have hne : H ≠ ⊥ := hL.componentOrbit_top_ne_bot
  obtain ⟨I,hI⟩ := exists_isIrrPlus_of_faithful ρ hf H hne
  exact ⟨fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hf hi H hne,
    subspaceCommutator_top_eq_top_of_normal_faithful_irreducible ρ hf hi H hne,
    I, hI, hI.irreducible_of_normal_restriction ρ hi H,
    hI.conjugates_span_of_normal_restriction ρ hi H,
    hI.eq_or_disjoint_conjugate_of_normal_restriction ρ hi H,
    hI.isotropic_or_nondegenerate_of_normal_restriction ρ hi H B halt hpres,
    hI.finrank_gt_two ρ H⟩

/-- A homogeneous constituent on the actual normal component orbit, retaining
its independent orbit under the specified elementary actor. -/
@[expose] def ComponentOrbitSelection
    (B : LinearMap.BilinForm (ZMod 2) V) (L A : Subgroup G) : Prop :=
  let H := componentOrbit L ⊤
  letI := componentOrbit_top_normal L
  fixedSpace ρ H = ⊥ ∧ subspaceCommutator ρ ⊤ H = ⊤ ∧
  ∃ I : Submodule (ZMod 2) V, ∃ hI : Homogeneous.IsIrrPlusWith ρ H A I,
    IsIrreducible (invariantSubspace ρ H I hI.invariant).toRepresentation ∧
    (⨆ g : G, conjugateSubrepresentation ρ H
      (invariantSubspace ρ H I hI.invariant) g) = ⊤ ∧
    (∀ g : G, I.map (ρ g) = I ∨ Disjoint (I.map (ρ g)) I) ∧
    ((∀ v ∈ I, ∀ w ∈ I, B v w = 0) ∨ (B.restrict I).Nondegenerate) ∧
    2 < Module.finrank (ZMod 2) I ∧ sSupIndep (subspaceOrbit ρ A I)

/-- A.1.42 chooses a homogeneous constituent for any two-subgroup, and the
zero fixed space transfers orbit independence to the original module. -/
theorem componentOrbit_selection (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (B : LinearMap.BilinForm (ZMod 2) V) (halt : B.IsAlt)
    (hpres : ∀ g v w, B (ρ g v) (ρ g w) = B v w)
    {L A : Subgroup G} (hL : IsComponent G L) (hA : IsPGroup 2 A) :
    ComponentOrbitSelection ρ B L A := by
  let H := componentOrbit L ⊤
  let := componentOrbit_top_normal L
  let : Group.IsPerfect H := hL.orbit_isPerfect ⊤
  have hne : H ≠ ⊥ := hL.componentOrbit_top_ne_bot
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hf hi H hne
  have hnorm : A ≤ normalizer (H : Set G) := by rw [H.normalizer_eq_top]; exact le_top
  obtain ⟨I,hI⟩ := Homogeneous.exists_isIrrPlusWith_of_faithful ρ hf H A hne hnorm hA
  exact ⟨hfix,subspaceCommutator_top_eq_top_of_normal_faithful_irreducible ρ hf hi H hne,
    I,hI,hI.isIrrPlus.irreducible_of_normal_restriction ρ hi H,
    hI.isIrrPlus.conjugates_span_of_normal_restriction ρ hi H,
    hI.isIrrPlus.eq_or_disjoint_conjugate_of_normal_restriction ρ hi H,
    hI.isIrrPlus.isotropic_or_nondegenerate_of_normal_restriction ρ hi H B halt hpres,
    hI.isIrrPlus.finrank_gt_two ρ H,hI.independent_orbit_of_fixedSpace_eq_bot ρ hfix⟩

end Representation.BinaryOffender
