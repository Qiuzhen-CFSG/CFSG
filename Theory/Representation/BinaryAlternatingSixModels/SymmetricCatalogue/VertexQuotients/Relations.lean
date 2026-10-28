module

public import Theory.Representation.BinaryDuadStructure.NaturalCover
public import Theory.Representation.BinaryAlternatingSixModels

/-!
# Simple quotients of the S₆ line-relation cover

The existing five-dimensional duad quotient and its natural projection carry
literal S₆ actions. The one-dimensional binary kernel is fixed. A map from
this cover to a simple module either survives on that kernel, giving the
trivial representation, or factors through the marked natural representation.
The argument also holds after pullback along any automorphism of S₆.

This supplies the relation-quotient steps for both vertex modules, without
assuming a simple-module catalogue or irreducibility after restriction to A₆.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), G.5.1–3,
printed pp.342–345; the concrete five-dimensional cover is constructed in
`BinaryDuadStructure.NaturalCover`.
-/

@[expose] public section

open Theory.SpecificGroups.SymmetricSix BinaryPermutation BinaryDuadModule
open BinaryDuadStructure Representation
namespace BinaryAlternatingSix.SymmetricCatalogue.VertexQuotients

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- A fixed nonzero vector identifies a simple binary representation with the trivial model. -/
theorem trivial_of_fixed (ρ : Representation (ZMod 2) S6 V) [IsIrreducible ρ]
    (v : V) (hv : v ≠ 0) (hfix : ∀ g, ρ g v = v) :
    Nonempty (ρ.Equiv trivialSymmetric) := by
  let t : trivialSymmetric.IntertwiningMap ρ := {
    toLinearMap := (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2).smulRight v
    isIntertwining' g := by
      apply LinearMap.ext
      intro a
      change a • v = ρ g (a • v)
      rw [map_smul, hfix] }
  have ht : t ≠ 0 := by
    intro h
    have he := congrArg (fun f : trivialSymmetric.IntertwiningMap ρ => f 1) h
    exact hv (by simpa [t] using he)
  let := trivialSymmetric_irreducible
  exact ⟨(t.ofBijective ((IsIrreducible.bijective_or_eq_zero t).resolve_right ht)).symm⟩

/-- A nonzero map between simple modules gives the required equivalence, in quotient orientation. -/
theorem equiv_of_nonzero {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    {σ : Representation (ZMod 2) S6 U} {ρ : Representation (ZMod 2) S6 V}
    [IsIrreducible σ] [IsIrreducible ρ] (f : σ.IntertwiningMap ρ) (hf : f ≠ 0) :
    Nonempty (ρ.Equiv σ) :=
  ⟨(f.ofBijective ((IsIrreducible.bijective_or_eq_zero f).resolve_right hf)).symm⟩

theorem pointSum_symmetric (g : S6) (u : Full Duad) :
    pointSum (pointAction g u) = firstNatural g (pointSum u) := by
  change (∑ d : Duad, u (g⁻¹ • d) • (polarVector d).val) =
    firstNatural g (∑ d : Duad, u d • (polarVector d).val)
  rw [map_sum]
  simp only [map_smul]
  have hv (d : Duad) : firstNatural g (polarVector d).val =
      (polarVector (g • d)).val := polarAction_vector g d
  simp_rw [hv]
  exact (Equiv.sum_comp (MulAction.toPerm g)
    (fun d => u (g⁻¹ • d) • (polarVector d).val)).symm.trans (by
      simp only [MulAction.toPerm_apply, inv_smul_smul])

theorem lineSpan_symmetric (g : S6) {u : Full Duad} (hu : u ∈ lineSpan) :
    pointAction g u ∈ lineSpan := by
  rw [lineSpan_eq_sup] at hu ⊢
  obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.mp hu
  rw [map_add]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (lineComplementSpan_invariant g hv))
    (Submodule.mem_sup_right (constants_invariant Duad
      (MulAction.toPermHom S6 Duad g) hw))

noncomputable def relationAction : Representation (ZMod 2) S6 LineQuotient :=
  pointAction.quotient lineSpan (fun g _ hu => lineSpan_symmetric g hu)

theorem projection_symmetric (g : S6) (q : LineQuotient) :
    naturalProjection (relationAction g q) = firstNatural g (naturalProjection q) := by
  induction q using Submodule.Quotient.induction_on with
  | H u => exact pointSum_symmetric g u

noncomputable def projectionHom : relationAction.IntertwiningMap firstNatural :=
  naturalProjection.intertwiningMap_of_isIntertwiningMap _ _ projection_symmetric

theorem projection_kernel_fixed {q : LineQuotient} (hq : naturalProjection q = 0)
    (g : S6) : relationAction g q = q := by
  by_cases hz : q = 0
  · simp [hz]
  let K := projectionHom.ker
  have hdim : Module.finrank (ZMod 2) K.toSubmodule = 1 := naturalProjection_ker_finrank
  have hne : (⟨q, hq⟩ : K.toSubmodule) ≠ 0 := fun h => hz (congrArg Subtype.val h)
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one hdim hne
    (K.toRepresentation g ⟨q, hq⟩)
  have han : a ≠ 0 := by
    intro he
    rw [he, zero_smul] at ha
    have hh := congrArg (K.toRepresentation g⁻¹) ha
    simp only [map_zero, Representation.inv_self_apply] at hh
    exact hne hh.symm
  have ha1 : a = 1 := (show ∀ a : ZMod 2, a ≠ 0 → a = 1 by decide) a han
  rw [ha1, one_smul] at ha
  exact (congrArg Subtype.val ha).symm

/-- A simple quotient of the relation module, with any automorphic marking,
is trivial or the correspondingly marked natural module. -/
theorem relation_quotient (α : MulAut S6)
    (ρ : Representation (ZMod 2) S6 V) [IsIrreducible ρ]
    (f : IntertwiningMap (relationAction.comp α.toMonoidHom) ρ) (hf : f ≠ 0) :
    Nonempty (ρ.Equiv trivialSymmetric) ∨
      Nonempty (ρ.Equiv (firstNatural.comp α.toMonoidHom)) := by
  by_cases hk : naturalProjection.ker ≤ f.toLinearMap.ker
  · right
    let E := naturalProjection.quotKerEquivOfSurjective naturalProjection_surjective
    let t : NaturalModule →ₗ[ZMod 2] V :=
      (naturalProjection.ker.liftQ f.toLinearMap hk).comp E.symm.toLinearMap
    have ht (q : LineQuotient) : t (naturalProjection q) = f q := by
      simp only [t, E, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
      rfl
    let T : IntertwiningMap (firstNatural.comp α.toMonoidHom) ρ := {
      toLinearMap := t
      isIntertwining' g := by
        apply LinearMap.ext
        intro v
        obtain ⟨q, rfl⟩ := naturalProjection_surjective v
        change t (firstNatural (α g) (naturalProjection q)) = ρ g (t (naturalProjection q))
        rw [← projection_symmetric, ht, ht]
        exact IntertwiningMap.isIntertwining (relationAction.comp α.toMonoidHom) ρ f g q }
    have hT : T ≠ 0 := by
      intro h
      apply hf
      apply IntertwiningMap.ext
      apply LinearMap.ext
      intro q
      exact (ht q).symm.trans (congrArg (fun z => z (naturalProjection q)) h)
    let : IsIrreducible (firstNatural.comp α.toMonoidHom) :=
      (irreducible_comp_surjective_iff α.toMonoidHom α.surjective firstNatural).mpr
        firstNatural_irreducible
    exact equiv_of_nonzero T hT
  · left
    have hex : ∃ q, naturalProjection q = 0 ∧ f q ≠ 0 := by
      by_contra! h
      exact hk h
    obtain ⟨q, hq, hn⟩ := hex
    apply trivial_of_fixed ρ (f q) hn
    intro g
    rw [← IntertwiningMap.isIntertwining (relationAction.comp α.toMonoidHom) ρ f]
    exact congrArg f (projection_kernel_fixed hq (α g))

/-- The relation quotient applies directly to an intertwiner on the fifteen points. -/
theorem point_relations (α : MulAut S6)
    (ρ : Representation (ZMod 2) S6 V) [IsIrreducible ρ]
    (f : IntertwiningMap (pointAction.comp α.toMonoidHom) ρ) (hf : f ≠ 0)
    (hline : ∀ s, f (line s) = 0) :
    Nonempty (ρ.Equiv trivialSymmetric) ∨
      Nonempty (ρ.Equiv (firstNatural.comp α.toMonoidHom)) := by
  have hk : lineSpan ≤ f.toLinearMap.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s, rfl⟩
    exact hline s
  let q : IntertwiningMap (relationAction.comp α.toMonoidHom) ρ := {
    toLinearMap := lineSpan.liftQ f.toLinearMap hk
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      induction x using Submodule.Quotient.induction_on with
      | H x => exact IntertwiningMap.isIntertwining (pointAction.comp α.toMonoidHom) ρ f g x }
  apply relation_quotient α ρ q
  intro h
  apply hf
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact congrArg (fun z : IntertwiningMap (relationAction.comp α.toMonoidHom) ρ =>
    z (lineSpan.mkQ x)) h

end BinaryAlternatingSix.SymmetricCatalogue.VertexQuotients
