module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.NaturalSections
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.SourceActions.Geometry
public import Theory.Representation.BinaryPermutation.FiveTensorQuadratic
public import Theory.Representation.BinaryPermutationAlternatingActions


/-!
# Marked five-letter coordinates on the literal section

The B.4.2(5) action equivalence marks A₅ inside the offender-generated S₅.
Its module equivalence, followed by the odd-degree core equivalence, gives
compatible A₅ coordinates. The inverted-cubic section construction then
intertwines both K and the embedded S₃ on W/(C∩W).

`ConstituentRealization` retains the actual actor, its surjection onto the
faithful constituent group, and the original quotient map. `FactorCoordinates`
intertwines only K times the specified S₃. Neither interface asserts an
isomorphism for the whole ambient group or removes a central section.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.2(5),
printed p.86, and the external alternative of 13.8.20, printed p.954.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender InvertedCubicTensor
open scoped TensorProduct
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction

variable {D E N M : Type*} [Group D] [Group E]
  [AddCommGroup N] [Module (ZMod 2) N] [AddCommGroup M] [Module (ZMod 2) M]
  (σ : Representation (ZMod 2) E N) (J L : Subgroup E)
  (e : MarkedActionEquiv σ J L (BinaryPermutation.naturalRepresentation (Fin 5))
    (alternatingGroup (Fin 5)))

/-- The marked component coordinates use the same five-letter marking as the offender group. -/
def componentEquiv (b : D ≃* L) : D ≃* alternatingGroup (Fin 5) :=
  b.trans e.subgroupEquiv

/-- Convert the classified natural quotient to the even-weight five-letter core. -/
def coreCoordinates (a : M ≃ₗ[ZMod 2] N) : M ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 5) :=
  (a.trans e.action.linearEquiv).trans (BinaryPermutation.coreEquivNatural (Fin 5) (by decide)).symm

/-- The constituent marking survives conversion from the quotient model to the core. -/
theorem coreCoordinates_equivariant (τ : Representation (ZMod 2) D M)
    (b : D ≃* L) (a : M ≃ₗ[ZMod 2] N)
    (ha : ∀ k v, a (τ k v) = σ (b k) (a v)) (k : D) (v : M) :
    coreCoordinates σ J L e a (τ k v) =
      BinaryPermutation.alternatingCoreRepresentation (Fin 5)
        (componentEquiv σ J L e b k) (coreCoordinates σ J L e a v) := by
  let c := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
  apply c.injective
  change c (c.symm (e.action.linearEquiv (a (τ k v)))) =
    c (BinaryPermutation.coreRepresentation (Fin 5) (e.subgroupEquiv (b k)).val
      (c.symm (e.action.linearEquiv (a v))))
  rw [c.apply_symm_apply, ha]
  have he := e.action.intertwines (⟨b k, e.contained (b k).property⟩ : J) (a v)
  change e.action.linearEquiv (σ (b k) (a v)) = _ at he
  rw [e.compatible] at he
  rw [he, BinaryPermutation.coreEquivNatural_equivariant, c.apply_symm_apply]

variable {G U : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) G U) (K : Subgroup G)
  (s : S₃ →* G) (hs : ∀ (k : K) g, Commute (k : G) (s g))
  (C W : Subrepresentation ρ)

/-- Actual coordinates on W/(C∩W), before eliminating the central sections. -/
def sectionCoordinates
    (a : SectionMultiplicity ρ s C W ≃ₗ[ZMod 2] N)
    (hgen : subspaceCommutator ρ ⊤ ((alternatingGroup (Fin 3)).map s) = ⊤) :
    SectionSpace ρ C W ≃ₗ[ZMod 2]
      BinaryPermutation.core (Fin 5) ⊗[ZMod 2] BinaryPermutation.core (Fin 3) :=
  modelCoordinates ρ s C W (coreCoordinates σ J L e a) hgen

set_option backward.isDefEq.respectTransparency false in
/-- The section coordinates intertwine every element of K times the embedded S₃. -/
theorem sectionCoordinates_equivariant
    (b : K ≃* L) (a : SectionMultiplicity ρ s C W ≃ₗ[ZMod 2] N)
    (hgen : subspaceCommutator ρ ⊤ ((alternatingGroup (Fin 3)).map s) = ⊤)
    (ha : ∀ k v,
      a (sectionMultiplicityAction ρ K.subtype s hs C W k v) = σ (b k) (a v))
    (k : K) (g : S₃) (v : SectionSpace ρ C W) :
    sectionCoordinates σ J L e ρ s C W a hgen
        (sectionRepresentation ρ C W (k.val * s g) v) =
      BinaryPermutation.FiveTensorQuadratic.tensorAction
        (BinaryPermutation.coreRepresentation (Fin 3))
        ((componentEquiv σ J L e b k).val, g)
        (sectionCoordinates σ J L e ρ s C W a hgen v) := by
  obtain ⟨z, rfl⟩ := (sectionTensorEquiv ρ s C W hgen).surjective v
  have he := congrArg (sectionCoordinates σ J L e ρ s C W a hgen)
    (sectionTensorEquiv_equivariant ρ K.subtype s hs C W hgen k g z)
  apply he.symm.trans
  simp only [sectionCoordinates, modelCoordinates, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]
  clear he
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul i n =>
    simp only [HigherFieldBorelFixedSpaces.externalTensor, Representation.tprod_apply,
      MonoidHom.comp_apply, TensorProduct.map_tmul, TensorProduct.congr_tmul,
      LinearEquiv.refl_apply]
    rw [coreCoordinates_equivariant σ J L e _ b a ha]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]


/-- Coordinates intertwining the component and the specified commuting S₃ only.
Extending these coordinates to every ambient actor is a separate theorem. -/
structure FactorCoordinates {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D) (s : S₃ →* D) where
  component : K ≃* alternatingGroup (Fin 5)
  moduleEquiv : V ≃ₗ[ZMod 2]
    BinaryPermutation.core (Fin 5) ⊗[ZMod 2] BinaryPermutation.core (Fin 3)
  intertwines : ∀ (k : K) (g : S₃) v,
    moduleEquiv (ρ (k.val * s g) v) =
      BinaryPermutation.FiveTensorQuadratic.tensorAction
        (BinaryPermutation.coreRepresentation (Fin 3))
        ((component k).val, g) (moduleEquiv v)

/-- Realization of a faithful constituent action on the literal central quotient.
The actor is a subgroup of the actual ambient group (in the source, K*T*).
Both the component inclusion and the quotient map are retained. -/
structure ConstituentRealization {D V E N : Type*} [Group D]
    [AddCommGroup V] [Module (ZMod 2) V] [Group E]
    [AddCommGroup N] [Module (ZMod 2) N]
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D)
    (σ : Representation (ZMod 2) E N) (L : Subgroup E) where
  actor : Subgroup D
  contains : K ≤ actor
  space : Submodule (ZMod 2) V
  stable : actor ≤ subspaceStabilizer ρ space
  irrPlus : IsIrrPlus ρ K space
  groupMap : actor →* E
  surjective : Function.Surjective groupMap
  component : K ≃* L
  component_map : ∀ k : K, groupMap ⟨k, contains k.property⟩ = (component k : E)
  linearEquiv : centralQuotient ρ K space ≃ₗ[ZMod 2] N
  intertwines : ∀ (g : actor) (v : space),
    linearEquiv (Submodule.Quotient.mk
      (⟨ρ g v, (stable g.property v).mpr v.property⟩ : space)) =
        σ (groupMap g) (linearEquiv (Submodule.Quotient.mk v))

/-- The realized action restricts to the chosen component equivalence. -/
theorem ConstituentRealization.component_intertwines
    {D V E N : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    [Group E] [AddCommGroup N] [Module (ZMod 2) N]
    {ρ : Representation (ZMod 2) D V} {K : Subgroup D}
    {σ : Representation (ZMod 2) E N} {L : Subgroup E}
    (r : ConstituentRealization ρ K σ L) (k : K) (v : centralQuotient ρ K r.space) :
    r.linearEquiv (centralQuotientRepresentation ρ K r.space r.irrPlus.choose k v) =
      σ (r.component k) (r.linearEquiv v) := by
  induction v using Submodule.Quotient.induction_on with | _ v =>
  have h := r.intertwines ⟨k, r.contains k.property⟩ v
  rw [r.component_map] at h
  exact h

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction

end
