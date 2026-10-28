module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Construction.CyclicLine.Preparation
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.ReductionClassification.CommonSimpleRigidity
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.PrincipalBlock
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.LocalInertia

/-!
# Common-simple rigidity for principal eleven-block reductions

Every endpoint of the supplied tree satisfies common-simple rigidity, since
the embedded edge already has the full dimension. The principal vertex is
one such endpoint. This argument does not assume a serial vertex family.

The source-group data also discharge all `PrimeOrderInput` fields, including
primitivity of the two literal reduced projectors. We give the exact conditional
application of the remaining normalizer-length and extremal recognition
theorems, with the specified `r.residue`. Their proof obligations remain open;
the conditional application is not a proof of rigidity at an arbitrary vertex.

Source: Feit VII.2.25, printed pp.280 and 304, reduced-module part only.
-/

public section
namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction

open Representation Representation.CyclicDefect.PrimeOrderRealLine
open Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules
open Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.ReductionClassification
open Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree
open Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence

variable {G : Type*} [Group G] [Finite G] {d : OrdinaryData G}

/-- Rigidity at any endpoint of the actual supplied tree. -/
theorem principalBlock_commonSimpleRigidity_at_endpoint (b : PrincipalBlockIdentification d)
    (r : CompatibleRoots b.data ElevenClosure 15960)
    (t : Tree b.data.chi b.data.block 11 10 (principalBlock_rootLift b r))
    (v : {i // i ∈ b.data.block}) (hv : (t.incident v).card = 1) :
    CommonSimpleRigidity t r v :=
  commonSimpleRigidity_of_incident_card_eq_one (by decide) hv

/-- In particular the principal vertex satisfies the exact rigidity predicate. -/
theorem principalBlock_principal_commonSimpleRigidity (b : PrincipalBlockIdentification d)
    (r : CompatibleRoots b.data ElevenClosure 15960)
    (t : Tree b.data.chi b.data.block 11 10 (principalBlock_rootLift b r)) :
    CommonSimpleRigidity t r ⟨b.data.principal, b.data.principal_mem⟩ :=
  principalBlock_commonSimpleRigidity_at_endpoint b r t _ (principalBlock_principal_endpoint b t)

/-- All earlier local block inputs are available at the literal residue map;
neither modular primitivity statement needs an additional hypothesis. -/
theorem principalBlock_rigidity_primeOrderInput (b : PrincipalBlockIdentification d)
    (r : CompatibleRoots b.data ElevenClosure 15960)
    (horder : Nat.card G = 175560) (P : Sylow 11 G) :
    PrimeOrderInput b.data r.residue 15960 P where
  sylow_card := sylow_eleven_card horder P
  cyclic := sylow_eleven_isCyclic horder P
  principal_primitive := reducedPrincipal_isCentrallyPrimitive b.data r.residue
  local_primitive := reducedPrincipal_sylowBrauer_isCentrallyPrimitive b.data r.residue P
  inertial_index := by
    rw [reducedPrincipal_inertialIndex]
    exact sylow_eleven_centralizer_index d horder P
  ordinary_card := principalBlock_card b
  regular_orders := regular_order_dvd_root_order horder

/-- The exact eleven-block application, conditional on the two distinct
remaining source theorems. The local inputs to each are discharged here. -/
theorem principalBlock_commonSimpleRigidity_of_normalizerLength_theorems
    (b : PrincipalBlockIdentification d) (r : CompatibleRoots b.data ElevenClosure 15960)
    (horder : Nat.card G = 175560)
    (t : Tree b.data.chi b.data.block 11 10 (principalBlock_rootLift b r))
    (v : {i // i ∈ b.data.block}) (P : Sylow 11 G)
    (hlength : PrimeOrderInput b.data r.residue 15960 P → VertexNormalizerLengths r P v)
    (hrecognition : PrimeOrderInput b.data r.residue 15960 P →
      ∀ (a b' s l : ℕ)
      (ρ : Representation ElevenClosure G (Fin a → ElevenClosure))
      (σ : Representation ElevenClosure G (Fin b' → ElevenClosure))
      (τ : Representation ElevenClosure G (Fin s → ElevenClosure)),
      (l = 1 ∨ l = 10) →
      Module.IsIndecomposable (MonoidAlgebra ElevenClosure G) ρ.asModule →
      Module.IsIndecomposable (MonoidAlgebra ElevenClosure G) σ.asModule →
      ρ.asAlgebraHom (reducedPrincipal b.data r.residue) = 1 →
      σ.asAlgebraHom (reducedPrincipal b.data r.residue) = 1 →
      HasNormalizerLength P ρ l → HasNormalizerLength P σ l →
      IsIrreducible τ →
      ∀ f : τ.IntertwiningMap ρ, Function.Injective f →
      ∀ g : τ.IntertwiningMap σ, Function.Injective g → Nonempty (ρ.Equiv σ)) :
    CommonSimpleRigidity t r v := by
  have hi := principalBlock_rigidity_primeOrderInput b r horder P
  exact commonSimpleRigidity_of_normalizerLengths P (hlength hi) (hrecognition hi)

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction
