module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.F4ChevalleySplitTorus
public import Theory.AlgebraicGroup.RootSubgroups.Defs

/-!
# Root weights of the literal F4 root subgroups

The regular inverse of each integral root curve restricts to the closed F4
carrier, giving its additive parametrization. The diagonal conjugation formula
then identifies its character, independently of the choice of parametrization.
These are the root-subgroup and weight assertions of GLS3 1.9.1–1.9.3; neither
maximality of the torus nor exhaustiveness of its roots is assumed here.
-/

public noncomputable section

open Theory.AlgebraicGroup.StandardRootSystem
namespace Theory.AlgebraicGroup.F4Chevalley
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

local instance : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
  (splitTorus (k := k)).carrierAlgebraicGroup

/-- The ambient root-recovery polynomial restricts to the closed carrier. -/
theorem rootMorphism_coordinate_preimage (r : Root) :
    ∀ c : (KPlus k).Coordinates,
      ∃ q : Variety.PolynomialFunction (Carrier (k := k)),
        Variety.PolynomialFunction.pullback (rootMorphism r).toVariety q =
          Variety.PolynomialFunction.ofPolynomial (KPlus k) (MvPolynomial.X c) := by
  intro c
  obtain ⟨q, hq⟩ := RootPairing.IntegralGeckConstruction.rootMorphism_coordinate_preimage
    (P := typeF4RootPairing) (b := typeF4RootPairing_base) (k := k) r c
  refine ⟨Variety.PolynomialFunction.pullback (ambientClosedCarrier (k := k)).inclusion.toVariety q, ?_⟩
  apply Variety.PolynomialFunction.ext
  intro x
  change q ((ambientClosedCarrier (k := k)).inclusion.onPoints
    ((rootMorphism r).onPoints x)) = _
  rw [rootMorphism_inclusion_apply]
  exact congrArg (fun f : Variety.PolynomialFunction (KPlus k) => f x) hq

/-- The canonical additive parametrization of the literal root subgroup. -/
def rootParametrization (r : Root) :
    let _ := (rootSubgroup (k := k) r).carrierAlgebraicGroup
    OneParameterParametrization (rootSubgroup (k := k) r).carrierVariety := by
  let _ := (rootSubgroup (k := k) r).carrierAlgebraicGroup
  exact Classical.choose ((rootMorphism r).iso_imageClosedSubgroup_of_coordinate_preimage
    (rootMorphism_injective r) (rootMorphism_coordinate_preimage r))

/-- Each literal F4 root subgroup is a one-parameter algebraic group. -/
theorem rootSubgroup_isOneParameter (r : Root) :
    let _ := (rootSubgroup (k := k) r).carrierAlgebraicGroup
    IsOneParameterGroup (rootSubgroup (k := k) r).carrierVariety :=
  ⟨rootParametrization r⟩

lemma rootParametrization_hom (r : Root) :
    let _ := (rootSubgroup (k := k) r).carrierAlgebraicGroup
    (rootParametrization (k := k) r).hom =
      (rootMorphism r).codRestrictClosedSubgroup (rootSubgroup r)
        (fun y => ⟨y, rfl⟩) := by
  let _ := (rootSubgroup (k := k) r).carrierAlgebraicGroup
  exact Classical.choose_spec ((rootMorphism r).iso_imageClosedSubgroup_of_coordinate_preimage
    (rootMorphism_injective r) (rootMorphism_coordinate_preimage r))

lemma rootParametrization_include_value (r : Root) (a : k) :
    let _ := (rootSubgroup (k := k) r).carrierAlgebraicGroup
    (rootSubgroup (k := k) r).includePoint ((rootParametrization r).value a) =
      (rootMorphism r).onPoints (kPlusPoint a) := by
  let _ := (rootSubgroup (k := k) r).carrierAlgebraicGroup
  change (rootSubgroup (k := k) r).inclusion.onPoints
    ((rootParametrization r).hom.onPoints (kPlusPoint a)) = _
  rw [rootParametrization_hom]
  exact (rootMorphism r).codRestrictClosedSubgroup_inclusion_apply
    (rootSubgroup r) (fun y => ⟨y, rfl⟩) (kPlusPoint a)

/-- The character for inverse conjugation on the literal root curve. -/
def rootWeight (r : Root) : TorusWeight (splitTorus (k := k)) :=
  splitTorusCharacter (torusRootExponent r)

lemma rootWeight_pointCharacter (r : Root)
    (s : Variety.Point (splitTorus (k := k)).carrierVariety) :
    (rootWeight (k := k) r).pointCharacter s =
      (↑(∏ i, (dPointEquiv 4 ((splitTorusIso (k := k)).inv.onPoints s) i) ^
        torusRootExponent r i) : k) :=
  congrArg Units.val (splitTorusCharacter_apply_point (torusRootExponent r) s)

/-- Inverse conjugation multiplies the additive root parameter by its weight. -/
theorem rootMorphism_splitTorus_conjugation (r : Root) (a : k)
    (s : Variety.Point (splitTorus (k := k)).carrierVariety) :
    ((splitTorus (k := k)).includePoint s)⁻¹ *
      (rootMorphism r).onPoints (kPlusPoint a) * (splitTorus (k := k)).includePoint s =
      (rootMorphism r).onPoints (kPlusPoint ((rootWeight (k := k) r).pointCharacter s * a)) := by
  rw [rootWeight_pointCharacter]
  have h := splitTorusMorphism_root_conjugation
    ((splitTorusIso (k := k)).inv.onPoints s) r a
  rw [splitTorusIso_inverse_apply] at h
  exact h

/-- Each root curve is invariant under the concrete rank-four torus. -/
theorem rootSubgroup_invariant (r : Root) :
    IsClosedSubgroupInvariant (splitTorus (k := k)) (rootSubgroup (k := k) r) := by
  intro t ht x hx
  let s : Variety.Point (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).pointEquiv.symm ⟨t, ht⟩
  have hs : (splitTorus (k := k)).includePoint s = t := by
    change ((splitTorus (k := k)).pointEquiv s).val = t
    simp [s]
  change x ∈ (rootMorphism r).image at hx
  rcases hx with ⟨q, rfl⟩
  have hq : q = kPlusPoint (q.val PUnit.unit) := by
    apply (additiveGroupPointEquiv k).injective
    rfl
  rw [hq, ← hs, rootMorphism_splitTorus_conjugation]
  exact ⟨kPlusPoint ((rootWeight (k := k) r).pointCharacter s * q.val PUnit.unit), rfl⟩

/-- The same character scales every algebraic additive parametrization. -/
theorem rootWeightEquation (r : Root) :
    RootWeightEquation (splitTorus (k := k)) (rootSubgroup (k := k) r)
      (rootWeight (k := k) r) := by
  intro y t s
  let _ := (rootSubgroup (k := k) r).carrierAlgebraicGroup
  let p := rootParametrization (k := k) r
  obtain ⟨c, hc, _⟩ := oneParameterParametrization_eq_rescale p y
  rw [show (rootSubgroup (k := k) r).includePoint (y.value t) =
      (rootMorphism r).onPoints (kPlusPoint (c * t)) by
        rw [hc.2, rootParametrization_include_value]]
  rw [show (rootSubgroup (k := k) r).includePoint
      (y.value ((rootWeight (k := k) r).pointCharacter s * t)) =
      (rootMorphism r).onPoints
        (kPlusPoint (c * ((rootWeight (k := k) r).pointCharacter s * t))) by
        rw [hc.2, rootParametrization_include_value]]
  rw [rootMorphism_splitTorus_conjugation]
  congr 2
  ring

/-- The literal root subgroup and its explicit weight satisfy the root contract. -/
theorem rootSubgroup_package (r : Root) :
    IsTorusRootSubgroup (splitTorus (k := k)) (rootSubgroup (k := k) r) ∧
      RootWeightEquation (splitTorus (k := k)) (rootSubgroup (k := k) r)
        (rootWeight (k := k) r) :=
  ⟨⟨rootSubgroup_invariant r, rootSubgroup_isOneParameter r⟩, rootWeightEquation r⟩

end Theory.AlgebraicGroup.F4Chevalley
