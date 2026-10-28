module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.RootWeights
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SplitTorus
public import Theory.AlgebraicGroup.RootSubgroups.Cocharacter
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.ChevalleyVersions
public import Theory.AlgebraicGroup.RootSystems.F4RootPairingULift

/-!
# The F4 coroot convention obstruction

GLS3 1.12.1 defines `h(t) = n(1)⁻¹ n(t)` and uses inverse conjugation
`x^h = h⁻¹ x h`, so a root evaluates on its own coroot as `t²`.
The existing representation convention `algebraicCorootElement` is instead
`n(t) n(1)⁻¹`. Its diagonal parameter is inverted, and the literal root weight
evaluates on it as `t⁻²`. Consequently no realized root datum on any torus
of this carrier can identify both a literal simple root subgroup and its
cocharacter with that word at the same parameter. This is an obstruction to
that identification contract, not to the existence of the F4 root model.

The proof uses the actual root parametrization and conjugation, then uniqueness
of integral Laurent exponents, valid also in characteristic two. It makes no
assumption identifying the torus or its root weights with the split coordinates.
Sources: GLS3 1.9.2, 1.9.5(d), 1.9.6 and 1.12.1, especially
`refs/KGroup/GLS3/Chapter1.tex`, lines 506 and 532.
-/

public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]
local instance : AlgebraicGroup (F4Chevalley.splitTorus (k := F)).carrierVariety :=
  (F4Chevalley.splitTorus (k := F)).carrierAlgebraicGroup

/-- Evaluation on the representation convention gives the negative Cartan exponent. -/
theorem rootWeight_simpleCoroot (r : F4Chevalley.Root) (i : Fin 4) :
    WeightCocharacterEquation (F4Chevalley.splitTorus (k := F))
      (F4Chevalley.rootWeight r) (F4Chevalley.splitTorusSimpleCoroot i)
      (-typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex i)) := by
  intro t
  rw [F4Chevalley.rootWeight_pointCharacter]
  change (↑(∏ j, (dPointEquiv 4 ((F4Chevalley.splitTorusIso (k := F)).inv.onPoints
    ((F4Chevalley.splitTorusCocharacter (F4Chevalley.simpleCorootExponent i)).onPoints t)) j) ^
      F4Chevalley.torusRootExponent r j) : F) = _
  rw [F4Chevalley.splitTorusCocharacter_inverse_apply]
  simp only [dCharacterTupleMorphism_apply, Fin.prod_univ_one]
  simp [F4Chevalley.simpleCorootExponent, F4Chevalley.torusRootExponent]

/-- Inverting the representation-coroot parameter restores the Cartan exponent. -/
theorem rootWeight_simpleCoroot_inverse_parameter (r : F4Chevalley.Root) (i : Fin 4)
    (t : Variety.Point (KMult F)) :
    (F4Chevalley.rootWeight (k := F) r).pointCharacter
      ((F4Chevalley.splitTorusSimpleCoroot i).onPoints t⁻¹) =
        (dPointEquiv 1 t 0 : F) ^
          typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex i) := by
  let f : Variety.Point (KMult F) →* (Fin 1 → Fˣ) :=
    { toFun := dPointEquiv 1
      map_one' := dPointEquiv_one 1
      map_mul' := dPointEquiv_mul 1 }
  have hinv : dPointEquiv 1 t⁻¹ = (dPointEquiv 1 t)⁻¹ := map_inv f t
  rw [rootWeight_simpleCoroot r i t⁻¹, hinv]
  simp

/-- In particular the diagonal exponent on the same root is minus two. -/
theorem rootWeight_simpleCoroot_self (i : Fin 4) :
    WeightCocharacterEquation (F4Chevalley.splitTorus (k := F))
      (F4Chevalley.rootWeight (typeF4SimpleRootIndex i))
      (F4Chevalley.splitTorusSimpleCoroot i) (-2) := by
  simpa only [RootPairing.pairingIn_same] using
    rootWeight_simpleCoroot (F := F) (typeF4SimpleRootIndex i) i

/-- The existing positive representation coroot scales its own root by `t⁻²`. -/
theorem algebraicCorootElement_self_conjugation (i : Fin 4)
    (t : Variety.Point (KMult F)) (a : F) :
    (algebraicCorootElement (typeF4SimpleRootIndex i) (dPointEquiv 1 t 0))⁻¹ *
      algebraicRootElement (typeF4SimpleRootIndex i) a *
      algebraicCorootElement (typeF4SimpleRootIndex i) (dPointEquiv 1 t 0) =
      algebraicRootElement (typeF4SimpleRootIndex i)
        ((dPointEquiv 1 t 0 : F) ^ (-2 : ℤ) * a) := by
  have h := F4Chevalley.rootMorphism_splitTorus_conjugation
    (typeF4SimpleRootIndex i) a ((F4Chevalley.splitTorusSimpleCoroot i).onPoints t)
  change ((F4Chevalley.splitTorus (k := F)).inclusion.onPoints _)⁻¹ *
    algebraicRootElement _ a * (F4Chevalley.splitTorus (k := F)).inclusion.onPoints _ =
      algebraicRootElement _ _ at h
  rw [splitTorusSimpleCoroot_eq_algebraicCoroot,
    rootWeight_simpleCoroot_self i t] at h
  exact h

/-- The prescribed root subgroup and same-parameter representation coroot
cannot belong to a realized datum, even on an arbitrary different torus. -/
theorem no_realization_with_algebraicCorootElement
    {T : ClosedSubgroup (F4Chevalley.Carrier (k := F))}
    (D : RootGroupData (F4Chevalley.Carrier (k := F)) T)
    (hD : D.IsRealization) (α : D.Root) (i : Fin 4)
    (hroot : D.rootSubgroup α = F4Chevalley.rootSubgroup (typeF4SimpleRootIndex i))
    (hcoroot : letI := T.carrierAlgebraicGroup
      ∀ t : Variety.Point (KMult F),
      T.includePoint ((D.rootCocharacter α).onPoints t) =
        algebraicCorootElement (typeF4SimpleRootIndex i) (dPointEquiv 1 t 0)) : False := by
  let _ := T.carrierAlgebraicGroup
  have hweight := (hD.2.2.1 α).2
  rw [hroot] at hweight
  have hminus : WeightCocharacterEquation T (D.rootWeight α) (D.rootCocharacter α) (-2) := by
    intro t
    have h := hweight (F4Chevalley.rootParametrization (typeF4SimpleRootIndex i))
      1 ((D.rootCocharacter α).onPoints t)
    rw [F4Chevalley.rootParametrization_include_value,
      F4Chevalley.rootParametrization_include_value, hcoroot] at h
    change (algebraicCorootElement _ _)⁻¹ * algebraicRootElement _ 1 *
      algebraicCorootElement _ _ = algebraicRootElement _ _ at h
    rw [algebraicCorootElement_self_conjugation] at h
    have hp := F4Chevalley.rootMorphism_injective (typeF4SimpleRootIndex i) h
    have ha := congrArg (fun q : Variety.Point (KPlus F) => q.val PUnit.unit) hp
    change (dPointEquiv 1 t 0 : F) ^ (-2 : ℤ) * 1 =
      (D.rootWeight α).pointCharacter ((D.rootCocharacter α).onPoints t) * 1 at ha
    simpa only [mul_one] using ha.symm
  have hplus : WeightCocharacterEquation T (D.rootWeight α) (D.rootCocharacter α) 2 := by
    have h := hD.rootWeight_rootCocharacter α α
    rwa [hD.2.2.2.2.2.2.1 α] at h
  have h := (weightCocharacterEquation_existsUnique T (D.rootWeight α)
    (D.rootCocharacter α)).unique hminus hplus
  norm_num at h

/-- The requested F4 model identifications already contradict one simple root;
changing the maximal torus or the transported base cannot repair them. -/
theorem no_rootSystemModel_with_algebraicCorootElement
    (M : RootSystemModel typeF4RootPairingULift (F4Chevalley.Carrier (k := F)))
    (hroot : ∀ r : F4Chevalley.Root,
      M.rootData.rootSubgroup (M.rootEquiv.symm ⟨r⟩) = F4Chevalley.rootSubgroup r)
    (hcoroot : letI := M.torus.carrierAlgebraicGroup
      ∀ (i : Fin 4) (t : Variety.Point (KMult F)),
        M.torus.includePoint ((M.rootData.rootCocharacter
          (M.rootEquiv.symm ⟨typeF4SimpleRootIndex i⟩)).onPoints t) =
          algebraicCorootElement (typeF4SimpleRootIndex i) (dPointEquiv 1 t 0)) : False := by
  exact no_realization_with_algebraicCorootElement M.rootData M.realization
    (M.rootEquiv.symm ⟨typeF4SimpleRootIndex 0⟩) 0 (hroot _) (hcoroot 0)

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel
