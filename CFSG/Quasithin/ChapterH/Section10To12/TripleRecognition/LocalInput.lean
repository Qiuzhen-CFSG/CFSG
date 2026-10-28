module

public import CFSG.Quasithin.ChapterH.Section10To12.TripleRecognition.Unitary
public import CFSG.Quasithin.ChapterH.Section10To12.TripleRecognition.Restriction
public import CFSG.Quasithin.ChapterH.Section10To12.TripleLocalGeometry

/-!
# Unitary input for the triple Mathieu local calculation

The faithful action and the actual binary coordinate equivalence constructed
in `Unitary` discharge the unitary premise of `TripleLocalGeometry` for every
genuine triple cover. The compatibility proposition is the literal matrix
action equation, proved below. The imported coordinate theorems also identify
the specified central scalars and the Hermitian form in those coordinates.

For an ambient faithful irreducible module of dimension twelve, the source
hypothesis F*(G) = L supplies normality and hence irreducible restriction.
The resulting input acts on that original module, with its unchanged L-action.
The separate displacement theorem supplies dimension twelve in H.12.1(3).

Source: Aschbacher–Smith H.12.1(1–3), printed pp.393–394 (PDF pp.404–405).
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.ChapterH.Section10To12
open Representation Theory.GroupTheory
open scoped Matrix

namespace IsTripleM22
variable {L V : Type*} [Group L] [Finite L]
  [AddCommGroup V] [Module (ZMod 2) V]
  (hL : IsTripleM22 L) (ρ : Representation (ZMod 2) L V)
  (hf : Function.Injective ρ) [ρ.IsIrreducible]
  (hd : Module.finrank (ZMod 2) V = 12)

/-- The local input on the given module, with a literal coordinate-action proposition. -/
def hermitianRestrictionInput : HermitianRestrictionInput L where
  action := UnitaryModel.unitaryAction hL
  faithful := UnitaryModel.unitaryAction_faithful hL
  compatible := ∀ (g : L) (v : V),
    ((UnitaryModel.unitaryAction hL g).val :
      Matrix (Fin 6) (Fin 6) Theory.SpecificGroups.U6Two.Field) *ᵥ
      UnitaryModel.standardCoordinates hL ρ hf hd v =
        UnitaryModel.standardCoordinates hL ρ hf hd (ρ g v)

/-- The compatibility premise of the local-geometry input is discharged. -/
theorem hermitianRestrictionInput_compatible :
    (hermitianRestrictionInput hL ρ hf hd).compatible :=
  UnitaryModel.unitaryAction_intertwines hL ρ hf hd

end IsTripleM22

namespace TripleRecognition
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]
  (L : Subgroup G) (hL : IsTripleM22 L) (hF : generalizedFitting G = L)
  (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
  (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 12)

/-- The source ambient module supplies the unitary input on its actual component restriction. -/
def hermitianRestrictionInputOfGeneralizedFitting : HermitianRestrictionInput L := by
  let : L.Normal := hF ▸ inferInstance
  let := irreducible_restriction L hL ρ hf hd
  exact hL.hermitianRestrictionInput (ρ.comp L.subtype) (hf.comp L.subtype_injective) hd

/-- Compatibility for the original ambient vectors and the literal restricted action. -/
theorem hermitianRestrictionInputOfGeneralizedFitting_compatible :
    (hermitianRestrictionInputOfGeneralizedFitting L hL hF ρ hf hd).compatible := by
  let : L.Normal := hF ▸ inferInstance
  let := irreducible_restriction L hL ρ hf hd
  exact hL.hermitianRestrictionInput_compatible (ρ.comp L.subtype)
    (hf.comp L.subtype_injective) hd

end TripleRecognition
end CFSG.Quasithin.ChapterH.Section10To12
