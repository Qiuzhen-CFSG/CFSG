module

public import CFSG.Quasithin.ChapterH.Section10To12.TripleDisplacement.Odd
public import CFSG.Quasithin.ChapterH.Section10To12.TripleRecognition.LocalInput

/-!
# Discharging the module premises of the H.12 local calculation

For the original ambient representation, assemble `TripleModuleInput` from the
proved recognition, unitary and displacement theorems. The cubic field uses
exactly the component subtype map, and the involution field quantifies over
all ambient involutions. The compatibility theorem retains the actual unitary
coordinate identity supplied by recognition. No numerical or model premise
is added to the source assumptions.

Source: Aschbacher–Smith H.12.1, printed pp.393–394 (PDF pp.404–405).
The later subgroup and local-geometry conclusions remain with their owners.
-/

public section
open Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterH.Section10To12.TripleDisplacement
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (L : Subgroup G) (hL : IsTripleM22 L) (hF : generalizedFitting G = L)
  (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
  (hρ : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 12)

/-- The source hypotheses construct the full module input used by local geometry. -/
@[expose] noncomputable def localModuleInput : TripleModuleInput G V where
  component := L
  triple := hL
  representation := ρ
  faithful := hρ
  irreducible := inferInstance
  dimension := hd
  hermitian := TripleRecognition.hermitianRestrictionInputOfGeneralizedFitting L hL hF ρ hρ hd
  cubic_displacement := noncentral_three_fixedCodim_eq_eight L hL hF ρ hρ hd
  involution_displacement := four_le_fixedCodim_involution L hL hF ρ hρ hd

/-- The assembled local input satisfies the literal unitary coordinate identity. -/
theorem localModuleInput_compatible :
    (localModuleInput L hL hF ρ hρ hd).hermitian.compatible :=
  TripleRecognition.hermitianRestrictionInputOfGeneralizedFitting_compatible L hL hF ρ hρ hd

end CFSG.Quasithin.ChapterH.Section10To12.TripleDisplacement
