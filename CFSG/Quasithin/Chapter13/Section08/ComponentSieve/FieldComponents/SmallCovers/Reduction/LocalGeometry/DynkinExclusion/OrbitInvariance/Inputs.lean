module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance.Models
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance.SectionPassage

/-!
# Orbit statements supplied by the earlier F.9.18 theorem

These are explicit inputs for a fixed source representation. They are the
consumer-facing consequences of F.9.18(3),(4) after K=K₀ and H*=K*T* have been
established; they are not assertions of F.9.18 for arbitrary modules. The
source assembly must discharge them from the genuine F.9 setup, including its
SQTK, C-component and generation hypotheses. Quantification is over every
actual homogeneous Irr⁺ member of that representation, not just the desired
invariant member. Both orbit action images in (3), and all three alternatives
in (4), are retained. The initial list of possible component groups in (4)
is not needed here, since the component is already identified as the triple
cover.

The hatted spaces in (4iii) are literal images in V/C_V(L). Its two-summand
identity, disjointness, element outside the stabilizer and nonisomorphism are
retained. The natural actions have actual equivariant coordinates; the A₇
case retains the source's dimension of the unhatted space.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), F.9.18(3),(4),
printed pp.325–326; application to 13.8.21(2), printed p.956.
-/

@[expose] public section

open Representation Representation.BinaryOffender Subgroup
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance

variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) (L : Subgroup D) [L.Normal]
  (P : Sylow 2 D) (hgen : L ⊔ (P : Subgroup D) = ⊤)

/-- The complete hatted-pair alternative needed from F.9.18(4iii). -/
structure HattedNaturalPair (I : Submodule (ZMod 2) V)
    (hI : IsIrrPlusWith ρ L P I) : Prop where
  model : NaturalModel (quotientImage ρ L I hI.invariant).toRepresentation ∨
    (Nonempty (L ≃* alternatingGroup (Fin 7)) ∧ Module.finrank (ZMod 2) I = 4)
  pair : ∃ t : P, (t : D) ∉ subspaceStabilizer ρ I ∧
    (orbitSpan ρ ⊤ I).map (fixedSpace ρ L).mkQ =
      I.map (fixedSpace ρ L).mkQ ⊔
        (rightConjugate ρ I t).map (fixedSpace ρ L).mkQ ∧
    Disjoint (I.map (fixedSpace ρ L).mkQ)
      ((rightConjugate ρ I t).map (fixedSpace ρ L).mkQ) ∧
    ¬ SameModule (quotientImage ρ L I hI.invariant)
      (quotientImage ρ L (rightConjugate ρ I t)
        (hI.isIrrPlus.map_normalizer ρ (hI.normalizes (P.inv_mem t.property))).choose)

/-- Universal earlier-result inputs on the fixed source module. The caller
must derive these in its genuine F.9 context. No alternative has been removed
on account of the triple-cover identification. -/
structure OrbitInputs : Prop where
  ratio : ∀ (I : Submodule (ZMod 2) V) (hI : IsIrrPlusWith ρ L P I),
    quadraticRatio (imageRepresentation
      (orbitSubrepresentation ρ hI.normalizes hI.isIrrPlus hgen).toRepresentation) ≤ 2 ∧
    quadraticRatio (imageRepresentation
      (orbitSubrepresentation ρ (show (⊤ : Subgroup D) ≤ normalizer (L : Set D) by
        rw [Subgroup.normalizer_eq_top]) hI.isIrrPlus (sup_top_eq L)).toRepresentation) ≤ 2
  alternatives : ∀ (I : Submodule (ZMod 2) V) (hI : IsIrrPlusWith ρ L P I),
    (⊤ ≤ subspaceStabilizer ρ I) ∨
    (orbitSpan ρ P I = I ∧ IsFFModule (imageRepresentation
      (orbitSubrepresentation ρ hI.normalizes hI.isIrrPlus hgen).toRepresentation)) ∨
    HattedNaturalPair ρ L P I hI

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance
