module

public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Trio.Spaces
public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Trio.FixedCommutators
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.TensorSection
public import Theory.Representation.RepEquiv

/-!
# The standard trio middle section as a native tensor space

The Theory layer constructs the native first-moment map on the nine-dimensional
pair space. The fixed-space calculation identifies its explicit affine-plane
kernel with the intrinsic three-space, so the quotient has a checked linear
equivalence with the literal tensor target. Even octad parity cancels the
affine translations, proving equivariance through the actual native quotient.
The independent tensor irreducibility calculation then proves that this is a
chief factor. The imported fixed-space theorem discharges the flag inclusion,
so no additional premise is needed for the standard marking.

Source: Aschbacher–Smith H.15.6(3), printed p.401, with H.14.1(3), printed
p.396. We use the actual flag section `V₉/V₃`, correcting the printed `V₉/V`.
Arbitrary-trio transport and the full source theorem belong to the parent
assembly.
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
open MathieuCode
open MathieuCode.TrioCalculation
open scoped BigOperators TensorProduct
namespace CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
noncomputable section

abbrev F := ZMod 2
abbrev A := QuotientConstruction.Vector
abbrev NT := NaturalTensor
abbrev standardPairSpace := trioPairSpace standardTrio

/-- The native first-moment map restricted to the actual standard pair space. -/
noncomputable def standardPairMoment : standardPairSpace →ₗ[F] NT :=
  pairMoment

lemma standardPairMoment_surjective : Function.Surjective standardPairMoment := by
  exact pairMoment_surjective

/-- The intrinsic fixed-space kernel in the pair-space subtype is the affine-plane range. -/
lemma standardSectionKernel_eq_planeRange :
    (trioFixedSpace standardTrio).comap (trioPairSpace standardTrio).subtype =
      MathieuCode.TrioCalculation.standardPlanePairMap.range := by
  ext v
  constructor
  · intro hv
    rw [standard_trioFixedSpace_eq_planeRange] at hv
    obtain ⟨a, ha⟩ := hv
    exact ⟨a, Subtype.ext ha⟩
  · rintro ⟨a, ha⟩
    rw [standard_trioFixedSpace_eq_planeRange]
    exact ⟨a, congrArg Subtype.val ha⟩

/-- The native first-moment quotient is the tensor space. -/
noncomputable def standardSectionEquiv :
    TrioSection standardTrio ≃ₗ[F] NT := by
  let q :
      (MathieuCode.TrioCalculation.standardPairSpace ⧸
        MathieuCode.TrioCalculation.standardPlanePairMap.range) ≃ₗ[F]
      (trioPairSpace standardTrio ⧸
        (trioFixedSpace standardTrio).comap (trioPairSpace standardTrio).subtype) :=
    Submodule.Quotient.equiv _ _ (LinearEquiv.refl F _) (by
      rw [standardSectionKernel_eq_planeRange]
      exact Submodule.map_id _)
  exact q.symm.trans MathieuCode.TrioCalculation.pairMomentQuotientEquiv


lemma standardSectionEquiv_mk (v : trioPairSpace standardTrio) :
    standardSectionEquiv
      (((trioFixedSpace standardTrio).comap (trioPairSpace standardTrio).subtype).mkQ v) =
      standardPairMoment v := by
  rfl

lemma standardSectionEquiv_intertwines (g : trioStabilizer standardTrio)
    (v : TrioSection standardTrio) :
    standardSectionEquiv (trioSectionRepresentation standardTrio g v) =
      standardTensorRepresentation g (standardSectionEquiv v) := by
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    change cocodeMoment (cocodeRepresentation g.val v.val) =
      standardTensorRepresentation g (cocodeMoment v.val)
    exact cocodeMoment_equivariant g v.val v.property

/-- The middle factor is identified with the specified natural tensor action. -/
def standardSectionRepresentationEquiv :
    (trioSectionRepresentation standardTrio).Equiv standardTensorRepresentation :=
  Representation.Equiv.mk standardSectionEquiv (fun g => by
    apply LinearMap.ext
    intro v
    exact standardSectionEquiv_intertwines g v)

theorem standard_trioSection_irreducible :
    Representation.IsIrreducible (trioSectionRepresentation standardTrio) :=
  Representation.RepEquiv.irreducible_of_euqiv
    (Representation.RepEquiv.ofRepresentationEquiv standardSectionRepresentationEquiv)
    standardTensorRepresentation_irreducible

end
end CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
