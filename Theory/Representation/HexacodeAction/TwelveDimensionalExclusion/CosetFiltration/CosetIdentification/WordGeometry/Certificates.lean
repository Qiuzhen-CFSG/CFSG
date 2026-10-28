module
public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetFiltration.CosetIdentification.WordGeometry.Witnesses

/-!
# Kernel checks for the fixed subgroup and transporter words

The compact arithmetic certifies the original 45 representative words, all eight
subgroup words, subgroup multiplication and inversion, and the ninety literal
inverse-action transitions. `GroupWords` interprets these equations faithfully
on the actual cover. No diagnostic output is used as a proof oracle.

Source application: Aschbacher–Smith K.1.3, printed p.453 / PDF p.464.
Witness provenance and ATLAS attribution are recorded in `Witnesses`.
-/

@[expose] public section

open Representation.Hexacode.SixDimensional.EvenImage.PairData
namespace Representation.Hexacode.TwelveDimensional.CosetCertificate.CosetIdentification.WordGeometry

theorem representative_checks : ∀ i, wordMatrix (cosetWords i) = representativeMatrix i := by
  decide +kernel

theorem subgroup_checks : ∀ p,
    ((subgroupWords p).map (fun a => wordMatrix (sylowWords a))).foldr mm ident =
      subgroupMatrix p := by
  decide +kernel

theorem subgroup_mul_checks : ∀ a b,
    mm (subgroupMatrix a) (subgroupMatrix b) = subgroupMatrix (subgroupMul a b) := by
  decide +kernel

theorem subgroup_inv_checks : ∀ a,
    mm (subgroupMatrix (subgroupInv a)) (subgroupMatrix a) = ident := by
  decide +kernel

theorem transporter_checks : ∀ j i,
    mm (mm (letterMatrix (j, -1)) (representativeMatrix i))
      (subgroupMatrix (transporterIndex j i)) =
    mm (mpow scalarMatrix (phase j i).val) (representativeMatrix (rowSource j i)) := by
  decide +kernel

end Representation.Hexacode.TwelveDimensional.CosetCertificate.CosetIdentification.WordGeometry
