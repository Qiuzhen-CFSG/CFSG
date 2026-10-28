module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.DistanceTwoGeometry
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.PolarPointResidues.Geometry

/-!
# The original D-system supplies the local polar facts

The marked A₆/S₆ quotient identifies the actual point residue, in either
orientation, with the binary symplectic quadrangle. Its eight-object orbit,
actual stabilizer lifts and projection property are exactly the three
inputs used by the global distance and nonsingular-triple arguments.

Source: Aschbacher–Smith I.5.4(1) and I.5.9, printed pp.420–422.
-/

public section
namespace Quasithin.I5.DSystem
variable {G : Type*} [Group G] (S : DSystem .C3 G)

theorem source_local_polar_facts : S.LocalPolarFacts where
  noncoplanar_card := PolarPointResidues.noncoplanar_eight S
  transporter := PolarPointResidues.noncoplanar_transporter S
  projection := PolarPointResidues.projection S

end Quasithin.I5.DSystem
