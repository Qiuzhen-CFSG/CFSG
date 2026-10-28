module

public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads.Equivalences

/-!
# The canonical M23 cocode-filtration target

These definitions separate the finite-calculation input from its head-bound
assembly. A certificate module can import this file without importing its
future consumer. The degree set is a requirement on a genuine filtration;
it asserts no constituent calculation.

Source application: Guralnick–Malle, Classification of 2F-modules I,
Proposition 5.1, M23 paragraph, manuscript p.16.
-/

@[expose] public noncomputable section
namespace Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads

/-- The allowed degrees in the concrete finite-filtration certificate. -/
def factorDegrees : Set ℕ := {11, 44, 120}

/-- The only coordinate action requiring an independent filtration calculation. -/
abbrev canonicalCocodeAction := Coordinates.action canonicalMarking false

end Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads
