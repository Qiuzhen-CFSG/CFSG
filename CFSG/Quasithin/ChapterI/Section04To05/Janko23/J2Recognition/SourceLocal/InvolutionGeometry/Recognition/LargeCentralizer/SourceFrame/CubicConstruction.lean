module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.RootProduct
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.Identification
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.ModelGeometry

/-!
# Constructing the cubic geometry of the canonical source root product

The seed and local census identify the full normalizer of every returning
pair's canonical root product with the explicit UT₃(F₄) semidirect product.
The identification carries the literal R to the model root subgroup and
its embedded center to E. Transporting the model's x-axis and two cubic
tori therefore constructs all the source cubic geometry, including |R| = 64,
Z(R) = E and |C_G(t) ∩ N_G(R)| = 48 for every nonidentity t in U.

The existential theorem supplies the geometry input to the separate marked
frame assembly. It needs only the seed and supplied local census; no
normalizer identification or second-involution centralizer premise remains.

Source: Aschbacher, *Sporadic Groups* (1994), 46.2–46.3 and 46.14,
printed pp.251 and 257–258; the application is in 47.1, pp.259–260.
-/

public section

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame

variable {G : Type*} [Group G] [Finite G] {D : Seed G}

/-- The actual normalizer action constructs the cubic geometry on the
canonical root product of every returning pair. -/
theorem ReturningPair.nonempty_cubicGeometry (P : ReturningPair D) (L : LocalCensus D) :
    Nonempty (CubicGeometry P) := by
  obtain ⟨I⟩ := NormalizerRecognition.nonempty_identification P L
  exact I.cubicGeometry

/-- The earlier §46 geometry required by the marked-frame assembly, with
both the full-normalizer identification and its model geometry discharged. -/
theorem exists_cubicGeometry (D : Seed G) (L : LocalCensus D) :
    ∃ P : ReturningPair D, Nonempty (CubicGeometry P) := by
  obtain ⟨P⟩ := exists_returningPair D
  exact ⟨P, P.nonempty_cubicGeometry L⟩

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame
