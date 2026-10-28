module

public import Theory.SpecificGroups.PSL3.PointRadicalGeneration
public import Theory.Representation.SpecialLinearThreeFrameGeometry.RootGeneration

/-!+# Generation by three independent point radicals

The concrete radical fixing a point and having all displacements in it is
exactly the point radical in the natural SL₃ frame geometry. Thus the six-root
generation theorem shows that radicals at three independent lines generate
SL₃(F). This uses the actual matrix subgroups over any field, including F₂.

For a marked right conjugator, `radical_conjugate` identifies its conjugate
radical with the radical at the inverse-matrix translate of the point. The
source application retains those translates and the original marks in
`LinearThree.Structure.Radical.Geometry.Generation`.

Source: Aschbacher–Smith, G.2.5(2), printed pp.335–336 / PDF pp.346–347,
using the frame roots of G.1.1–2, printed p.327 / PDF p.338.
-/

public section
open Matrix Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.PointRadicalGeneration
variable {F : Type*} [Field F]

/-- The two concrete radical definitions have the same matrix conditions. -/
theorem radical_eq_frame_pointRadical (P : Submodule F (Fin 3 → F)) :
    radical P = SpecialLinearGroup.FrameGeometry.pointRadical P := by
  ext a
  change (_ ∧ _) ↔ (_ ∧ _)
  exact and_comm

/-- The radicals at a direct frame of three lines generate the actual SL₃(F). -/
theorem radical_sup_sup_eq_top (P Q R : Submodule F (Fin 3 → F))
    (hP : Module.finrank F P = 1) (hQ : Module.finrank F Q = 1)
    (hR : Module.finrank F R = 1) (hPQ : Disjoint P Q)
    (hPQR : Disjoint (P ⊔ Q) R) (hspan : (P ⊔ Q) ⊔ R = ⊤) :
    (radical P ⊔ radical Q) ⊔ radical R = ⊤ := by
  let b : SpecialLinearGroup.FrameGeometry.Frame F :=
    { point := ![P, Q, R]
      dimension := by
        intro i
        fin_cases i
        · exact hP
        · exact hQ
        · exact hR
      disjoint := hPQ
      third_disjoint := hPQR
      span := hspan }
  simpa [b, ← radical_eq_frame_pointRadical] using b.iSup_pointRadical_eq_top

end Matrix.PSL3.PointRadicalGeneration
