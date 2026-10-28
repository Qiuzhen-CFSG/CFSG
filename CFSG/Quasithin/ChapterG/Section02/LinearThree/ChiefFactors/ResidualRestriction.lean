module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.Sections
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.Terminal
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.Obstruction
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.IntersectionAssembly
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.CoreAssembly
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.PointChief
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.BinaryField

/-!
# Genuine local residual restriction for G.2.5

The literal star/model map identifies N_L(V₁) with the marked-line stabilizer
and L₁ with its two-residual image. Determinant-one alignment gives the
standard matrix parabolic. The core normalizes L₁, so all sections omitted
on intersection with L₁ have trivial local action.

Over F₂, the image is the affine A₄ subgroup and the terminal quotient is C₃.
The natural flags are 1|2, the dual flags 2|1, and the radical is the same
irreducible cubic plane. V and all upper natural layers survive intersection;
all lower annihilator planes survive, with only central scalar quotients
possibly omitted. Genuine quotient coordinates retain the ambient actions.

For |F|=2^n with n>1, the image is the full point parabolic. Its block quotient
is GL₂(F); the natural, dual and radical actions retain their scalar characters
and determinant twists. Both natural and dual layers survive intersection in
full. In particular V₁ itself is an actual noncentral two-chief subgroup of
L₁ of order 2^n, not a natural SL₂(2^n)-plane of order 2^(2n).
This supplies a precise source obstruction to discarding the scalar factors.
It does not construct an instance of all ambient source hypotheses or refute
the complete book theorem. The larger-field source statement still requires
resolution by the chief-factor assembly owner.

The earlier U≤T, I=LU, genuine marked layer identifications and star-kernel
comparison remain explicit where used. Their producers are the structure
and recognition developments. Both terminal quotients have no two-chief
factors. Numerical chief refinement and the final source count belong to
`ChiefFactors`; no count is asserted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), G.2.1 and
G.2.5(8), printed pp.332,335–336; binary consumer 12.8.8, printed pp.851–852.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction
variable {G : Type*} [Group G] [Finite G] {D : Setup G}
  {F : Type*} [Field F] [Finite F] {n : ℕ} {g h : G}

/-- The terminal chief-refinement premise is discharged for every source field and exponent. -/
theorem terminal_hasNoTwoChiefFactors (d : Hypothesis D F n g h) :
    NoncentralChiefRefinement.HasNoTwoChiefFactors (D.L₁ ⧸ pCore 2 D.L₁) := by
  by_cases hn : n = 1
  · subst n
    exact BinaryField.terminal_hasNoTwoChiefFactors (d := d)
  · have hp := d.exponent_pos
    exact ScalarConstituents.larger_terminal_hasNoTwoChiefFactors (d := d) (by omega)

/-- The entire original natural module lies in the local residual, including its point. -/
theorem natural_le_residual (d : Hypothesis D F n g h)
    (hUT : D.U ≤ D.T) (hILU : I D g h = D.L ⊔ D.U) : D.V ≤ D.L₁ := by
  by_cases hn : n = 1
  · subst n
    exact BinaryField.V_le_residual (d := d) hUT hILU
  · have hp := d.exponent_pos
    obtain ⟨a⟩ := exists_pointAlignment d
    exact IntersectionAssembly.Larger.V_le_residual a (by omega) hUT hILU
end CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction
