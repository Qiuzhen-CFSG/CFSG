module

public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.ResidualNineFrattini
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# The original E.2.17 conjugate-span consumer

Take B = V ∩ O₂(H) and the literal global span U = <B^H>. Its normality follows
from the definition of conjugate span. Once the source four-dimensional branch
identifies U as a quaternion central product, the residual-nine obstruction
uses the original V and its normality in the marked Sylow subgroup. Inversion
is required only modulo the Frattini subgroup of O²(H)/(O²(H) ∩ O₂(H)).

The remaining source inputs are the quaternion structure of this global span
and the source inversion statement. The conclusion excludes order nine for
the actual residual image; identifying its order in the exceptional source
branch remains with the solvable-source assembly.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, E.2.17,
printed pp.229--230, with U = <B^H>.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.DihedralCubic
variable {H : Type*} [Group H] [Finite H]

/-- Exclude the order-nine image on the source global span without assuming
that the earlier local pair core is normalized by the Sylow subgroup. -/
theorem source_conjugate_span_residual_image_ne_nine
    (S : Sylow 2 H) (V : Subgroup H) [IsElementaryAbelian 2 V]
    (d : QuaternionCentralProductData (conjugateSpanBy (V⊓pCore 2 H) ⊤))
    (hVS : V≤(S : Subgroup H)) (hn : (V.subgroupOf (S : Subgroup H)).Normal)
    (v : H) (hv : v∈V)
    (hi : ∀ k : pResidual 2 H, (MulAut.conjNormal v : MulAut (pResidual 2 H)) k*k ∈
      (frattini (pResidual 2 H⧸(pCore 2 H).subgroupOf (pResidual 2 H))).comap
        (QuotientGroup.mk' ((pCore 2 H).subgroupOf (pResidual 2 H)))) :
    letI : (conjugateSpanBy (V⊓pCore 2 H) ⊤).Normal :=
      normalizer_eq_top_iff.mp (top_unique (le_normalizer_conjugateSpanBy _ ⊤))
    Nat.card ((pResidual 2 H).map (d.quotientWreathAction.comp MulAut.conjNormal))≠9 := by
  let : (conjugateSpanBy (V⊓pCore 2 H) ⊤).Normal :=
    normalizer_eq_top_iff.mp (top_unique (le_normalizer_conjugateSpanBy _ ⊤))
  exact source_residual_image_ne_nine_of_frattini_inversion S _ V d hVS hn v hv hi

end CFSG.Quasithin.ChapterE.DihedralCubic
