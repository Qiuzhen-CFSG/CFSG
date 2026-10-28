module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.A312Specialization.Sieve
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.A312Specialization.Binary
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.A312Specialization.RankOne

/-!
# The A.3.12 alternatives for the actual PSL₃(4) cover

For B ≤ K in the finite SQTK group H, assume B and K are quasisimple,
K is normal in H, m₃(B)=2, and Z(B)=O₂(B) has order four. Retain the
actual marking of B/O₂(B) as PSL₃(4). The supplied A.3.12 embedding of
the images in H/O₂(H) then gives equality or the actual M₂₃ model for
K's image.

The image of B remains a quasisimple central cover with center of order
at most four and the same marked quotient. The full twenty-two-case sieve
uses this bound for normal extension kernels, the order formulas for the
small and rank-one models, and Sylow-center orders to distinguish PSL₃(4)
from PSL₄(2). Every separation premise of the sieve is discharged here.
Normality of B is neither assumed nor inferred. Equality of the original
subgroups and the M₂₃ multiplier exclusion belong to the later rigidity
argument.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
A.3.12 (printed pp.47--48), and the proof of 15.3.38 on printed p.1136.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry.A312Specialization
open Chapter1.Section02 Chapter1.Section02.LocalModels
universe u
variable {H : Type u} [Group H] [Finite H]

/-- Specialize all A.3.12 alternatives at the actual PSL₃(4) central cover.
The source's SQTK, normality and rank hypotheses are retained; once the
embedding is supplied, the sieve itself needs only the indicated cover data. -/
theorem a312_eq_or_mathieu23 {κ : GroupClass.{u}} (_hH : IsSQTK κ H)
    (B K : Subgroup H) [IsQuasisimple B] [IsQuasisimple K]
    (hBK : B ≤ K) (_hK : K.Normal) (_hrank : primeRank 3 B = 2)
    (hZ : center B = pCore 2 B) (hc : Nat.card (center B) = 4)
    (c : ProjectiveMarking B 4)
    (hemb : A312Embedding (B.map (QuotientGroup.mk' (pCore 2 H)))
      (K.map (QuotientGroup.mk' (pCore 2 H)))) :
    B.map (QuotientGroup.mk' (pCore 2 H)) = K.map (QuotientGroup.mk' (pCore 2 H)) ∨
      Nonempty ((K.map (QuotientGroup.mk' (pCore 2 H))) ≃* Sporadic.Mathieu.M23) := by
  apply specialize_of_model_separations (fun _ _ h => no_binary_four h) ?_
    B K hBK c hZ hc hemb
  intro X _ _ hd hu
  exact ⟨fun n _ => no_psl_two_of_card hd hu (2 ^ n),
    fun p _ _ _ h => h.elim (no_psl_two_of_card hd hu p) (no_sl_two_of_card hd hu p)⟩

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry.A312Specialization
