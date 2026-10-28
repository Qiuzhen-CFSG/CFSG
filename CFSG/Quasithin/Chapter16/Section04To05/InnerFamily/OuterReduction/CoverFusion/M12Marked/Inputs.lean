module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.CoverFusion.Reduction
public import Theory.Mathieu.M12.SmallParabolicPair.SylowGeometry

/-!
# The remaining finite calculation in the M₁₂ central involution centralizer

The marked centralizer `firstParabolic = C_M₁₂(z)` has order 192.
The needed calculation concerns only its automorphisms: one whose square
is the identity and whose fixed subgroup has order eight moves an element
by the marked central involution z. This definition is a proof obligation,
not an assertion that the calculation holds.

The M₁₂ marked-fusion reduction obtains exactly these inputs by restricting
the original outer involution after conjugating a residual involution to z.
This avoids requiring a classification of all automorphisms of M₁₂.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
16.4.9(2), printed pp.1190–1191; the earlier table is 16.1.5(4), p.1171.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.OuterReduction.CoverFusion
open Sporadic.Mathieu Sporadic.Mathieu.M12SmallPair

/-- The exact local finite calculation still required by the assembly. -/
def M12CentralizerDisplacement : Prop :=
  ∀ a : MulAut firstParabolic, a ^ 2 = 1 → Nat.card a.fixedSubgroup = 8 →
    ∃ l : firstParabolic, (a l : M12) * (l : M12)⁻¹ = z

end CFSG.Quasithin.Chapter16.Intersections.OuterReduction.CoverFusion
