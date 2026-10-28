module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Basic
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.SourceCount

/-!
# The J₂ local census from the source hypotheses

This is the source-local entry point for the complete `LocalCensus` of a
recognition seed. The §46 producers identify the involutions of C_G(z)
conjugate to z with the involutions of its actual core and prove conjugacy
inside C_G(z) of all outside involutions. The §47 producer identifies the
literal source pairs with 120 outside choices and eight compatible core
choices over each, giving a(z) = 960.

The extension calculations use the actual core and quotient isomorphisms
and the induced action on the five singular points. They supply the local
facts needed from the w = 2 argument without assuming recognition of G.
The application below substitutes the proved census into Thompson's order
formula, leaving the second-centralizer calculation to its source owner.

Source: Aschbacher, *Sporadic Groups* (1994), 46.1(2), 46.8, 46.11,
46.14(5)(b), and the first calculation of 47.1, printed pp.251–259.
-/

public section

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal

variable {G : Type*} [Group G] [Finite G]

/-- The full earlier-source census, with both fusion assertions and the count
960 proved from the recognition seed. In particular this applies to every
finite simple ambient group; simplicity is not needed for these local facts. -/
theorem localCensus (D : Seed G) : InvolutionGeometry.LocalCensus D where
  core_fusion := fun _ huH hu => InvolutionGeometry.core_fusion D huH hu
  outside_fusion := InvolutionGeometry.outside_involutions_isConj D
  count_at_z := fun _ ht => InvolutionGeometry.sourceCount_at_z_eq_960 ht

/-- The proved first count in the literal Thompson formula used in 47.1.
Only the second centralizer and the count at the other involution remain. -/
theorem source_order_formula_at_z {D : Seed G} {t : G}
    (ht : InvolutionGeometry.OtherInvolution D t) :
    Nat.card G = 960 * Nat.card (involutionCentralizer t) +
      InvolutionGeometry.sourceCount D.z t t * 1920 := by
  rw [InvolutionGeometry.source_order_formula ht, (localCensus D).count_at_z t ht]

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal
