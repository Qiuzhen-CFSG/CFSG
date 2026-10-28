module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.NonsingularC
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.PairImages
public import Theory.Mathieu.M24.ChapterHStabilizers.Involutions

/-!
# The fixed-point-free pair and its fifteen invariant octads

The native fixed-point-free involution is the product of the first vertical
Figure 2(c) generator and the marked pair permutation. Its invariant Witt
octads are exactly the fifteen unions of two tetrads in its associated sextet.
Their incidence profiles identify the tetrads: two distinct transpositions
with the same profile have kernel-label sum 818. In particular stars 0 and 11
have identical profiles. The next module uses these certificates to control
the full quotient centralizer and the inner-half characters of its involutions.

Source: Kleidman--Wilson (1988), opening of Section 2.3, printed p.492.
The block catalogue, star relabelling and kernel labels are the certified
native Mathieu/ATLAS coordinates of the imported model.
-/

set_option backward.isDefEq.respectTransparency true
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu
open scoped Pointwise
namespace Janko4.LocalStructure.ElementaryNormalizerCover.ABB
open Cardinality QuotientCount.Image KernelCount
open InvolutionCentralizers.Second ElementaryEightGeometry
open LargeCenterRadicals.OuterHalf M22Images.KernelAction
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel basis

def freePair : StarGroup := NonsingularC.vertical 0 * pairPermutation

theorem freePair_square : freePair ^ 2 = 1 := by
  apply Subtype.ext
  decide +kernel

theorem freePair_fixed_free : ∀ i : Fin 24, freePair.val i ≠ i := by decide +kernel

def stableIndex : Fin 15 → Fin 759 := ![59,124,162,189,209,294,332,360,380,462,493,513,569,589,641]
def incident (i : Fin 759) (x : Fin 24) : Prop :=
  StarOrderCertificate.relabel x ∈ m24BlockAt i
instance (i : Fin 759) (x : Fin 24) : Decidable (incident i x) := inferInstanceAs
  (Decidable (StarOrderCertificate.relabel x ∈ m24BlockAt i))
def Stable (i : Fin 759) : Prop :=
  ∀ x : Fin 24, incident i (freePair.val x) ↔ incident i x
instance (i : Fin 759) : Decidable (Stable i) := inferInstanceAs
  (Decidable (∀ x : Fin 24, incident i (freePair.val x) ↔ incident i x))
theorem stable_exhaustive : ∀ i : Fin 759, Stable i → ∃ j, stableIndex j = i := by
  decide +kernel
theorem stable_indices : ∀ j, Stable (stableIndex j) := by decide +kernel
theorem stable_twins : ∀ j, incident (stableIndex j) 0 ↔ incident (stableIndex j) 11 := by
  decide +kernel
theorem twin_label : ∀ x y : Fin 24, x ≠ y → freePair.val x ≠ y →
    (∀ j, incident (stableIndex j) x ↔ incident (stableIndex j) y) →
    Nat.xor (pairLabel x (freePair.val x)) (pairLabel y (freePair.val y)) = 818 := by
  decide +kernel
end Janko4.LocalStructure.ElementaryNormalizerCover.ABB
