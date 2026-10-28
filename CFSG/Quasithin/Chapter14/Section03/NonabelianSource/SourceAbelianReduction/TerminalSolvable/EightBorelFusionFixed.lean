module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelFusion
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.FusionWitness

/-!
# The fixed-core fusion reduction on the original eight-field component

The original component and its marked inclusion amalgam inherit the explicit
long-root conclusion of the Sylow fixed-space calculation. A pair of core
elements centralizing the fused involution and having commutator z suffices:
Sylow conjugacy supplies the previously separate mutual-core incidence.
The root marking is that of the given whole-amalgam equivalence, and the
conjugating element belongs to the original Mc, including its cubic extension.

The local pair is constructed for the specified short-root representative.
Exclusion of the short-root orbit under Mc,
matching sixth-power relation, ambient recognition and final Borel exclusion
remain with qt-e-14315-eight-borel-exclusion. The independent marked realization
is still an explicit earlier input.
Source: Aschbacher--Smith F.4.35, p.292; 14.2.18--19, p.987; 14.3.15, p.994.
-/

open scoped commutatorElement
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    {F : InvariantFlag T (rankTwoSeed T M) 2} {g : G} {K : Subgroup G}
include hG hempty hM hu hmany hcard e

/-- The actual mutual-core case has an Mc-conjugate with genuine long-root
image, not merely a vector fixed modulo the center. -/
theorem source_eight_marked_mutual_core_long_root
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G)))
    (a : G) (ha : a∉Mc) {z : G} (hz : z∈centralInvolutions T) (hz1 : z≠1)
    (hzR : z∈(K.pCoreIn 2).map (MulAut.conj a).toMonoidHom)
    (htQ : MulAut.conj a z∈K.pCoreIn 2) :
    ∃ b : Mc, ∃ q : (K ⊔ (T:Subgroup G)).pCoreIn 2,
      (q:G)=MulAut.conj (b:G) (MulAut.conj a z) ∧
      _root_.Triality.Standard.EvenInvolutionGeometry.IsLongRootInvolution
        1 Nat.zero_lt_one (EightLargeParabolic.firstCoreEquiv r q).val := by
  have hjoin := source_eight_marked_join_eq hG T hempty hM hu hmany hcard e hK h8 r
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  apply EightLargeParabolic.source_mutual_core_long_root
    hG hempty hM hu hmany hcard e hH r a ha hz hz1
  · simpa only [hjoin] using hzR
  · simpa only [hjoin] using htQ

/-- The literal core pair discharges mutual incidence on ComponentLift and
EightImageRow; its long-root conclusion retains the original endpoint marking. -/
theorem source_eight_marked_pair_long_root
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G)))
    (a : G) (ha : a∉Mc) {z : G} (hz : z∈centralInvolutions T) (hz1 : z≠1)
    (htQ : MulAut.conj a z∈K.pCoreIn 2)
    {x y : G} (hx : x∈K.pCoreIn 2) (hy : y∈K.pCoreIn 2)
    (hxt : Commute x (MulAut.conj a z)) (hyt : Commute y (MulAut.conj a z))
    (hxy : ⁅x,y⁆=z) :
    ∃ b : Mc, ∃ q : (K ⊔ (T:Subgroup G)).pCoreIn 2,
      (q:G)=MulAut.conj (b:G) (MulAut.conj a z) ∧
      _root_.Triality.Standard.EvenInvolutionGeometry.IsLongRootInvolution
        1 Nat.zero_lt_one (EightLargeParabolic.firstCoreEquiv r q).val := by
  have hjoin := source_eight_marked_join_eq hG T hempty hM hu hmany hcard e hK h8 r
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  apply EightLargeParabolic.source_pair_long_root
    hG hempty hM hu hmany hcard e hH r a ha hz hz1
    (by simpa only [hjoin] using htQ)
    (by simpa only [hjoin] using hx) (by simpa only [hjoin] using hy) hxt hyt hxy

/-- The concrete model short root supplies the local pair on the extracted
component. Its ambient fusion would force the same Mc-orbit to contain an
element marked as a long root. -/
theorem source_eight_marked_higher_short_fusion
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G)))
    (a : G) (ha : a∉Mc) {z : G} (hz : z∈centralInvolutions T) (hz1 : z≠1)
    (htQ : MulAut.conj a z∈K.pCoreIn 2)
    (d : _root_.Triality.Standard.ExtensionField
      (_root_.Triality.Standard.binaryParameters 1 Nat.zero_lt_one))
    (hshort : (r.left ⟨MulAut.conj a z,(show K≤K ⊔ (T:Subgroup G) from le_sup_left) (pCoreIn_le 2 K htQ)⟩).val=
      _root_.Triality.Standard.RadicalCoordinates.LeviCommutators.short
        (_root_.Triality.Standard.binaryParameters 1 Nat.zero_lt_one) rfl 2 d) :
    ∃ b : Mc, ∃ q : (K ⊔ (T:Subgroup G)).pCoreIn 2,
      (q:G)=MulAut.conj (b:G) (MulAut.conj a z) ∧
      _root_.Triality.Standard.EvenInvolutionGeometry.IsLongRootInvolution
        1 Nat.zero_lt_one (EightLargeParabolic.firstCoreEquiv r q).val := by
  have hjoin := source_eight_marked_join_eq hG T hempty hM hu hmany hcard e hK h8 r
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  have htQ' : MulAut.conj a z∈(K ⊔ (T:Subgroup G)).pCoreIn 2 := by
    simpa only [hjoin] using htQ
  apply EightLargeParabolic.source_higher_short_fusion_reduction
    hG hempty hM hu hmany hcard e hH r a ha hz hz1 htQ' d
  rw [EightLargeParabolic.firstCoreEquiv_val]
  exact hshort

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
