module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelCompletion
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.FusionIntersection

/-!
# Extraspecial intersections for the original eight-field component

Apply the source F.4.35 intersection and Sylow-factorization calculation to
ComponentLift and EightImageRow. The embedded O₂(K), its ambient conjugates,
the original Sylow and its central involution group are retained literally.
The marked realization remains the independent earlier input; source fusion,
ambient recognition and Borel exclusion remain with this task's final assembly.

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

/-- The source F.4.35 core-intersection bound on the literal extracted component. -/
theorem source_eight_marked_core_intersection
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G)))
    (a : G) (ha : a∉Mc) :
    let Q := K.pCoreIn 2
    let R := Q.map (MulAut.conj a).toMonoidHom
    IsElementaryAbelian 2 (Q ⊓ R : Subgroup G) ∧ Nat.card (Q ⊓ R : Subgroup G)≤32 := by
  have hjoin := source_eight_marked_join_eq hG T hempty hM hu hmany hcard e hK h8 r
  have hH : K ∈ Chapter3.HStar (T : Subgroup G) M := by
    simpa only [hjoin] using
      (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  have rK : EightLargeParabolic.MarkedTriality T M Mc K := hjoin ▸ r
  exact EightLargeParabolic.source_conjugate_core_intersection
    hG hempty hM hu hmany hcard e hH rK a ha

/-- The literal Sylow factorization and commutator conclusion after mutual-core
placement. This does not claim the remaining source fusion or recognition step. -/
theorem source_eight_marked_core_fusion_factorization
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G)))
    (a : G) (ha : a∉Mc) {z : G} (hz : z∈centralInvolutions T) (hz1 : z≠1)
    (hzR : z∈(K.pCoreIn 2).map (MulAut.conj a).toMonoidHom)
    (hcT : (K.pCoreIn 2).map (MulAut.conj a).toMonoidHom ⊓
      centralizer ({z}:Set G) ≤ (T : Subgroup G))
    (htQ : MulAut.conj a z∈K.pCoreIn 2) :
    let Q := K.pCoreIn 2
    let C := Q.map (MulAut.conj a).toMonoidHom ⊓ centralizer ({z}:Set G)
    Nat.card C=256 ∧ Nat.card (Q ⊓ C : Subgroup G)=32 ∧ Q ⊔ C=(T : Subgroup G) ∧
      ∀ x∈(T : Subgroup G), ⁅x,MulAut.conj a z⁆∈centralInvolutions T := by
  have hjoin := source_eight_marked_join_eq hG T hempty hM hu hmany hcard e hK h8 r
  have hH : K ∈ Chapter3.HStar (T : Subgroup G) M := by
    simpa only [hjoin] using
      (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  have rK : EightLargeParabolic.MarkedTriality T M Mc K := hjoin ▸ r
  obtain ⟨hc,hi,hgen⟩ := EightLargeParabolic.source_conjugate_core_sylow_factorization
    hG hempty hM hu hmany hcard e hH rK a ha hz hz1 hzR hcT
  exact ⟨hc,hi,hgen,EightLargeParabolic.source_conjugate_core_fixed_mod_center
    hG hempty hM hu hmany hcard e hH rK a ha hz hz1 hzR hcT htQ⟩

/-- Sylow positioning is discharged inside Mc on the actual component. The
remaining mutual-core incidence is the earlier part of the source fusion proof. -/
theorem source_eight_marked_mutual_core_fusion
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G)))
    (a : G) (ha : a∉Mc) {z : G} (hz : z∈centralInvolutions T) (hz1 : z≠1)
    (hzR : z∈(K.pCoreIn 2).map (MulAut.conj a).toMonoidHom)
    (htQ : MulAut.conj a z∈K.pCoreIn 2) :
    ∃ b : Mc, ∀ x∈(T : Subgroup G),
      ⁅x,MulAut.conj (b:G) (MulAut.conj a z)⁆∈centralInvolutions T := by
  have hjoin := source_eight_marked_join_eq hG T hempty hM hu hmany hcard e hK h8 r
  have hH : K ∈ Chapter3.HStar (T : Subgroup G) M := by
    simpa only [hjoin] using
      (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  have rK : EightLargeParabolic.MarkedTriality T M Mc K := hjoin ▸ r
  exact EightLargeParabolic.source_mutual_core_fusion_reduction
    hG hempty hM hu hmany hcard e hH rK a ha hz hz1 hzR htQ

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
