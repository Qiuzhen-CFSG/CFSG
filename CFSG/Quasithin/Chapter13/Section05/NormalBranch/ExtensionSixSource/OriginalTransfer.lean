module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource.Transfer
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource.OriginalWeakClosure

/-!
# Original-source transfer and cyclic center in 13.5.16

The complete source theorem 13.5.15 and the exclusion of the recognized
U₄(3) branch supply all hypotheses of Thompson transfer. Every ambient
involution belongs to the original point class, and the actual core center
is cyclic of order four. A generator squares to the source point, and its
conjugates outside H are disjoint. These are the inputs to the abelian
plane span in the last paragraph of 13.5.16.

Source: Aschbacher–Smith, Proposition 13.5.16, printed pp.921–922.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource
open Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)
include d h e hseed hn hU

/-- All ambient involutions lie in the original point class. -/
theorem original_ambient_involutions_fused
    (z : G) (hz : z ∈ D.V₁) (hz1 : z ≠ 1)
    (x : G) (hx : orderOf x = 2) : IsConj z x := by
  obtain ⟨_,_,b⟩ := SourceConclusions.source13_5_15 d h e hseed hn hU
  exact ambient_involutions_fused d h e hseed hn hU b
    (original_extension_model d h e hseed hn hU) z hz hz1 x hx

/-- The actual core center is cyclic, with its original order retained. -/
theorem original_core_center_cyclic : IsCyclic (center D.QH) ∧ Nat.card (center D.QH) = 4 := by
  obtain ⟨_,_,b⟩ := SourceConclusions.source13_5_15 d h e hseed hn hU
  have hS := original_extension_model d h e hseed hn hU
  exact ⟨core_center_cyclic d h e hseed hn hU b hS,
    extension_center_card d h e hseed hn hU b hS⟩

/-- A center generator has the original point involution as its square. -/
theorem original_exists_center_generator
    (z : G) (hz : z ∈ D.V₁) (hz1 : z ≠ 1) :
    ∃ j : G, orderOf j = 4 ∧ j ^ 2 = z ∧
      (center D.QH).map D.QH.subtype = zpowers j := by
  obtain ⟨_,_,b⟩ := SourceConclusions.source13_5_15 d h e hseed hn hU
  exact exists_center_generator d h e hseed hn hU b
    (original_extension_model d h e hseed hn hU) z hz hz1

/-- Distinct source point centralizers have disjoint core centers. -/
theorem original_center_conjugate_disjoint
    (z : G) (hz : z ∈ D.V₁) (hz1 : z ≠ 1)
    (y : G) (hy : y ∉ D.H) :
    Disjoint ((center D.QH).map D.QH.subtype)
      (((center D.QH).map D.QH.subtype).conjBy y) := by
  obtain ⟨_,_,b⟩ := SourceConclusions.source13_5_15 d h e hseed hn hU
  exact center_conjugate_disjoint d h e hseed hn hU b
    (original_extension_model d h e hseed hn hU) z hz hz1 y hy

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource
