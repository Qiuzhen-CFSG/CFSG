module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource.WeakClosure
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceConclusions

/-!
# Original-source weak closure for 13.5.16

The full source theorem 13.5.15 supplies the pair and all local conclusions
internally. The counterexample excludes the recognized U₄(3) branch and
therefore supplies its S₆ alternative. The actual core is weakly closed in H
and the original Sylow subgroup. Burnside fusion fixes the original point
inside the actual core center. No weak-closure, action, cardinality or
completed 13.5.15 conclusion remains an extra input.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition 13.5.16, printed p.921.
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

/-- The original counterexample excludes the recognized U₄(3) branch,
so its literal local quotient is S₆. -/
theorem original_extension_model :
    Nonempty ((M ⧸ pCore 2 M) ≃* Equiv.Perm (Fin 6)) := by
  obtain ⟨_,_,b⟩ := SourceConclusions.source13_5_15 d h e hseed hn hU
  rcases (b.nine rfl).2 with heq | hext
  · exact (d.counterexample.no_unitary_four
      (TypeU4.isPSU_of_natural_normal_branch d h b heq.1)).elim
  · exact hext.1

/-- The literal original core has no distinct conjugate contained in H. -/
theorem original_core_weakly_closed_in_normalizer (x : G)
    (hx : D.QH.conjBy x ≤ D.H) : D.QH.conjBy x = D.QH := by
  obtain ⟨_,_,b⟩ := SourceConclusions.source13_5_15 d h e hseed hn hU
  exact core_weakly_closed_in_normalizer d h e hseed hn hU b
    (original_extension_model d h e hseed hn hU) x hx

/-- The original point is fixed under fusion inside the original core center. -/
theorem original_point_fixed_in_core_center {z y : G} (hz : z ∈ D.V₁)
    (hy : y ∈ (center D.QH).map D.QH.subtype) (hzy : IsConj z y) : y = z := by
  obtain ⟨_,_,b⟩ := SourceConclusions.source13_5_15 d h e hseed hn hU
  exact point_fixed_in_core_center d h e hseed hn hU b
    (original_extension_model d h e hseed hn hU) hz hy hzy

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource
