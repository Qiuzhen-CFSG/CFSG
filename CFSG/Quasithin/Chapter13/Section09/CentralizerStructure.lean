module

public import CFSG.Quasithin.Chapter13.Section09.CentralizerStructure.CentralClosure
public import CFSG.Quasithin.Chapter13.Section09.CentralizerStructure.Overgroups
public import CFSG.Quasithin.Chapter13.Section09.CentralizerStructure.MarkedCore

/-!
# The centralizer steps in 13.9.7–8

This interface proves 13.9.7 from the marked earlier geometry and the
genuine simple QTKE hypothesis. It also exports the fully constructed
G.2.2 application on C_G(z)/⟨z⟩, the weak-closure deductions for A and B,
and the solvability consequence of the actual centralizer quotient by Q.

The remaining parts of 13.9.8 are the normality of Q, the orthogonal
quotient recognition, and the three-overgroup identification of BQ with
O₂(C_G(z)). They are not asserted by the conditional deductions here.
Final assembly of those branches belongs to this module.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed pp.971–972 (PDF pp.988–989).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section09
open Subgroup CentralizerStructure
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Source 13.9.7. The earlier marked geometry is explicit for independent
work; the source owner supplies it from 13.9.2 and the original wreath model.
The class parameter can in particular be the full known-simple catalogue. -/
theorem source13_9_7 {K : GroupClass.{u}} (hG : IsSimpleQTKE K G)
    (d : Configuration G) (m : PairData d) :
    centralizer ({m.t, m.z} : Set G) = thompson d := by
  have he : centralizer ({m.t, m.z} : Set G) = m.D := by
    ext x
    simp only [PairData.D, PairData.C, mem_inf, mem_centralizer_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    exact and_comm
  exact he.trans (m.source13_9_7 (hG.evenCharacteristic d.T))

end CFSG.Quasithin.Chapter13.Section09
