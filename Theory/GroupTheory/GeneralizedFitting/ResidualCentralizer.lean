module
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer
public import Theory.GroupTheory.PResidual.NormalComplement
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
/-!
# Self-centralization of the residual in a core-free group

If O_p(G)=1, its Fitting subgroup has order prime to p and every component
is perfect. Both therefore lie in O^p(G). Generalized Fitting
self-centralization implies C_G(O^p(G))≤O^p(G).
The binary application supplies the normal layer in the moved-module
faithfulness step of Aschbacher–Smith B.6.10/E.2.3.
-/
public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
theorem generalizedFitting_le_pResidual_of_pCore_eq_bot (hcore : pCore p G = ⊥) :
    generalizedFitting G ≤ pResidual p G := by
  apply sup_le
  · exact (fitting_le_pPrimeCore_of_pCore_eq_bot p hcore).trans pPrimeCore_le_pResidual
  · apply sSup_le
    intro L hL
    let : IsQuasisimple L := hL.2
    apply le_sInf
    rintro N ⟨hN,hq⟩
    let : N.Normal := hN
    let : Group.IsNilpotent (G ⧸ N) := hq.isNilpotent
    exact le_of_isPerfect_of_solvable_quotient L N

theorem centralizer_pResidual_le_of_pCore_eq_bot (hcore : pCore p G = ⊥) :
    centralizer (pResidual p G : Set G) ≤ pResidual p G := by
  have hF := generalizedFitting_le_pResidual_of_pCore_eq_bot hcore
  exact (centralizer_le hF).trans ((centralizer_generalizedFitting_le G).trans hF)

end Theory.GroupTheory
