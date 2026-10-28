module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Centralizer.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.BSWSetup
public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.SmallBranch

/-!
# Recognizing the actual two-residual as A₅

The marked involution in J has a four-group centralizer and every involution
of J is conjugate to it, once the source residual facts are supplied. The
proved Brauer–Suzuki–Wall construction then gives A₄ or A₅. The A₄ case
would force J = X by cardinality, contrary to the proved J ⊈ L.

This result discharges recognition from `ResidualFacts`; producing those
facts from the original source hypotheses is still a separate obligation.
It assumes neither simplicity of G nor an ambient order or index.

Source: Aschbacher, “A 2-local characterization of M12”, Proposition 3.3,
printed p.38. The checked BSW route replaces its Exercise 16.6 citation.
-/

namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index
open Subgroup GorensteinWalter
variable {G : Type*} [Group G] [Finite G] {z : G} {L : Subgroup G}

/-- The four-group centralizer and single involution class recognize J.
The A₄ alternative is excluded using X ≤ J, |X|=12 and J ⊈ L. -/
public theorem residual_equiv_alternating_five (d : InvolutionData z L)
    (hz : orderOf z = 2) (hCL : Centralizer z ≤ L) (hK : ¬ d.K ≤ L)
    (r : ResidualFacts d) : Nonempty (d.J ≃* alternatingGroup (Fin 5)) := by
  let iJ : d.J := ⟨(d.i : G), r.i_mem⟩
  have hi : orderOf iJ = 2 :=
    (Subgroup.orderOf_coe iJ).symm.trans
      ((Subgroup.orderOf_coe d.i).trans d.i_order)
  let localData : DihedralInvolutionCentralizerHypotheses d.J 2 :=
    { two_le := le_rfl
      z := iJ
      involution := ⟨fun he => by simp [he] at hi, hi ▸ pow_orderOf_eq_one iJ⟩
      involutions_conjugate := fun u hu =>
        isConj_iff.mp (r.involutions_conjugate u (orderOf_eq_prime hu.2 hu.1))
      centralizer_equiv := r.centralizer_equiv }
  obtain ⟨b, _, _, hb⟩ := localData.exists_brauerSuzukiWallHypotheses
  have hb2 : Nat.card b.K = 2 := by simpa using hb
  rcases alternating_four_or_five_of_bsw_card_two b hb2 with h4 | h5
  · obtain ⟨e4⟩ := h4
    have hXcard := r.x_card
    have hJcard : Nat.card d.J = 12 :=
      (Nat.card_congr e4.toEquiv).trans (alternatingGroup.card_of_card_eq_four (by simp))
    have hXJ : d.X = d.J := eq_of_le_of_card_ge d.X_le_J (by omega)
    exact (d.J_not_le hz hCL hK (hXJ ▸ d.X_le_L)).elim
  · exact h5

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index
