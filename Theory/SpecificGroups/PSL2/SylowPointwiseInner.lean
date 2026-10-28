module

public import Theory.GroupAction.SylowPointwiseInner
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.Rigidity.BaseAutomorphisms.Linear

/-!
# Automorphisms fixing a binary PSL₂ Sylow subgroup

The established root-coordinate calculation identifies an automorphism fixing
the standard unipotent subgroup with conjugation by an element of that subgroup.
The canonical SL₂ quotient carries the upper unipotent Sylow subgroup onto
this subgroup; Sylow conjugacy then gives the assertion for every Sylow subgroup.
No restriction on the order of the automorphism is needed.

Source: GLS III, Theorem 2.6.5(e), as used in Aschbacher–Smith 16.1.6,
printed p.1172. This extends the existing PSL₂(4) specialization without
changing that public interface.
-/

public section

namespace Theory.PSL2
open BenderSuzuki.Converse BenderSuzuki.ZD.Linear BenderSuzuki.MatrixGroups

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

/-- Every automorphism fixing a Sylow two-subgroup pointwise is conjugation
by an element of that same Sylow subgroup, over any finite binary field. -/
theorem aut_fixing_sylow_inner (Q : Sylow 2 (PSL2MatrixGroup K))
    (a : MulAut (PSL2MatrixGroup K)) (ha : ∀ x ∈ Q, a x = x) :
    ∃ x ∈ Q, a = MulAut.conj x := by
  let U := Matrix.SpecialLinearGroup.upperUnipotentSylow K 2
  let P := U.mapSurjective (f := pi K) pi_surjective
  have hP : (P : Subgroup (PSL2MatrixGroup K)) = PUnip K := by
    rw [Sylow.coe_mapSurjective]
    change (Matrix.SpecialLinearGroup.upperUnipotent K).map (pi K) =
      (Unip K).map (pi K)
    congr 1
    ext g
    rw [Matrix.SpecialLinearGroup.mem_upperUnipotent, mem_Unip_iff]
    simp only [upper_transvection_eq_uni, eq_comm]
  apply MulAut.fixing_inner_sylow P Q _ a ha
  intro b hb
  change ∀ x ∈ (P : Subgroup _), b x = x at hb
  change ∃ x ∈ (P : Subgroup _), b = MulAut.conj x
  rw [hP] at hb ⊢
  exact BenderSuzuki.ZD.BaseAutomorphisms.psl2_aut_fixing_unipotent_inner b hb

end Theory.PSL2
