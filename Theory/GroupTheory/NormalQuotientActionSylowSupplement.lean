module
public import Theory.GroupTheory.NormalQuotientOuterAction
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup

/-!
# Sylow supplements for characteristic quotient actions

The preimage of the inner automorphisms of L/N is L times the original
quotient-action kernel. If Out(L/N) is a p-group, any Sylow p-subgroup
covers the remaining outer action. The three literal subgroups therefore
generate the whole acting group.

Source application: Aschbacher--Smith, Lemma 12.3.8, printed p.810,
with N=O₂(L) and its actual ambient conjugation action.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- A Sylow subgroup covers the outer part of the characteristic quotient action. -/
theorem normalQuotientAction_sup_sylow_ker (P : Sylow p G)
    (L : Subgroup G) [L.Normal] (N : Subgroup L) [N.Characteristic]
    (ho : IsPGroup p (MulAut.Outer (L ⧸ N))) :
    L ⊔ (P : Subgroup G) ⊔ (normalQuotientAction L N).ker = ⊤ := by
  let a := normalQuotientAction L N
  let f : G →* MulAut.Outer (L ⧸ N) :=
    (QuotientGroup.mk' (MulAut.innerSubgroup (L ⧸ N))).comp a
  have hf : IsPGroup p (G ⧸ f.ker) :=
    (ho.to_subgroup f.range).of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  have hk : f.ker = L ⊔ a.ker := by
    rw [show f.ker = (MulAut.innerSubgroup (L ⧸ N)).comap a from by
      rw [← MonoidHom.comap_ker,QuotientGroup.ker_mk']]
    exact normalQuotientAction_comap_inner L N
  have hgen := P.sup_eq_top_of_quotient_isPGroup f.ker hf
  rw [hk] at hgen
  simpa only [sup_assoc,sup_comm,sup_left_comm] using hgen

end Subgroup
