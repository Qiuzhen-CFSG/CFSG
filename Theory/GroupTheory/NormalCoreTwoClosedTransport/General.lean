module
public import Theory.GroupTheory.NormalCoreTwoClosedTransport

/-!
# Two-closedness through kernels central modulo a two-group

Quotient out the marked normal two-subgroup. The remaining kernel is
central, so normality of the Sylow two-subgroup lifts; the final two-group
kernel lifts it again. The target need only be two-closed, and may have
an odd quotient. This is the full transport needed in E.2.9, printed p.222.
-/

public section
namespace Subgroup
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
omit [Finite H] in
theorem odd_pCore_index_of_central_kernel_mod_two_of_odd_index (f : G →* H)
    (hf : Function.Surjective f) (hi : Odd (pCore 2 H).index)
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hNker : N ≤ f.ker) (hcomm : ⁅f.ker,⊤⁆ ≤ N) :
    Odd (pCore 2 G).index := by
  let q := QuotientGroup.mk' N
  let b := QuotientGroup.lift N f hNker
  have hb : Function.Surjective b := by
    intro y
    obtain ⟨x,rfl⟩ := hf y
    exact ⟨q x,rfl⟩
  have hk : b.ker ≤ center (G ⧸ N) := by
    rw [QuotientGroup.ker_lift,← centralizer_univ,← coe_top]
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_top_of_surjective q (QuotientGroup.mk'_surjective N),← map_commutator]
    apply (map_eq_bot_iff _).mpr
    rw [QuotientGroup.ker_mk']
    exact hcomm
  have hbidx : Odd (pCore 2 (G ⧸ N)).index :=
    OddHall.odd_pCore_index_of_surjective_central_kernel b hb hk hi
  apply odd_pCore_index_of_surjective_two_kernel q (QuotientGroup.mk'_surjective N) _ hbidx
  rw [show q.ker = N from QuotientGroup.ker_mk' N]
  exact hN
end Subgroup
