module
public import Theory.GroupTheory.Recognition.Brauer.ActionKernel

/-!
# Odd order of Brauer's collineation kernel

The kernel of the actual point-and-line representation has odd order. This
is Brauer, *On finite Desarguesian planes I*, (4C), article page 123, giving
the odd normal subgroup needed in the final image description (4D).

If the kernel were even, Cauchy's theorem would give an involution in it.
The single involution class and normality then place the distinguished `j`
in the kernel. The kernel formula (4B) says that `j` centralizes every
involution, including all elements of the base line `j Mstar`. Cancellation
forces `Mstar` into `C(j)`, contrary to their disjointness and the nontriviality
of `Mstar`. This is the algebraic form of the source's moved-block
contradiction; all actions and subgroup instances are the original ones.
-/

open scoped Pointwise

namespace Theory.GroupTheory.BrauerPlaneSeed

private theorem j_not_mem_involution_centralizer
    {G : Type*} [Group G] [Finite G] (S : BrauerPlaneSeed G) :
    S.j ∉ Subgroup.centralizer {x : G | orderOf x = 2} := by
  intro hj
  apply S.Mstar_ne_bot
  apply le_antisymm _ bot_le
  intro m hm
  have hl : S.j * m ∈ (S.baseLine : Set G) :=
    Set.mem_smul_set.mpr ⟨m, hm, rfl⟩
  have hord : orderOf (S.j * m) = 2 :=
    S.orderOf_mem_line ⟨S.baseLine, MulAction.mem_orbit_self _⟩ hl
  have hc : m ∈ Subgroup.centralizer {S.j} := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have h := Subgroup.mem_centralizer_iff.mp hj (S.j * m) hord
    exact mul_left_cancel (by simpa only [mul_assoc] using h)
  have hmem : m ∈ S.Mstar ⊓ Subgroup.centralizer {S.j} := ⟨hm, hc⟩
  simpa only [S.disjoint_Mstar_centralizer.eq_bot] using hmem

public theorem odd_card_collineationRepresentation_ker
    {G : Type*} [Group G] [Finite G] (S : BrauerPlaneSeed G) :
    Odd (Nat.card S.collineationRepresentation.ker) := by
  rw [← Nat.not_even_iff_odd]
  intro heven
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := S.collineationRepresentation.ker) 2
    (even_iff_two_dvd.mp heven)
  have hxG : orderOf (x : G) = 2 := by
    simpa only [Subgroup.orderOf_coe] using hx
  obtain ⟨g, hg⟩ := isConj_iff.mp (S.involutions_isConj hxG S.j_order)
  have hjH : S.j ∈ S.collineationRepresentation.ker := by
    rw [← hg]
    exact (inferInstance : S.collineationRepresentation.ker.Normal).conj_mem _ x.property _
  rw [S.ker_collineationRepresentation] at hjH
  exact j_not_mem_involution_centralizer S hjH

end Theory.GroupTheory.BrauerPlaneSeed
