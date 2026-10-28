module

public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# Generalized Fitting subgroups with inner quotient automorphisms

Suppose F*(G) is perfect and every automorphism of its central quotient is
inner. Perfectness lifts innerness from that quotient to F*(G). Thus every
element of G lies in F*(G) C_G(F*(G)), which equals F*(G) by the generalized
Fitting centralizer theorem. No assertion about the center of F*(G) is needed.

This is the ambient-action reduction for the M₂₃ and M₂₄ branches in
Aschbacher–Smith, Chapter K, printed pp.451, 457–458.
-/

public section
namespace Theory.GroupTheory
open Subgroup

/-- A perfect generalized Fitting subgroup whose central quotient has only
inner automorphisms is the whole finite ambient group. -/
theorem generalizedFitting_eq_top_of_inner_centralQuotient
    {G S : Type*} [Group G] [Finite G] [Group S]
    [Group.IsPerfect (generalizedFitting G)]
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* S)
    (hi : Function.Surjective (MulAut.conj : S →* MulAut S)) :
    generalizedFitting G = ⊤ := by
  let L := generalizedFitting G
  apply top_unique
  intro g _
  obtain ⟨a, ha⟩ := hi (MulAut.centralQuotientAction e (MulAut.conjNormal g : MulAut L))
  obtain ⟨l, hl⟩ := (MulAut.centralQuotientAction_inner_iff e
    (MulAut.conjNormal g : MulAut L)).mp ⟨a, ha.symm⟩
  have hm : g ∈ (MulAut.innerSubgroup L).comap MulAut.conjNormal := ⟨l, hl.symm⟩
  rw [MulAut.conjNormal_comap_innerSubgroup] at hm
  exact (sup_le le_rfl (centralizer_generalizedFitting_le G)) hm

end Theory.GroupTheory
