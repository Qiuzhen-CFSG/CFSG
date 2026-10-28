module

public import Theory.Mathieu.M22.Properties.AutomorphismCoverage
public import Theory.Mathieu.M22.Properties.HexadExtension.Kernel
public import Theory.GroupAction.AutomorphismFixedSubgroup

/-!
# Outer M₂₂ automorphisms in the faithful design action

Surjectivity and faithfulness of the design action lift every abstract outer
involution to an odd involution on the 22 points. Its full fixed subgroup in
M₂₂ is exactly the inverse image of the permutation centralizer. Thus geometric
calculations in the design apply to the full abstract fixed subgroup.

These are the transport steps for Aschbacher–Smith 16.1.5(5), combined manuscript
of 1 March 2004, printed p.1171. The eight fixed points of the standard odd
representative are checked here; exhaustive coverage and the two centralizer
structures are separate model calculations.
-/

@[expose] public section

namespace Sporadic.Mathieu.M22OuterCentralizers

open scoped Pointwise

/-- The centralizer in M₂₂ of an actual design automorphism. -/
noncomputable def centralizer (s : m22DesignAut) : Subgroup M22 :=
  (m22DesignAutToAut s).fixedSubgroup

/-- The actual fixed points in the faithful degree-22 permutation action. -/
def fixedPoints (s : m22DesignAut) : Finset (Fin 22) :=
  Finset.univ.filter fun x => s.val x = x

@[simp] theorem mem_fixedPoints (s : m22DesignAut) (x : Fin 22) :
    x ∈ fixedPoints s ↔ s.val x = x := by
  simp [fixedPoints]

/-- Membership means commuting in the ambient permutation group. -/
theorem mem_centralizer_iff (s : m22DesignAut) (g : M22) :
    g ∈ centralizer s ↔
      (g : Equiv.Perm (Fin 22)) * (s : Equiv.Perm (Fin 22)) =
        (s : Equiv.Perm (Fin 22)) * (g : Equiv.Perm (Fin 22)) := by
  rw [centralizer, MulAut.mem_fixedSubgroup]
  rw [Subtype.ext_iff, m22DesignAutToAut_apply_perm,
    mul_inv_eq_iff_eq_mul, eq_comm]

/-- This is the full centralizer restricted to M₂₂, rather than a chosen subgroup. -/
theorem centralizer_eq_comap (s : m22DesignAut) :
    centralizer s =
      (Subgroup.centralizer ({(s : Equiv.Perm (Fin 22))} :
        Set (Equiv.Perm (Fin 22)))).comap M22.subtype := by
  ext g
  exact (mem_centralizer_iff s g).trans Subgroup.mem_centralizer_singleton_iff.symm

/-- The centralizer acts on the actual fixed-point set. -/
theorem centralizer_le_fixedPoints_stabilizer (s : m22DesignAut) :
    centralizer s ≤ MulAction.stabilizer M22 (fixedPoints s) := by
  intro g hg
  apply MulAction.mem_stabilizer_finset'.mpr
  intro x hx
  apply (mem_fixedPoints s _).mpr
  change s.val (g.val x) = g.val x
  have hc := Equiv.congr_fun ((mem_centralizer_iff s g).mp hg) x
  simpa only [Equiv.Perm.mul_apply, (mem_fixedPoints s x).mp hx] using hc.symm

/-- Restriction of the full centralizer action to the fixed points. -/
noncomputable def fixedPointAction (s : m22DesignAut) :
    centralizer s →* Equiv.Perm (fixedPoints s) :=
  (m22SetAction (fixedPoints s)).comp
    (Subgroup.inclusion (centralizer_le_fixedPoints_stabilizer s))

@[simp] theorem fixedPointAction_apply (s : m22DesignAut) (g : centralizer s)
    (x : fixedPoints s) :
    (fixedPointAction s g x).val = (g.val : Equiv.Perm (Fin 22)) x.val := rfl

/-- Faithfulness identifies inner automorphisms with the even design subgroup. -/
theorem induced_inner_iff (s : m22DesignAut) :
    (∃ g : M22, m22DesignAutToAut s = MulAut.conj g) ↔
      (s : Equiv.Perm (Fin 22)) ∈ M22 := by
  constructor
  · rintro ⟨g, hg⟩
    let t : m22DesignAut := ⟨g.val, g.property.1⟩
    have ht : m22DesignAutToAut t = MulAut.conj g := by
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      rw [m22DesignAutToAut_apply_perm, MulAut.conj_apply]
      rfl
    have hst : s = t := m22DesignAutToAut_injective (hg.trans ht.symm)
    exact hst ▸ g.property
  · intro hs
    refine ⟨⟨s.val, hs⟩, ?_⟩
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [m22DesignAutToAut_apply_perm, MulAut.conj_apply]
    rfl

/-- Every abstract outer involution lifts with its order and outer status intact. -/
theorem exists_outer_design_involution (r : MulAut M22) (hr : orderOf r = 2)
    (hi : ¬ ∃ g : M22, r = MulAut.conj g) :
    ∃ s : m22DesignAut, orderOf s = 2 ∧
      (s : Equiv.Perm (Fin 22)) ∉ M22 ∧ m22DesignAutToAut s = r := by
  obtain ⟨s, rfl⟩ := m22DesignAutToAut_surjective r
  refine ⟨s, ?_, fun hs => hi ((induced_inner_iff s).mpr hs), rfl⟩
  rwa [orderOf_injective m22DesignAutToAut m22DesignAutToAut_injective] at hr

/-- The standard odd involution moves fourteen points and fixes eight. -/
theorem standard_outer_fixedPoints_card :
    (fixedPoints m22OuterDesignAut).card = 8 := by
  decide +kernel

end Sporadic.Mathieu.M22OuterCentralizers
