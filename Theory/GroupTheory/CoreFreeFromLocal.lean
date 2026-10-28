module

public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Trivial normal core from a local normal subgroup and a conjugate

Let `R` be normal and self-centralizing inside `P`. If its image in the ambient
group is disjoint from a conjugate of `P`, then `P` has trivial normal core.
Indeed, the core intersects `R` trivially. Inside `P` these are disjoint normal
subgroups, so they commute; self-centralization then puts the core inside `R`.

For groups of Lie type this applies to a parabolic radical and an opposite
parabolic. The concrete inputs come from the Levi and centralizer geometry of
GLS3, Theorem 2.6.5 and Section 3.2, `refs/KGroup/GLS3/chapter2.tex` and
`chapter3.tex`. This elementary reduction requires no finiteness or simplicity.
-/

namespace Subgroup

variable {G : Type*} [Group G]

/-- A self-centralizing normal subgroup of `P` that misses a conjugate of `P`
forces the ambient normal core of `P` to be trivial. Normality of `R` is only
inside `P`. The comap here consists of the `x` with `g * x * g⁻¹ ∈ P`. -/
public theorem normalCore_eq_bot_of_disjoint_conjugate
    (P : Subgroup G) (R : Subgroup P) [R.Normal]
    (hc : centralizer (R : Set P) ≤ R) (g : G)
    (hd : Disjoint (R.map P.subtype) (P.comap (MulAut.conj g).toMonoidHom)) :
    P.normalCore = ⊥ := by
  let K : Subgroup P := P.normalCore.subgroupOf P
  have hdK : Disjoint K R := by
    apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    intro x hx
    have hxR : (x : G) ∈ R.map P.subtype := mem_map_of_mem _ hx.2
    have hxP : (x : G) ∈ P.comap (MulAut.conj g).toMonoidHom := hx.1 g
    have heq : (x : G) = 1 :=
      mem_bot.mp ((disjoint_iff.mp hd).le ⟨hxR, hxP⟩)
    exact mem_bot.mpr (Subtype.ext heq)
  have hcK : K ≤ centralizer (R : Set P) :=
    commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint hdK)
  have hK : K = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    exact (disjoint_iff.mp hdK).le ⟨hx, hc (hcK hx)⟩
  rw [← map_subgroupOf_eq_of_le P.normalCore_le]
  change K.map P.subtype = ⊥
  rw [hK, map_bot]

end Subgroup
