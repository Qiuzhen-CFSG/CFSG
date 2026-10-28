module

public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.Exhaustion.Structure
public import Theory.GroupTheory.CComponent.RadicalFree
public import Theory.GroupTheory.SolvableNormalAbelian
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Reduction to simple-component centralizers

A finite group without a nonidentity abelian normal subgroup has trivial
solvable radical: a nonidentity solvable normal subgroup would supply an
abelian characteristic subgroup. Its C-components are consequently simple.
If the centralizer of each such component is solvable, distinct components
cannot commute, so there is exactly one component. Conjugation preserves
components, making this one normal. Its centralizer is then solvable and
normal, hence trivial.

For the projective degree-three application, the absence of a fixed point
also rules out the identity subgroup. The matrix centralizer calculation
and the intrinsic identification of the simple component are separate inputs;
neither is asserted here.

Source: the reduction preceding recognition in GLS3, Theorem 6.5.3,
`refs/KGroup/GLS3/chapter6.tex`, printed p.347; C-component calculus from
Aschbacher–Smith, Proposition A.3.3.
-/

namespace CFSG.Quasithin.MainConverse.LinearThreeSections

open Subgroup Matrix Matrix.PSL3
open scoped MatrixGroups LinearAlgebra.Projectivization

variable {G : Type} [Group G]

/-- Any solvable normal subgroup vanishes when there is no abelian normal subgroup. -/
public theorem normal_solvable_eq_bot_of_not_hasAbelianNormal
    (hG : ¬ HasAbelianNormal G) (R : Subgroup G) [R.Normal]
    [Group.IsSolvable R] : R = ⊥ := by
  by_contra hR
  let : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).mpr hR
  obtain ⟨A, hAchar, hAcomm, hAne⟩ := Group.exists_nontrivial_abelian_characteristic R
  let := hAchar
  let := hAcomm
  apply hG
  exact ⟨A.map R.subtype, inferInstance,
    fun h => hAne ((A.map_eq_bot_iff_of_injective R.subtype_injective).mp h),
    Subgroup.map_isMulCommutative A R.subtype⟩

/-- The local exclusion forces the actual solvable radical to vanish. -/
public theorem solvableRadical_eq_bot_of_not_hasAbelianNormal [Finite G]
    (hG : ¬ HasAbelianNormal G) : Subgroup.solvableRadical G = ⊥ :=
  normal_solvable_eq_bot_of_not_hasAbelianNormal hG _

/-- A nontrivial group without nonidentity abelian normal subgroups is nonsolvable. -/
public theorem not_isSolvable_of_not_hasAbelianNormal [Nontrivial G]
    (hG : ¬ HasAbelianNormal G) : ¬ Group.IsSolvable G := by
  intro hs
  let := hs
  obtain ⟨A, hAn, hAc, hAne⟩ := Group.exists_nontrivial_abelian_normal G
  exact hG ⟨A, hAn, hAne, hAc⟩

/-- Solvable centralizers force a unique component, normal and self-centralizing.
The centralizer premise only concerns nonabelian simple subnormal subgroups. -/
public theorem exists_simple_normal_of_solvable_component_centralizers
    [Finite G] [Nontrivial G] (hG : ¬ HasAbelianNormal G)
    (hcentralizer : ∀ N : Subgroup G, N.IsSubnormal → IsSimpleGroup N →
      ¬ Group.IsSolvable N → Group.IsSolvable (Subgroup.centralizer (N : Set G))) :
    ∃ N : Subgroup G, N.Normal ∧ IsSimpleGroup N ∧ ¬ Group.IsSolvable N ∧
      Subgroup.centralizer (N : Set G) = ⊥ := by
  have hrad := solvableRadical_eq_bot_of_not_hasAbelianNormal hG
  obtain ⟨N, hN⟩ := Subgroup.exists_isCComponent_of_not_isSolvable
    (not_isSolvable_of_not_hasAbelianNormal hG)
  have hsimple : IsSimpleGroup N := hN.isSimpleGroup_of_solvableRadical_eq_bot hrad
  have hsol := hcentralizer N hN.subnormal hsimple hN.not_isSolvable
  let := hsol
  have hunique (K : Subgroup G) (hK : K.IsCComponent) : K = N := by
    by_contra hne
    have hle : K ≤ Subgroup.centralizer (N : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (hK.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot hrad hN hne)
    exact hK.not_isSolvable (Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hle) (Subgroup.inclusion_injective hle))
  have hnormal : N.Normal := Subgroup.normal_iff_map_conj_eq.mpr fun g =>
    hunique _ (hN.map_equiv (MulAut.conj g))
  let := hnormal
  exact ⟨N, hnormal, hsimple, hN.not_isSolvable,
    normal_solvable_eq_bot_of_not_hasAbelianNormal hG _⟩

attribute [local instance] Matrix.instDistribMulActionSpecialLinearGroupForall
  Matrix.instSMulCommClassSpecialLinearGroupForall

/-- The identity projective subgroup fixes a point under its actual scalar preimage. -/
public theorem fixesPointOrDual_bot (F : Type) [Field F] [Finite F] :
    FixesPointOrDual F (⊥ : Subgroup PSL(3,F)) := by
  have hv : (![1,0,0] : Fin 3 → F) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  let p : ℙ F (Fin 3 → F) := Projectivization.mk F ![1,0,0] hv
  refine Or.inl ⟨p, ?_⟩
  intro g hg
  have hq : projection F g = 1 := hg
  calc
    g • p = projection F g • p := rfl
    _ = p := by rw [hq, one_smul]

/-- A subgroup without a projective fixed point or dual point is nontrivial. -/
public theorem nontrivial_of_not_fixesPointOrDual (F : Type) [Field F] [Finite F]
    (U : Subgroup PSL(3,F)) (hU : ¬ FixesPointOrDual F U) : Nontrivial U := by
  apply (Subgroup.nontrivial_iff_ne_bot U).mpr
  intro h
  exact hU (h ▸ fixesPointOrDual_bot F)

end CFSG.Quasithin.MainConverse.LinearThreeSections
