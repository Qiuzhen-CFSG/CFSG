module

public import CFSG.Quasithin.ChapterE.Defs
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Quotient structure of odd E-members

If Q has trivial two-core and Q/O_p(Q) is a two-group, every prime core
other than O_p(Q) vanishes. The group Q is solvable, so its generalized
Fitting subgroup is O_p(Q). For odd p, the two-residual is also O_p(Q):
its quotient is a two-group, and every p-subgroup dies in any two-group
quotient. Surjective residual transport identifies the image of O²(K)
in Q = K/O₂(K) with F*(Q).

These are genuine structure consequences of E.1.2(E1), not assumptions
about irreducibility or the whole quotient's two-rank. They identify the
Frattini section used in E.5.2, printed p.243 of the combined manuscript
of Aschbacher–Smith (1 March 2004).
-/

open Subgroup Theory.GroupTheory

private theorem odd_pCore_eq_residual {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (hq : IsPGroup 2 (G ⧸ pCore p G)) : pResidual 2 G = pCore p G := by
  refine le_antisymm ?_ ?_
  · exact sInf_le ⟨inferInstance, hq⟩
  let q := QuotientGroup.mk' (pResidual 2 G)
  have hz : (pCore p G).map q = ⊥ := disjoint_self.mp
    (IsPGroup.disjoint_of_ne p 2 hp _ _ (pCore_isPGroup.map q)
      ((isPGroup_quotient_pResidual 2).to_subgroup _))
  simpa only [q, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] using hz

private theorem fitting_eq_odd_pCore {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime]
    (hcore : pCore 2 G = ⊥) (hq : IsPGroup 2 (G ⧸ pCore p G)) :
    generalizedFitting G = pCore p G := by
  let _ : Group.IsNilpotent (pCore p G) := pCore_isPGroup.isNilpotent
  let _ : Group.IsNilpotent (G ⧸ pCore p G) := hq.isNilpotent
  let _ : Group.IsSolvable G := (Group.isSolvable_iff_subgroup_quotient (pCore p G)).mpr
    ⟨inferInstance, inferInstance⟩
  have hE : componentLayer G = ⊥ := by
    apply sSup_eq_bot.mpr
    intro L hL
    let _ := hL.2
    let _ : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
    let _ : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
    exact (Group.IsPerfect.not_isSolvable L inferInstance).elim
  rw [generalizedFitting, hE, sup_bot_eq]
  apply le_antisymm ?_ (pCore_le_fitting G p)
  rw [fitting_eq_sup_pCore]
  apply iSup_le
  intro r
  let _ : Fact r.val.val.Prime := ⟨Nat.prime_of_mem_primeFactors r.val.property⟩
  by_cases hr : r.val.val = p
  · rw [hr]
  by_cases hr2 : r.val.val = 2
  · rw [hr2, hcore]
    exact bot_le
  let q := QuotientGroup.mk' (pCore p G)
  have hz : (pCore r.val.val G).map q = ⊥ := disjoint_self.mp
    (IsPGroup.disjoint_of_ne r.val.val 2 hr2 _ _ (pCore_isPGroup.map q)
      (hq.to_subgroup _))
  simpa only [q, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] using hz

namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

/-- The generalized Fitting group in the two-core quotient is its displayed
prime core whenever the remaining quotient is a two-group. -/
public theorem generalizedFitting_quotient_eq_pCore
    (K : Type*) [Group K] [Finite K] (p : ℕ) [Fact p.Prime]
    (hq : IsPGroup 2 ((K ⧸ pCore 2 K) ⧸ pCore p (K ⧸ pCore 2 K))) :
    generalizedFitting (K ⧸ pCore 2 K) = pCore p (K ⧸ pCore 2 K) :=
  fitting_eq_odd_pCore p (pCore_quotient_pCore_eq_bot 2) hq

/-- In E1 the residual image is the actual generalized Fitting subgroup
used by `weakClosureOddRadical`. -/
public theorem ECaseOdd.residual_image_eq_generalizedFitting {A K : Subgroup G} (h : ECaseOdd A K) :
    (pResidual 2 K).map (QuotientGroup.mk' (pCore 2 K)) =
      generalizedFitting (K ⧸ pCore 2 K) := by
  obtain ⟨p, hp, ho, hq, _, _, _⟩ := h
  let _ : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by intro he; subst p; norm_num at ho
  rw [map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _),
    odd_pCore_eq_residual p hp2 hq,
    fitting_eq_odd_pCore p (pCore_quotient_pCore_eq_bot 2) hq]
end CFSG.Quasithin.ChapterE
