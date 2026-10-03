module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic


/-!
# A large subgroup with prescribed commutator bound

Let V be contained in an abelian subgroup W. Suppose an index-two subgroup
of the actors centralizes W, and all commutators of W with the actors lie
in a subgroup R of W. For any target subgroup L there is K≤V whose
commutators lie in L, with |V|≤|R:R∩L| |K|. Neither invariance of V under
the actors nor containment of L in R is required.

Choose an actor outside the centralizing subgroup. Its commutator map on
V is a homomorphism into R because W is abelian. Compose with R/(R∩L)
and take its kernel. The kernel/image cardinality identity gives the size
bound; the two actor cosets show that the entire acting subgroup has its
commutator with that kernel in L.

This is the elementary kernel argument behind the first branch of
Stellmacher (9.8), printed p.55 of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Subgroup
open scoped commutatorElement

public theorem exists_large_subgroup_commutator_le_of_index_two
    {G : Type*} [Group G] [Finite G]
    (V W actors central target image : Subgroup G)
    (hVW : V ≤ W) (hcommW : IsMulCommutative W)
    (himageW : image ≤ W)
    (hcomm : ⁅W, actors⁆ ≤ image)
    (hcentral : central ≤ actors) (hcentralW : central ≤ centralizer (W : Set G))
    (hindex : central.relIndex actors = 2) :
    ∃ K : Subgroup G, K ≤ V ∧
      Nat.card V ≤ target.relIndex image * Nat.card K ∧ ⁅K, actors⁆ ≤ target := by
  classical
  let _ : IsMulCommutative W := hcommW
  have hcommImage : IsMulCommutative image :=
    le_centralizer_iff_isMulCommutative.mp
      (himageW.trans ((le_centralizer_iff_isMulCommutative.mpr hcommW).trans
        (centralizer_le himageW)))
  let _ : IsMulCommutative image := hcommImage
  let _ : CommGroup image := IsMulCommutative.instCommGroup
  let line := target.subgroupOf image
  obtain ⟨actor, hactor, hactorNot⟩ : ∃ actor ∈ actors, actor ∉ central := by
    by_contra! hle
    have heq : central = actors := le_antisymm hcentral hle
    rw [heq, relIndex_self] at hindex
    omega
  let displacement : V →* image := {
    toFun := fun element => ⟨⁅(element : G), actor⁆,
      hcomm (commutator_mem_commutator (hVW element.property) hactor)⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' := by
      intro x y
      apply Subtype.ext
      change ⁅(x : G) * (y : G), actor⁆ = ⁅(x : G), actor⁆ * ⁅(y : G), actor⁆
      rw [commutatorElement_mul_left_eq_conj_mul]
      have hy : ⁅(y : G), actor⁆ ∈ W :=
        himageW (hcomm (commutator_mem_commutator (hVW y.property) hactor))
      have hx : ⁅(x : G), actor⁆ ∈ W :=
        himageW (hcomm (commutator_mem_commutator (hVW x.property) hactor))
      have hxy : (x : G) * ⁅(y : G), actor⁆ = ⁅(y : G), actor⁆ * (x : G) :=
        (le_centralizer_iff_isMulCommutative.mpr hcommW) (hVW x.property) _ hy |>.symm
      have hcc : ⁅(y : G), actor⁆ * ⁅(x : G), actor⁆ =
          ⁅(x : G), actor⁆ * ⁅(y : G), actor⁆ :=
        (le_centralizer_iff_isMulCommutative.mpr hcommW) hy _ hx |>.symm
      rw [hxy, mul_inv_cancel_right, hcc] }
  let quotient := (QuotientGroup.mk' line).comp displacement
  let K := quotient.ker.map V.subtype
  have hKV : K ≤ V := map_subtype_le _
  refine ⟨K, hKV, ?_, ?_⟩
  · have hbound : Nat.card quotient.range ≤ target.relIndex image := by
      exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    have hmul := quotient.ker.index_mul_card
    rw [index_ker] at hmul
    have hcard : Nat.card K = Nat.card quotient.ker := card_map_of_injective V.subtype_injective
    rw [hcard, ← hmul]
    exact Nat.mul_le_mul_right _ hbound
  · apply commutator_le.mpr
    intro element helement mover hmover
    obtain ⟨elementV, helementKernel, rfl⟩ := helement
    have helementW := hVW elementV.property
    have hmain : ⁅(elementV : G), actor⁆ ∈ target := by
      have hq : quotient elementV = 1 := helementKernel
      exact (QuotientGroup.eq_one_iff (displacement elementV)).mp hq
    change ⁅(elementV : G), mover⁆ ∈ target
    by_cases hmoverCentral : mover ∈ central
    · have hc : ⁅(elementV : G), mover⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr
          (mem_centralizer_iff.mp (hcentralW hmoverCentral) _ helementW)
      rw [hc]
      exact target.one_mem
    have hfactor : actor⁻¹ * mover ∈ central := by
      have hh := (central.subgroupOf actors).mul_mem_iff_of_index_two hindex
        (a := ⟨actor⁻¹, actors.inv_mem hactor⟩) (b := ⟨mover, hmover⟩)
      exact hh.mpr (by simp only [mem_subgroupOf, inv_mem_iff, hactorNot, hmoverCentral])
    have hfactorComm : ⁅actor⁻¹ * mover, (elementV : G)⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        (mem_centralizer_iff.mp (hcentralW hfactor) _ helementW).symm
    have heq : ⁅mover, (elementV : G)⁆ = ⁅actor, (elementV : G)⁆ := by
      have hh := commutatorElement_mul_left_eq_conj_mul actor (actor⁻¹ * mover) (elementV : G)
      simpa only [mul_inv_cancel_left, hfactorComm, mul_one, mul_inv_cancel, one_mul] using hh
    rw [← commutatorElement_inv, heq, commutatorElement_inv]
    exact hmain

end Subgroup
