module

public import Theory.GroupTheory.ZStar.LocalReduction
public import Theory.GroupTheory.ZStar.OddCommutators

/-!
# Global isolation from Sylow weak closure

An involution that is central and weakly closed in a chosen Sylow two-subgroup
has no distinct commuting conjugate in the whole group. For a commuting
conjugate, work inside the involution's centralizer. Sylow conjugacy there
moves that conjugate into the chosen Sylow subgroup, where weak closure
identifies it with the involution. The conjugating element centralizes the
involution, so this equality also holds before conjugation.

The already proved global isolation theorem then gives odd order for every
commutator with the involution, and hence for its product with every conjugate.
These are the final local-to-global lemmas from historical
`Submission/ZStar/OddCommutators.lean` at commit `c3503435`, needed by the
principal-block argument and the core-free induction. The chosen Sylow subgroup,
production involution predicate, and exposed weak-closure predicate are reused
without alteration.
-/

namespace Glauberman.ZStar

open BenderSuzuki.PFAppendixIII

/-- Centrality and weak closure in a Sylow two-subgroup imply global isolation. -/
public theorem isolated_of_central_weaklyClosed
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (t : G) (htI : IsInvolution t)
    (htCentral : ∀ s, s ∈ (S : Subgroup G) → s * t = t * s)
    (htWeak : IsWeaklyClosedInSylow t (S : Subgroup G)) :
    ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t := by
  classical
  intro g hcomm
  let u := g * t * g⁻¹
  have huI : IsInvolution u := by
    simpa [u, rightConjugateElem, mul_assoc] using
      (isInvolution_rightConjugateElem (g := g⁻¹) htI)
  let C := Subgroup.centralizer ({t} : Set G)
  have hSC : (S : Subgroup G) ≤ C :=
    fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr (htCentral s hs)
  let SC := S.subtype hSC
  have huC : u ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  let uC : C := ⟨u, huC⟩
  have horder : orderOf uC = 2 := by
    rw [← Subgroup.orderOf_coe uC]
    exact orderOf_eq_two (by simpa [pow_two] using huI.sq_eq_one) huI.ne_one
  have hzpow : IsPGroup 2 (Subgroup.zpowers uC) := by
    apply IsPGroup.of_card (n := 1)
    simpa only [Nat.card_zpowers, pow_one] using horder
  obtain ⟨T, hT⟩ := hzpow.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C T SC
  have huT : uC ∈ (T : Subgroup C) := hT (Subgroup.mem_zpowers uC)
  have hcuSC : c * uC * c⁻¹ ∈ (SC : Subgroup C) := by
    have hmem : c * uC * c⁻¹ ∈ ((c • T : Sylow 2 C) : Subgroup C) := by
      rw [Sylow.coe_subgroup_smul]
      exact Set.mem_smul_set.mpr ⟨uC, huT, rfl⟩
    simpa [hc] using hmem
  have hcuS : (c : G) * u * (c : G)⁻¹ ∈ (S : Subgroup G) := by
    simpa [SC, Sylow.coe_subtype, Subgroup.mem_subgroupOf, uC] using hcuSC
  have hcg : ((c : G) * g) * t * ((c : G) * g)⁻¹ =
      (c : G) * u * (c : G)⁻¹ := by dsimp [u]; group
  have hcut : (c : G) * u * (c : G)⁻¹ = t :=
    hcg.symm.trans (htWeak.2 ((c : G) * g) (hcg ▸ hcuS))
  have hct : (c : G) * t = t * (c : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp c.property
  change u = t
  calc
    u = (c : G)⁻¹ * ((c : G) * u * (c : G)⁻¹) * (c : G) := by group
    _ = (c : G)⁻¹ * t * (c : G) := by rw [hcut]
    _ = (c : G)⁻¹ * (t * (c : G)) := by rw [mul_assoc]
    _ = (c : G)⁻¹ * ((c : G) * t) := by rw [← hct]
    _ = t := by simp

/-- Local weak closure and centrality force every commutator with the
involution to have odd order. -/
public theorem orderOf_commutator_odd_of_weaklyClosed
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (t : G) (htI : IsInvolution t)
    (htCentral : ∀ s, s ∈ (S : Subgroup G) → s * t = t * s)
    (htWeak : IsWeaklyClosedInSylow t (S : Subgroup G)) (g : G) :
    Odd (orderOf (g * t * g⁻¹ * t⁻¹)) :=
  orderOf_commutator_odd_of_isolated_involution htI
    (fun g hg => isolated_of_central_weaklyClosed S t htI htCentral htWeak g hg.eq) g

/-- Local weak closure and centrality force the product of the involution
with each conjugate to have odd order. -/
public theorem orderOf_conjugate_mul_odd_of_weaklyClosed
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (t : G) (htI : IsInvolution t)
    (htCentral : ∀ s, s ∈ (S : Subgroup G) → s * t = t * s)
    (htWeak : IsWeaklyClosedInSylow t (S : Subgroup G)) (g : G) :
    Odd (orderOf ((g * t * g⁻¹) * t)) := by
  simpa [htI.inv_eq_self] using orderOf_commutator_odd_of_weaklyClosed S t htI htCentral htWeak g

end Glauberman.ZStar
