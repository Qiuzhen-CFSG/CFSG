module

public import Theory.GroupTheory.GeneralizedFitting.NoComponentInverter
public import Theory.GroupTheory.CComponent.TwoComponent
public import Theory.GroupTheory.PStar.ActionTools
public import Theory.GroupTheory.PResidual.PrimeToTransport
public import Theory.GroupTheory.PPrimeCoreSurjection
public import Theory.GroupTheory.FiniteParabolicTransfer
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
/-!
# The generalized Fitting subgroup and the prime-complement residual

Every prime core belongs to the corresponding prime residual or complement
core. A component outside the residual centralizes it; its Sylow p-subgroup
is then central, so perfectness and transfer make that component a p'-group.
Subnormal core monotonicity finishes the generalized-Fitting containment.
Pullback through a two-group kernel gives the literal O₂,F* bound at p=3.

Source application: Aschbacher--Smith, 15.2.27(1), printed pp.1118--1119.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
theorem IsComponent.le_primeToResidual_sup_pPrimeCore (p : ℕ) [Fact p.Prime] {L : Subgroup G}
    (hL : IsComponent G L) : L ≤ primeToResidual p G ⊔ pPrimeCore p G := by
  let := hL.2
  rcases hL.normal_dichotomy (primeToResidual p G) with h | hc
  · exact h.trans le_sup_left
  · have hp : Nat.Coprime p (Nat.card L) := by
      let P : Sylow p L := Classical.choice inferInstance
      have hperfect : IsPPerfect p L := by
        intro N hN hq
        let := hN
        let : Group.IsNilpotent (L ⧸ N) := hq.isNilpotent
        exact top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ N)
      apply PStarAction.coprime_card_of_central_sylow hperfect P
      intro x hx
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      have hr : (P : Subgroup L).map L.subtype ≤ primeToResidual p G :=
        le_primeToResidual_of_isPGroup (P.isPGroup'.map _)
      exact ((commutator_eq_bot_iff_le_centralizer.mp hc) y.property x
        (hr (mem_map_of_mem _ hx))).symm
    have he : pPrimeCore p L = ⊤ := top_unique (le_sSup ⟨inferInstance, by simpa using hp⟩)
    have hh := hL.1.pPrimeCore_map_le (p := p)
    rw [he, ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hh.trans le_sup_right

theorem generalizedFitting_le_primeToResidual_sup_pPrimeCore (p : ℕ) [Fact p.Prime] :
    generalizedFitting G ≤ primeToResidual p G ⊔ pPrimeCore p G := by
  apply sup_le
  · exact (fitting_le_pCore_sup_pPrimeCore p).trans
      (sup_le_sup_right (le_primeToResidual_of_isPGroup pCore_isPGroup) _)
  · exact sSup_le fun L hL => IsComponent.le_primeToResidual_sup_pPrimeCore p hL

theorem twoCore_generalizedFitting_preimage_le_three_residual :
    (generalizedFitting (G ⧸ pCore 2 G)).comap (QuotientGroup.mk' (pCore 2 G)) ≤
      primeToResidual 3 G ⊔ pPrimeCore 3 G := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hk : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have ho : pPrimeCore 3 (G ⧸ pCore 2 G) = (pPrimeCore 3 G).map q := by
    rw [← pPrimeCore_comap_eq_of_surjective_coprime 3 q (QuotientGroup.mk'_surjective _) hk,
      map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  have hh := comap_mono (f := q) (generalizedFitting_le_primeToResidual_sup_pPrimeCore (G := G ⧸ pCore 2 G) 3)
  rw [← map_primeToResidual_of_surjective 3 q (QuotientGroup.mk'_surjective _), ho,
    ← Subgroup.map_sup, comap_map_eq] at hh
  have hker : q.ker ≤ pPrimeCore 3 G := le_sSup ⟨inferInstance, hk⟩
  exact hh.trans (sup_le le_rfl (hker.trans le_sup_right))
end Theory.GroupTheory
