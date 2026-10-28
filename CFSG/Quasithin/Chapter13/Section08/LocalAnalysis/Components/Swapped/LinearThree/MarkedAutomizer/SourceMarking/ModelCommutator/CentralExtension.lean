module

public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.PerfectCover
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

/-!
# A commutator calculation for central covers of S₄

For a finite central extension of S₄, the two-residual and any Sylow
two-subgroup generate the group. Their commutator maps onto A₄: every
even permutation is a product of two commutators with a fixed odd
permutation. Taking the two-residual still maps onto A₄. The quotient
above this residual is central-by-cyclic, hence abelian, so the residual
equals the full derived subgroup.

This structural calculation is the local ingredient for the literal
hexacode cover mark. It uses neither a splitting nor local quotient orders.
Source application: Aschbacher–Smith, Notation 13.2.1 and Lemma 13.2.2(3),
printed pp.877–878, used in 13.8.16(1), printed p.952.
-/

public section

open Subgroup
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer.ModelCommutator

private abbrev S4 := Equiv.Perm (Fin 4)

private theorem symmetric_residual : pResidual 2 S4 = alternatingGroup (Fin 4) := by
  apply le_antisymm
  · apply sInf_le
    refine ⟨inferInstance, IsPGroup.of_card (n := 1) ?_⟩
    change (alternatingGroup (Fin 4)).index = 2 ^ 1
    simp
  · rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro g hg
    apply mem_pResidual_of_orderOf_coprime
    rw [Equiv.Perm.IsThreeCycle.orderOf hg]
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem odd_commutator_certificate :
    ∀ u : S4, u.sign ≠ 1 → ∀ g : S4, g.sign = 1 →
      ∃ a b : alternatingGroup (Fin 4),
        ⁅(a : S4), u⁆ * ⁅(b : S4), u⁆ = g := by
  decide +kernel

private theorem symmetric_commutator (S : Subgroup S4)
    (hgen : alternatingGroup (Fin 4) ⊔ S = ⊤) :
    ⁅alternatingGroup (Fin 4), S⁆ = alternatingGroup (Fin 4) := by
  have hex : ∃ u ∈ S, (u : S4).sign ≠ 1 := by
    by_contra! hn
    have hS : S ≤ alternatingGroup (Fin 4) := hn
    have ht : (⊤ : Subgroup S4) ≤ alternatingGroup (Fin 4) := by
      rw [← hgen]
      exact sup_le le_rfl hS
    have hf := ht (mem_top (Equiv.swap (0 : Fin 4) 1))
    norm_num [Equiv.Perm.mem_alternatingGroup] at hf
  obtain ⟨u, hu, ho⟩ := hex
  apply le_antisymm (commutator_le_left _ _)
  intro g hg
  obtain ⟨a, b, rfl⟩ := odd_commutator_certificate u ho g hg
  exact mul_mem (commutator_mem_commutator a.property hu)
    (commutator_mem_commutator b.property hu)

private theorem central_cyclic_lift {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : f.ker ≤ center G) (N : Subgroup G) [N.Normal]
    (A : Subgroup H) [A.Normal] [IsCyclic (H ⧸ A)] (hN : N.map f = A) :
    commutator G ≤ N := by
  have hle : N ≤ A.comap f := by
    rw [← hN]
    exact le_comap_map f N
  let F := QuotientGroup.map N A f hle
  have hker : F.ker ≤ center (G ⧸ N) := by
    intro z hz
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N z
    have hfg : f g ∈ A := by
      apply (QuotientGroup.eq_one_iff _).mp
      exact hz
    obtain ⟨n, hn, he⟩ := mem_map.mp (hN ▸ hfg)
    have hk : g * n⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
    have hc := hf hk
    have hq : QuotientGroup.mk' N g = QuotientGroup.mk' N (g * n⁻¹) := by
      simp only [map_mul, map_inv]
      have hqn : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
      rw [hqn, inv_one, mul_one]
    rw [hq]
    rw [mem_center_iff]
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective N y
    simpa only [map_mul] using congrArg (QuotientGroup.mk' N) (mem_center_iff.mp hc h)
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
    (F.isMulCommutative_of_isCyclic_of_ker_le_center hker)

/-- In a finite central cover of S₄, the residual of the residual–Sylow
commutator is exactly the full derived subgroup. -/
theorem central_symmetric_residual_commutator {G : Type*} [Group G] [Finite G]
    (f : G →* Equiv.Perm (Fin 4)) (hf : Function.Surjective f) (hker : f.ker ≤ center G)
    (U : Sylow 2 G) :
    (pResidual 2 (⁅pResidual 2 G, (U : Subgroup G)⁆ : Subgroup G)).map
      ⁅pResidual 2 G, (U : Subgroup G)⁆.subtype = commutator G := by
  let D := ⁅pResidual 2 G, (U : Subgroup G)⁆
  have hgen := pResidual_sup_sylow_eq_top U
  let hDn : D.Normal := normalizer_eq_top_iff.mp (top_unique (hgen ▸
    sup_le (normalizer_commutator_ge_left _ _) (normalizer_commutator_ge_right _ _)))
  let E := (pResidual 2 D).map D.subtype
  have hE : E.Normal := inferInstance
  let A := alternatingGroup (Fin 4)
  have hR : (pResidual 2 G).map f = A := by
    rw [map_pResidual_of_surjective 2 f hf, symmetric_residual]
  have hD : D.map f = A := by
    dsimp only [D]
    rw [map_commutator, hR]
    apply symmetric_commutator
    change A ⊔ (U : Subgroup G).map f = ⊤
    rw [← hR, ← Subgroup.map_sup, hgen, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact hf
  have hA : (pResidual 2 A).map A.subtype = A := by
    have hp : IsPPerfect 2 A := by
      change IsPPerfect 2 (alternatingGroup (Fin 4))
      rw [← symmetric_residual]
      exact isPPerfect_pResidual (G := S4) 2
    rw [(pResidual_eq_top_iff 2 A).mpr hp, ← MonoidHom.range_eq_map, range_subtype]
  have hmap : E.map f = A := by
    dsimp only [E]
    rw [map_embedded_pResidual, hD, hA]
  let : IsCyclic (S4 ⧸ A) := isCyclic_of_prime_card (p := 2) (by
    change A.index = 2
    exact alternatingGroup.index_eq_two)
  apply le_antisymm
  · exact (map_subtype_le _).trans (commutator_mono le_top le_top)
  · exact central_cyclic_lift f hker E A hmap

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer.ModelCommutator

end
