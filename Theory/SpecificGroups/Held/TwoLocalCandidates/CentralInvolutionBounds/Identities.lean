module
public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Tables2
/-!
# The central involution in the literal max5 subgroup

The published permutation tables certify that the fourth power of max5First
is a nonidentity involution and commutes with both actual max5 generators.
Closure then gives containment of max5 in its centralizer.
Source: ATLAS HeG1-max5W1; GLS3 Table 5.3p, the 2B centralizer.
-/
namespace Held.TwoLocalCandidates.CentralInvolutionBounds
open Cores Cores.Tables2
public theorem p2_eq_representation : p2 = representation (max5First ^ 4) := by
  rw [p2_eq]
  simp only [coreGenerator, coreWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, embedding, MonoidHom.comp_apply,
    map_zpow]
  rfl
public theorem orderOf_centralInvolution : orderOf (max5First ^ 4) = 2 := by
  rw [← orderOf_injective representation representation_injective, ← p2_eq_representation]
  apply orderOf_eq_prime
  · apply Equiv.ext
    apply allLetters
    set_option maxRecDepth 16384 in
    set_option maxHeartbeats 8000000 in
      decide +kernel
  · intro h
    have h0 := congrArg (fun p : Equiv.Perm (Fin 2058) => p 0) h
    have hn : p2 0 ≠ (0 : Fin 2058) := by decide +kernel
    exact hn h0
public theorem max5_le_centralizer :
    max5 ≤ Subgroup.centralizer ({max5First ^ 4} : Set He) := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases Set.mem_insert_iff.mp hg with rfl | hg
  · apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact (Commute.self_pow max5First 4).eq
  · have he : g = max5Second := Set.mem_singleton_iff.mp hg
    subst g
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply representation_injective
    have hp : representation max5Second = p1 := p1_eq.symm
    have hz := p2_eq_representation.symm
    have hc : p1 * p2 = p2 * p1 := by
      apply Equiv.ext
      apply allLetters
      set_option maxRecDepth 16384 in
      set_option maxHeartbeats 8000000 in
        decide +kernel
    exact (map_mul representation max5Second (max5First ^ 4)).trans
      ((congrArg₂ (· * ·) hp hz).trans
        (hc.trans ((congrArg₂ (· * ·) hz.symm hp.symm).trans
          (map_mul representation (max5First ^ 4) max5Second).symm)))

end Held.TwoLocalCandidates.CentralInvolutionBounds
