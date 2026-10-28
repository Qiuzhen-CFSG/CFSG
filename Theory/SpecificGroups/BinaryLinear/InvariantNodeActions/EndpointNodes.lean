module
public import Theory.SpecificGroups.BinaryLinear.EndpointMinimalPair
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.FirstPair
public import Theory.GroupTheory.SylowIndexThreeQuotient

/-!
# Endpoint data under a fixed binary flag marking

The first-node quotient and residual-size calculations transfer to the last
node through a graph automorphism adjusted to preserve the prescribed Sylow
flag. Both endpoints therefore have literal S₃ two-core quotients and
residuals of order at least sixteen, using the original basis throughout.
For every node, the three-coset action and self-normalizing full flag
also identify the literal S₃ quotient.
This is the marked version of the endpoint-pair construction, used to lift
the endpoints through a possibly nontrivial two-core in the constrained case.

Source: Aschbacher--Smith 15.1.22(3), printed pp.1099--1100.
-/

public section
open Subgroup
namespace BinaryLinear.InvariantNodeActions
open OuterCyclic OrderedResidualConjugators

/-- The two endpoints of the prescribed flag have large two-residuals and
literal symmetric-three quotients, without changing the flag marking. -/
theorem endpoint_node_data {m : ℕ} (hm : 3 ≤ m)
    (S : Sylow 2 (LinearGroup (m+1))) (b : Basis m)
    (hb : (S : Subgroup _) = cutStabilizer b Set.univ)
    (j : Fin m) (hj : j.val = 0 ∨ j.val = m-1) :
    Nonempty ((minimalParabolic b j ⧸ pCore 2 (minimalParabolic b j)) ≃*
      Equiv.Perm (Fin 3)) ∧
      16 ≤ Nat.card (pResidual 2 (minimalParabolic b j)) := by
  let : Finite (LinearGroup (m+1)) := Finite.of_injective
    (fun g : LinearGroup (m+1) => (g : Space (m+1) → Space (m+1))) DFunLike.coe_injective
  let i : Fin m := ⟨0,by omega⟩
  let P := minimalParabolic b i
  let Q := minimalParabolic b i.rev
  let γ := graphLinear (m+1)
  let S' := S.mapSurjective (f := γ.symm.toMonoidHom) γ.symm.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (LinearGroup (m+1)) S S'
  have hg' : (S : Subgroup _).map (MulAut.conj g).toMonoidHom = S' := by
    exact congrArg (fun U : Sylow 2 (LinearGroup (m+1)) => (U : Subgroup (LinearGroup (m+1)))) hg
  have hfix : (cutStabilizer b Set.univ).map (γ * MulAut.conj g).toMonoidHom =
      cutStabilizer b Set.univ := by
    rw [←hb]
    change (S : Subgroup _).map (γ.toMonoidHom.comp (MulAut.conj g).toMonoidHom) = _
    rw [←map_map,hg']
    change ((S : Subgroup _).map γ.symm.toMonoidHom).map γ.toMonoidHom = _
    ext x
    simp only [mem_map_equiv,MulEquiv.symm_symm,MulEquiv.apply_symm_apply]
  have hpq : P.map (γ * MulAut.conj g).toMonoidHom = Q :=
    graph_inner_reverses_minimalParabolic b g hfix i
  let ep : P ≃* Q := ((γ * MulAut.conj g).subgroupMap P).trans (MulEquiv.subgroupCongr hpq)
  have hPcard : 16 ≤ Nat.card (pResidual 2 P) := by
    have hh := first_node_residual_card_ge_sixteen hm b
    rwa [nodeResidual,card_subtype] at hh
  let eqP := first_node_quotient hm b
  rcases hj with hj | hj
  · have he : j = i := Fin.ext hj
    subst j
    exact ⟨⟨eqP⟩,hPcard⟩
  · have he : j = i.rev := Fin.ext (by simpa [i,Fin.val_rev] using hj)
    subst j
    refine ⟨⟨(QuotientGroup.congr _ _ ep (pCore_map_iso 2 ep)).symm.trans eqP⟩,?_⟩
    rw [←map_pResidual_of_surjective 2 ep.toMonoidHom ep.surjective,
      card_map_of_injective ep.injective]
    exact hPcard
/-- Every binary node has its literal S₃ two-core quotient. -/
theorem node_quotient {m : ℕ}
    (S : Sylow 2 (LinearGroup (m+1))) (b : Basis m)
    (hb : (S : Subgroup _) = cutStabilizer b Set.univ) (i : Fin m) :
    Nonempty ((minimalParabolic b i ⧸ pCore 2 (minimalParabolic b i)) ≃*
      Equiv.Perm (Fin 3)) := by
  let : Finite (LinearGroup (m+1)) := Finite.of_injective
    (fun g : LinearGroup (m+1) => (g : Space (m+1) → Space (m+1))) DFunLike.coe_injective
  let P := minimalParabolic b i
  have hSP : (S : Subgroup _) ≤ P := by
    rw [hb]
    exact (cutStabilizer_le_iff _ _ _).mpr (Set.subset_univ _)
  let U := S.subtype hSP
  have hi : (U : Subgroup P).index = 3 := by
    change (S : Subgroup _).relIndex P = 3
    rw [hb]
    exact BinaryLinear.CubicSylowGeneration.minimalParabolic_index b i
  apply sylow_index_three_core_quotient U hi
  apply lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal U)
  intro he
  have hn : ((S : Subgroup _).subgroupOf P).Normal := by
    change (U : Subgroup P).Normal
    rw [←he]
    infer_instance
  have hnorm := (normal_subgroupOf_iff_le_normalizer hSP).mp hn
  rw [hb,BinaryLinear.SylowFlagOvergroups.normalizer_fullFlag_eq] at hnorm
  have hsame : P = (S : Subgroup _) := le_antisymm (hb ▸ hnorm) hSP
  change (S : Subgroup _).relIndex P = 3 at hi
  rw [hsame,relIndex_self] at hi
  norm_num at hi
end BinaryLinear.InvariantNodeActions

