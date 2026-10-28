module

public import Mathlib.LinearAlgebra.Eigenspace.Pi

universe u v w

namespace Theory.AlgebraicGroup.Bor1

variable {k : Type u} [Field k]
variable {ι : Type v} {V : Type w} [AddCommGroup V] [Module k V]

/-- The common eigenspaces of an arbitrary family of endomorphisms are
independent when indexed by their full joint eigenvalue functions.  No
commutativity assumption on the endomorphisms is required. -/
public theorem iSupIndep_commonEigenspaces (f : ι → Module.End k V) :
    iSupIndep fun χ : ι → k => ⨅ i, (f i).eigenspace (χ i) := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
      intro vectors hvectors hsum χ hχ
      by_cases hother : ∃ ψ ∈ s, ψ ≠ χ
      · obtain ⟨ψ, hψ, hψχ⟩ := hother
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hψχ
        let shifted : (ι → k) → V := fun μ => (μ i - χ i) • vectors μ
        have hshifted_mem : ∀ μ ∈ s,
            shifted μ ∈ ⨅ j, (f j).eigenspace (μ j) := by
          intro μ hμ
          exact (⨅ j, (f j).eigenspace (μ j)).smul_mem _ (hvectors μ hμ)
        have hshifted_sum : ∑ μ ∈ s, shifted μ = 0 := by
          calc
            ∑ μ ∈ s, shifted μ =
                (f i - χ i • (LinearMap.id : Module.End k V))
                  (∑ μ ∈ s, vectors μ) := by
              simp only [shifted, map_sum, LinearMap.sub_apply,
                LinearMap.smul_apply, LinearMap.id_apply]
              apply Finset.sum_congr rfl
              intro μ hμ
              have hmem := hvectors μ hμ
              rw [Submodule.mem_iInf] at hmem
              have heigen := Module.End.mem_eigenspace_iff.mp (hmem i)
              rw [heigen]
              exact sub_smul (μ i) (χ i) (vectors μ)
            _ = 0 := by rw [hsum]; simp
        have hshiftedχ : shifted χ = 0 := by simp [shifted]
        have hshifted_erase : ∑ μ ∈ s.erase χ, shifted μ = 0 := by
          calc
            ∑ μ ∈ s.erase χ, shifted μ =
                (∑ μ ∈ s.erase χ, shifted μ) + shifted χ := by
              rw [hshiftedχ, add_zero]
            _ = ∑ μ ∈ s, shifted μ := Finset.sum_erase_add _ _ hχ
            _ = 0 := hshifted_sum
        have hψerase : ψ ∈ s.erase χ :=
          Finset.mem_erase.mpr ⟨hψχ, hψ⟩
        have hshiftedψ : shifted ψ = 0 :=
          ih (s.erase χ) (Finset.erase_ssubset hχ)
            shifted (fun μ hμ => hshifted_mem μ (Finset.mem_of_mem_erase hμ))
            hshifted_erase ψ hψerase
        have hvectorsψ : vectors ψ = 0 := by
          have hcoeff : ψ i - χ i ≠ 0 := sub_ne_zero.mpr hi
          exact (smul_eq_zero.mp hshiftedψ).resolve_left hcoeff
        have horiginal_erase : ∑ μ ∈ s.erase ψ, vectors μ = 0 := by
          calc
            ∑ μ ∈ s.erase ψ, vectors μ =
                (∑ μ ∈ s.erase ψ, vectors μ) + vectors ψ := by
              rw [hvectorsψ, add_zero]
            _ = ∑ μ ∈ s, vectors μ := Finset.sum_erase_add _ _ hψ
            _ = 0 := hsum
        exact ih (s.erase ψ) (Finset.erase_ssubset hψ)
          vectors (fun μ hμ => hvectors μ (Finset.mem_of_mem_erase hμ))
          horiginal_erase χ (Finset.mem_erase.mpr ⟨hψχ.symm, hχ⟩)
      · have hs : s = {χ} := by
          apply Finset.eq_singleton_iff_unique_mem.mpr
          refine ⟨hχ, ?_⟩
          intro ψ hψ
          by_contra hψχ
          exact hother ⟨ψ, hψ, hψχ⟩
        subst s
        simpa using hsum

end Theory.AlgebraicGroup.Bor1
