module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.IntrinsicSource

/-!
# Assembling the intrinsic A₃ system in 14.4.13

The local model and parabolic calculations are explicit premises. From them
we derive the chamber, its Sylow witnesses, intrinsic generatedness, and D4
using the unique maximal two-local overgroup and the residual normalizer.
All quotients and parabolics are transported to the literal generated group
G₀. Applying the earlier I.5.1 recognition implication there gives the final
order contradiction. No equality between G₀ and the ambient group is used.

These are conditional assembly lemmas, not proofs of the still-required
14.4.6--12 model calculations or their parabolic consequences.

Source: Aschbacher--Smith, combined 1 March 2004 manuscript, 14.4.13,
printed p.1012.
-/

public section

open Subgroup

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.IntrinsicSource

universe u
variable {G : Type u} [Group G]

private theorem chamber_eq_of_point_parabolics (A B C T : Subgroup G) (hTA : T ≤ A)
    (h : Quasithin.I5.RankTwoParabolics A (T.subgroupOf A)
      (B.subgroupOf A) (C.subgroupOf A)) :
    Quasithin.I5.chamberSubgroup ![A, B, C] = T := by
  ext x
  simp only [Quasithin.I5.chamberSubgroup, Subgroup.mem_iInf, Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.forall_fin_zero, and_true]
  constructor
  · rintro ⟨ha, hb, hc⟩
    have hx : (⟨x, ha⟩ : A) ∈ B.subgroupOf A ⊓ C.subgroupOf A := ⟨hb, hc⟩
    rw [h.borel_eq] at hx
    exact hx
  · intro ht
    have hx : (⟨x, hTA ht⟩ : A) ∈ B.subgroupOf A ⊓ C.subgroupOf A := by
      rw [h.borel_eq]
      exact ht
    exact ⟨hTA ht, hx.1, hx.2⟩

/-- Assemble D1--D5 on the actual generated subgroup. The only source inputs
beyond the three local quotients and parabolics are ambient uniqueness,
normality of L in M, and the marked residual-normalizer calculation. -/
noncomputable def source_dSystem [Finite G]
    (L L₁ L₂ X M : Subgroup G) (T : Sylow 2 G)
    (hq₁ : Nonempty (coreQuotient (L ⊔ (T : Subgroup G)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)))
    (hq₂ : Nonempty (coreQuotient (L₁ ⊔ X ⊔ (T : Subgroup G)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hq₃ : Nonempty (coreQuotient (localJoin L₂ X ⊔ (T : Subgroup G)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)))
    (hp₁ : Quasithin.I5.RankTwoParabolics (L ⊔ (T : Subgroup G) : Subgroup G)
      ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G)))
      ((L₁ ⊔ X ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G)))
      ((localJoin L₂ X ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))))
    (hp₂ : Quasithin.I5.RankTwoParabolics (L₁ ⊔ X ⊔ (T : Subgroup G) : Subgroup G)
      ((T : Subgroup G).subgroupOf (L₁ ⊔ X ⊔ (T : Subgroup G)))
      ((L ⊔ (T : Subgroup G)).subgroupOf (L₁ ⊔ X ⊔ (T : Subgroup G)))
      ((localJoin L₂ X ⊔ (T : Subgroup G)).subgroupOf (L₁ ⊔ X ⊔ (T : Subgroup G))))
    (hp₃ : Quasithin.I5.RankTwoParabolics (localJoin L₂ X ⊔ (T : Subgroup G) : Subgroup G)
      ((T : Subgroup G).subgroupOf (localJoin L₂ X ⊔ (T : Subgroup G)))
      ((L ⊔ (T : Subgroup G)).subgroupOf (localJoin L₂ X ⊔ (T : Subgroup G)))
      ((L₁ ⊔ X ⊔ (T : Subgroup G)).subgroupOf (localJoin L₂ X ⊔ (T : Subgroup G))))
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → L ⊔ (T : Subgroup G) ≤ K → K = M)
    (hLM : M ≤ normalizer (L : Set G))
    (hres : twoResidual (L ⊓ (localJoin L₂ X ⊔ (T : Subgroup G))) = L₂)
    (hnorm : (localJoin L₂ X ⊔ (T : Subgroup G)) ⊓ normalizer (L₂ : Set G) ≤
      L₂ ⊔ (T : Subgroup G))
    (hPM : L₂ ⊔ (T : Subgroup G) ≤ M)
    (hproper : IsCoatom ((L₂ ⊔ (T : Subgroup G)).subgroupOf
      (localJoin L₂ X ⊔ (T : Subgroup G)))) :
    Quasithin.I5.DSystem .A3 (actualG0 L T L₁ L₂ X) := by
  let K := actualG0 L T L₁ L₂ X
  let F := sourceVertex L T L₁ L₂ X
  let F₀ : Fin 3 → Subgroup K := fun i => (F i).subgroupOf K
  have hch : Quasithin.I5.chamberSubgroup F = (T : Subgroup G) :=
    chamber_eq_of_point_parabolics _ _ _ _ le_sup_right hp₁
  have hch₀ : Quasithin.I5.chamberSubgroup F₀ = (T : Subgroup G).subgroupOf K := by
    change (⨅ i, (F i).comap K.subtype) = ((T : Subgroup G).comap K.subtype)
    rw [← Subgroup.comap_iInf]
    exact congrArg (fun A : Subgroup G => A.subgroupOf K) hch
  have hs (i : Fin 3) : ∃ S : Sylow 2 (F i),
      (S : Subgroup (F i)) = (T : Subgroup G).subgroupOf (F i) := by
    have ht : (T : Subgroup G) ≤ F i := by
      fin_cases i <;> exact le_sup_right
    exact ⟨T.subtype ht, rfl⟩
  obtain ⟨q₁, s₁, p₁⟩ := source_vertex_restriction L T L₁ L₂ X (F 1) (F 2) 0
    _ hq₁ (hs 0) hp₁
  obtain ⟨q₂, s₂, p₂⟩ := source_vertex_restriction L T L₁ L₂ X (F 0) (F 2) 1
    _ hq₂ (hs 1) hp₂
  obtain ⟨q₃, s₃, p₃⟩ := source_vertex_restriction L T L₁ L₂ X (F 0) (F 1) 2
    _ hq₃ (hs 2) hp₃
  refine {
    family := F₀
    finite_vertex := fun _ => inferInstance
    point_A3 := fun _ => q₁
    point_C3 := by simp
    line_quotient := q₂
    plane_quotient := q₃
    sylow := ?_
    point_parabolics := ?_
    line_parabolics := ?_
    plane_parabolics := ?_
    generate := ?_
    core_free := ?_
    nondegenerate := by simp }
  · intro i
    rw [hch₀]
    fin_cases i
    · exact s₁
    · exact s₂
    · exact s₃
  · rw [hch₀]
    exact p₁
  · rw [hch₀]
    exact p₂
  · rw [hch₀]
    exact p₃
  · simpa [F₀, F, sourceVertex] using source_vertices_generate_actualG0 L T L₁ L₂ X
  · rw [hch₀]
    exact source_intrinsic_core_free_of_residual_normalizer L T L₁ L₂ X M
      hunique hLM hres hnorm hPM hproper T.isPGroup'

/-- The conditional final assembly from the actual source parabolics and the
earlier I.5.1 implication. Its order hypothesis includes both d = 8 and d = 12.
The local model and parabolic premises still have to be constructed in the
14.4.6--12 branches before this proves the source elimination. -/
theorem source_large_dimension_contradiction [Finite G]
    (L L₁ L₂ X M : Subgroup G) (T : Sylow 2 G)
    (hq₁ : Nonempty (coreQuotient (L ⊔ (T : Subgroup G)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)))
    (hq₂ : Nonempty (coreQuotient (L₁ ⊔ X ⊔ (T : Subgroup G)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hq₃ : Nonempty (coreQuotient (localJoin L₂ X ⊔ (T : Subgroup G)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)))
    (hp₁ : Quasithin.I5.RankTwoParabolics (L ⊔ (T : Subgroup G) : Subgroup G)
      ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G)))
      ((L₁ ⊔ X ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G)))
      ((localJoin L₂ X ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))))
    (hp₂ : Quasithin.I5.RankTwoParabolics (L₁ ⊔ X ⊔ (T : Subgroup G) : Subgroup G)
      ((T : Subgroup G).subgroupOf (L₁ ⊔ X ⊔ (T : Subgroup G)))
      ((L ⊔ (T : Subgroup G)).subgroupOf (L₁ ⊔ X ⊔ (T : Subgroup G)))
      ((localJoin L₂ X ⊔ (T : Subgroup G)).subgroupOf (L₁ ⊔ X ⊔ (T : Subgroup G))))
    (hp₃ : Quasithin.I5.RankTwoParabolics (localJoin L₂ X ⊔ (T : Subgroup G) : Subgroup G)
      ((T : Subgroup G).subgroupOf (localJoin L₂ X ⊔ (T : Subgroup G)))
      ((L ⊔ (T : Subgroup G)).subgroupOf (localJoin L₂ X ⊔ (T : Subgroup G)))
      ((L₁ ⊔ X ⊔ (T : Subgroup G)).subgroupOf (localJoin L₂ X ⊔ (T : Subgroup G))))
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → L ⊔ (T : Subgroup G) ≤ K → K = M)
    (hLM : M ≤ normalizer (L : Set G))
    (hres : twoResidual (L ⊓ (localJoin L₂ X ⊔ (T : Subgroup G))) = L₂)
    (hnorm : (localJoin L₂ X ⊔ (T : Subgroup G)) ⊓ normalizer (L₂ : Set G) ≤
      L₂ ⊔ (T : Subgroup G))
    (hPM : L₂ ⊔ (T : Subgroup G) ≤ M)
    (hproper : IsCoatom ((L₂ ⊔ (T : Subgroup G)).subgroupOf
      (localJoin L₂ X ⊔ (T : Subgroup G))))
    (U : Subgroup G) (hUT : U ≤ (T : Subgroup G))
    (d : ℕ) (hd : d = 8 ∨ d = 12) (hcard : Nat.card U = 2 ^ (d + 1))
    (recognition : ∀ (K : Type u) [Group K] [Finite K],
      Quasithin.I5.DSystem .A3 K →
        Nonempty (K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2))) :
    False := by
  obtain ⟨e⟩ := recognition (actualG0 L T L₁ L₂ X)
    (source_dSystem L L₁ L₂ X M T hq₁ hq₂ hq₃ hp₁ hp₂ hp₃
      hunique hLM hres hnorm hPM hproper)
  exact source_order_contradiction L T L₁ L₂ X U T.isPGroup' hUT
    (source_large_card d (Nat.card U) hd hcard) e

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.IntrinsicSource
