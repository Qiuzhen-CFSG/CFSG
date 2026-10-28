module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow

/-!
# Escape from M and the local H₁ choice

The preceding TI assertion makes M ∩ N_G(V₁) normalize V: the nontrivial
point survives in every intersection. Consequently, if the point centralizer
were contained in M, 11.2.3(2) and the permitted 11.5.3(3) implication would
contradict one another when K=L₁. The strict case uses the preceding component
escape. The actual point normalizer then witnesses the nonempty collection
H(L₁T,M) ∩ G₁. This is the H₁ choice, not the further minimal-parabolic H choice.
Source: Aschbacher--Smith 11.5.4 and the following paragraph, printed p.780.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The original TI statement gives normalization on the actual intersection M₁. -/
theorem M₁_normalizes_seed (hp : E.point ≠ ⊥)
    (hTI : ∀ g ∈ E.M,
      V ⊓ V.map (MulAut.conj g : G →* G) = ⊥ ∨ V.map (MulAut.conj g : G →* G) = V) :
    E.M₁ ≤ normalizer (V : Set G) := by
  intro g hg
  have he : E.V₁.map (MulAut.conj g : G →* G) = E.V₁ :=
    mem_normalizer_iff_map_conj_eq.mp hg.2
  have hi : E.V₁ ≤ V ⊓ V.map (MulAut.conj g : G →* G) := by
    refine le_inf E.V₁_le ?_
    rw [← he]
    exact map_mono E.V₁_le
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply (hTI g hg.1).resolve_left
  intro hz
  exact D.centralQuotientPreimage_ne_bot E.point hp (bot_unique (hz ▸ hi))

/-- The centralizer escape in 11.5.4. The only later premise is the
independent 11.5.3(3) implication, whose producer is the nonabelian branch. -/
theorem point_centralizer_not_le_M (hp : E.point ≠ ⊥)
    (hTI : ∀ g ∈ E.M,
      V ⊓ V.map (MulAut.conj g : G →* G) = ⊥ ∨ V.map (MulAut.conj g : G →* G) = V)
    (hcontrol : centralizer (E.V₁ : Set G) ≤ E.M → E.G₁ ≤ E.M)
    (hKC : E.K ≤ centralizer (E.V₁ : Set G))
    (hescape : E.L₁ < E.K → ¬ E.K ≤ E.M)
    (hnonabelian : E.K = E.L₁ → ¬ IsMulCommutative E.W) :
    ¬ centralizer (E.V₁ : Set G) ≤ E.M := by
  intro hc
  by_cases he : E.K = E.L₁
  · have hn : E.G₁ ≤ normalizer (V : Set G) :=
      (le_inf (hcontrol hc) le_rfl).trans (E.M₁_normalizes_seed hp hTI)
    have hW : E.W = V :=
      le_antisymm (conjugateSpanBy_le le_rfl hn) (le_conjugateSpanBy V E.G₁)
    apply hnonabelian he
    rw [hW]
    let := D.elementary
    infer_instance
  · exact hescape (lt_of_le_of_ne (le_conjugateSpanBy E.L₁ E.G₁)
      (Ne.symm he)) (hKC.trans hc)

/-- Any point-normalizing overgroup of T has nontrivial two-core. -/
theorem point_overgroup_mem_H (hp : E.point ≠ ⊥) (H₁ : Subgroup G)
    (hT : (T : Subgroup G) ≤ H₁) (hH : H₁ ≤ E.G₁) : H₁ ∈ Chapter1.H G := by
  have hv : E.V₁ ≤ H₁.pCoreIn 2 := le_pCoreIn_of_normalizes
    (@IsElementaryAbelian.isPGroup 2 _ _ (D.centralQuotientPreimage_elementary E.point))
    (E.V₁_le.trans (D.le_sylow.trans hT)) hH
  intro hz
  exact D.centralQuotientPreimage_ne_bot E.point hp (bot_unique (hz ▸ hv))

/-- The collection H(L₁T,M) ∩ G₁ is nonempty, on the same chosen flag. -/
theorem exists_local_overgroup (hp : E.point ≠ ⊥)
    (hT : (T : Subgroup G) ≤ E.G₁)
    (hc : ¬ centralizer (E.V₁ : Set G) ≤ E.M) :
    ∃ H₁ : Subgroup G,
      H₁ ∈ Chapter1.HOutside G ((E.L₁ ⊔ (T : Subgroup G) : Subgroup G) : Set G)
        (E.M : Set G) ∧ H₁ ≤ E.G₁ := by
  refine ⟨E.G₁, ⟨⟨E.point_overgroup_mem_H hp E.G₁ hT le_rfl, ?_⟩, ?_⟩, le_rfl⟩
  · exact sup_le ((residualIn_le _).trans inf_le_right) hT
  · intro h
    exact hc ((centralizer_le_normalizer _).trans h)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
