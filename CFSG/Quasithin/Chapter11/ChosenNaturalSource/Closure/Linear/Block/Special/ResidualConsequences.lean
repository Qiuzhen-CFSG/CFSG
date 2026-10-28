module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special.Rank
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special.ResidualAction

/-!
# From the natural residual action to the full closure center

If the original solvable residual contains V and fixes precisely V₁
on V, its fixed subgroup on U is Z(U). Normality of the center under
G₁ propagates this fixation to K, the original G₁-closure of L₁.
The final source applications discharge both natural residual premises
using the original marked point-parabolic action.
Source: Aschbacher--Smith 11.5.7, refs/quasithin.pdf, printed p.782.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterG.Section02.LinearThree
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D) {x y : G}
  (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)
include d

/-- The natural residual fixed-space calculation gives the full fixed subgroup
of the original closure, using V≤L₁ to enter the collapsed core. -/
theorem closure_residual_fixed
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y)
    (hVL : V ≤ E.L₁)
    (hfixed : V ⊓ centralizer (E.L₁ : Set G) = E.V₁) :
    E.W ⊓ centralizer (E.L₁ : Set G) = closureCenter E := by
  let C := E.W ⊓ centralizer (L : Set G)
  have hCL : C ≤ centralizer (E.L₁ : Set G) := inf_le_right.trans (centralizer_le E.L₁_le)
  rw [closureCenter_eq E d hUT hf hc]
  apply le_antisymm
  · intro z hz
    have hzS : z ∈ threeCore E x y := by
      apply (threeGroup_chosen_centralizer E d hUT hf).le
      exact ⟨(threeGroup_eq_join d hUT hf).ge (mem_sup_right hz.1), centralizer_le hVL hz.2⟩
    have hS : threeCore E x y = V ⊔ C := by
      rw [threeCore_split E d hUT hf hc, threeCore_centralizer E d hUT hf hc]
    have hzprod : z ∈ (V : Set G) * (C : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left V C
        ((inf_le_right.trans (centralizer_le D.le_component)).trans (centralizer_le_normalizer _)),
        ← hS]
      exact hzS
    obtain ⟨v,hv,c,hcC,he⟩ := hzprod
    have hvfix : v ∈ centralizer (E.L₁ : Set G) := by
      have hh := (centralizer (E.L₁ : Set G)).mul_mem hz.2
        ((centralizer (E.L₁ : Set G)).inv_mem (hCL hcC))
      simpa only [← he, mul_inv_cancel_right] using hh
    rw [← he]
    exact mul_mem_sup (hfixed.le ⟨hv,hvfix⟩) hcC
  · exact sup_le
      (le_inf (E.V₁_le.trans (le_conjugateSpanBy V E.G₁)) (hfixed.ge.trans inf_le_right))
      (le_inf inf_le_left hCL)

omit d in
theorem closureCenter_normalized : E.G₁ ≤ normalizer (closureCenter E : Set G) :=
  (le_normalizer_conjugateSpanBy V E.G₁).trans
    (normalizer_le_normalizer_characteristic_image E.W (center E.W))

/-- Propagate the original residual's center fixation through its G₁-closure. -/
theorem K_centralizes_center
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y)
    (hVL : V ≤ E.L₁)
    (hfixed : V ⊓ centralizer (E.L₁ : Set G) = E.V₁) :
    E.K ≤ centralizer (closureCenter E : Set G) := by
  apply conjugateSpanBy_le
  · apply le_centralizer_iff.mp
    exact (closure_residual_fixed E d hUT hf hc hVL hfixed).ge.trans inf_le_right
  · exact (closureCenter_normalized E).trans (normalizer_le_normalizer_centralizer _)

/-- The original residual fixes precisely the center of U; the natural
residual action premises are discharged. -/
theorem source_closure_residual_fixed
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y) :
    E.W ⊓ centralizer (E.L₁ : Set G) = closureCenter E :=
  closure_residual_fixed E d hUT hf hc (chosen_le_residual E d) (chosen_residual_fixed E d)

/-- The original conjugate-span K centralizes the full closure center. -/
theorem source_K_centralizes_center
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y) :
    E.K ≤ centralizer (closureCenter E : Set G) :=
  K_centralizes_center E d hUT hf hc (chosen_le_residual E d) (chosen_residual_fixed E d)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special
