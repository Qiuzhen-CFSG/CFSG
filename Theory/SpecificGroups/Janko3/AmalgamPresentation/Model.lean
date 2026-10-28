module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Core
public import Theory.SpecificGroups.Janko3.Model.Order
import Mathlib.Tactic.FinCases

/-!
# The literal amalgam generators in the ATLAS J₃ model

The six marked generators are products of the existing certified stabilizer-chain
transversals. They represent exactly the six saved permutations used for the
22 relations in `AmalgamPresentation.Core`. The original ATLAS generators are
recovered by explicit signed words. All identities use the already certified
three-point base: only points 0, 1, 2 are checked by kernel reduction.
No finiteness or order bound on the universal presentation follows from this map.

Source data: `Scratch/J3AmalgamComparison/Algebra/model-groups.g` and its frozen
local/overlap words; chain coordinates and independent untrusted discovery are
retained in `Scratch/J3ModelCoordinates/`. Permutation multiplication uses the
same inverse-of-GAP action convention as the existing ATLAS model.
-/

@[expose] public section
namespace Sporadic.Janko3.AmalgamPresentation.ModelCoordinates
open OrderCertificate Theory.GroupTheory Subgroup.CosetWordCertificate
set_option Elab.async false

def chainElement (r : Fin 6156) (s : Fin 510) (t : Fin 16) : Model :=
  ⟨L0Rep r * (L1Rep s * L2Rep t), by
    change L0Rep r * (L1Rep s * L2Rep t) ∈ modelSubgroup
    rw [← H0_eq_modelSubgroup]
    exact H0.mul_mem (L0Rep_mem r)
      (H0.mul_mem (H1_le (L1Rep_mem s)) (H1_le (H2_le (L2Rep_mem t))))⟩

def modelGenerator : Fin 6 → Model
  | 0 => chainElement 0 348 1
  | 1 => chainElement 0 70 0
  | 2 => chainElement 1796 92 6
  | 3 => chainElement 1863 452 2
  | 4 => chainElement 5489 314 10
  | _ => chainElement 1197 319 15

private def fastChain (r : Fin 6156) (s : Fin 510) (t : Fin 16) : Equiv.Perm (Fin 6156) :=
  evalWord fastL0Gen (L0RepWord r) * (L1Rep s * L2Rep t)

private def fastGenerator : Fin 6 → Equiv.Perm (Fin 6156)
  | 0 => fastChain 0 348 1
  | 1 => fastChain 0 70 0
  | 2 => fastChain 1796 92 6
  | 3 => fastChain 1863 452 2
  | 4 => fastChain 5489 314 10
  | _ => fastChain 1197 319 15

private theorem fastChain_eq (r : Fin 6156) (s : Fin 510) (t : Fin 16) :
    embedding (chainElement r s t) = fastChain r s t := by
  change L0Rep r * (L1Rep s * L2Rep t) =
    evalWord fastL0Gen (L0RepWord r) * (L1Rep s * L2Rep t)
  rw [fastL0Gen_eq]
  rfl

private theorem fastGenerator_eq (i : Fin 6) :
    embedding (modelGenerator i) = fastGenerator i := by
  fin_cases i <;> exact fastChain_eq _ _ _

private theorem embedding_eval (w : Word (Fin 6)) :
    embedding (eval modelGenerator w) = eval fastGenerator w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [eval_cons, eval_cons, map_mul, ih]
    congr 1
    cases a with
    | mk i b => cases b <;> simp only [Bool.false_eq_true, ↓reduceIte,
        map_inv, fastGenerator_eq]

private theorem relators_fix_0 :
    ∀ i : Fin 22, eval fastGenerator (relatorWord i) (0 : Fin 6156) = 0 := by
  apply allFin
  decide +kernel

private theorem relators_fix_1 :
    ∀ i : Fin 22, eval fastGenerator (relatorWord i) (1 : Fin 6156) = 1 := by
  apply allFin
  decide +kernel

private theorem relators_fix_2 :
    ∀ i : Fin 22, eval fastGenerator (relatorWord i) (2 : Fin 6156) = 2 := by
  apply allFin
  decide +kernel

/-- Every literal local and overlap relation holds in the actual ATLAS model. -/
theorem modelGenerator_satisfies : Satisfies modelGenerator := by
  intro i
  apply model_base_trivial
  · change embedding (eval modelGenerator (relatorWord i)) 0 = 0
    rw [embedding_eval]
    exact relators_fix_0 i
  · change embedding (eval modelGenerator (relatorWord i)) 1 = 1
    rw [embedding_eval]
    exact relators_fix_1 i
  · change embedding (eval modelGenerator (relatorWord i)) 2 = 2
    rw [embedding_eval]
    exact relators_fix_2 i

private theorem model_eq_of_base (x y : Model)
    (h0 : embedding x 0 = embedding y 0)
    (h1 : embedding x 1 = embedding y 1)
    (h2 : embedding x 2 = embedding y 2) : x = y := by
  apply inv_mul_eq_one.mp
  apply model_base_trivial
  · change embedding x⁻¹ (embedding y 0) = 0
    rw [← h0]
    exact (embedding x).symm_apply_apply 0
  · change embedding x⁻¹ (embedding y 1) = 1
    rw [← h1]
    exact (embedding x).symm_apply_apply 1
  · change embedding x⁻¹ (embedding y 2) = 2
    rw [← h2]
    exact (embedding x).symm_apply_apply 2

private def atlasAWord : Word (Fin 6) := [(4, false), (0, false), (3, false), (2, true), (1, true), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true)]

private theorem atlasAWord_eq : eval modelGenerator atlasAWord = a := by
  apply model_eq_of_base
  all_goals
    rw [embedding_eval]
    change eval fastGenerator atlasAWord _ = atlasA _
    rw [← fastA_eq_atlas]
    decide +kernel

private def atlasBWord : Word (Fin 6) := [(5, true), (5, true), (1, true), (3, false), (2, true), (1, true), (0, false), (0, false), (1, false), (0, false), (0, false), (1, true), (0, false), (1, true), (1, true), (0, true)]

private theorem atlasBWord_eq : eval modelGenerator atlasBWord = b := by
  apply model_eq_of_base
  all_goals
    rw [embedding_eval]
    change eval fastGenerator atlasBWord _ = atlasB _
    rw [← fastB_eq_atlas]
    decide +kernel

private theorem eval_mem_closure (w : Word (Fin 6)) :
    eval modelGenerator w ∈ Subgroup.closure (Set.range modelGenerator) := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [eval_cons]
    apply Subgroup.mul_mem _ _ ih
    split
    · exact Subgroup.subset_closure ⟨a.1, rfl⟩
    · exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨a.1, rfl⟩)

/-- The frozen six-generator marking generates the actual model: the two original
ATLAS generators are explicit words of lengths twelve and sixteen. -/
theorem modelGenerator_generates : Subgroup.closure (Set.range modelGenerator) = ⊤ := by
  apply top_unique
  rw [← generators_closure, Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | hx
  · rw [← atlasAWord_eq]
    exact eval_mem_closure _
  · have he : x = b := hx
    subst x
    rw [← atlasBWord_eq]
    exact eval_mem_closure _

/-- The literal amalgam presentation maps onto the independently constructed model. -/
def modelEvaluation : Carrier →* Model := evaluation modelGenerator_satisfies

theorem modelEvaluation_surjective : Function.Surjective modelEvaluation :=
  evaluation_surjective modelGenerator_satisfies modelGenerator_generates

end Sporadic.Janko3.AmalgamPresentation.ModelCoordinates
