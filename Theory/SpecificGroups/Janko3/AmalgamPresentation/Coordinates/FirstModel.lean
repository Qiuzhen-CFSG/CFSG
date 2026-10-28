module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Model
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.LocalBound.Presentation
import Mathlib.Tactic.FinCases

/-!
# The literal first local subgroup of the marked ATLAS model

The first pair fixes the first point. Conversely, words of lengths five and
ten recover the two certified generators of its full stabilizer. Thus the
literal generated subgroup has order 8160, with no local recognition input.
The words were found by untrusted search and are checked at the certified
three-point base of the actual model.
-/

@[expose] public section
set_option Elab.async false
namespace Sporadic.Janko3.AmalgamPresentation.ModelCoordinates
open Subgroup Subgroup.CosetWordCertificate OrderCertificate Theory.GroupTheory

def firstLocalModel : Subgroup Model := closure ({modelGenerator 0,modelGenerator 1} : Set Model)
private def pairGenerator (b : Bool) : Model := if b then modelGenerator 1 else modelGenerator 0
private def pairPermutation (b : Bool) : Equiv.Perm (Fin 6156) := embedding (pairGenerator b)
private def stabilizerGenerator (i : Fin 4) : Model :=
  ⟨L1Gen i, by
    change L1Gen i ∈ modelSubgroup
    rw [←H0_eq_modelSubgroup]
    apply H1_le
    exact ⟨[i],by simp [evalWord]⟩⟩

private theorem equal_of_base (x y : Model)
    (h0 : embedding x 0 = embedding y 0)
    (h1 : embedding x 1 = embedding y 1)
    (h2 : embedding x 2 = embedding y 2) : x = y := by
  apply inv_mul_eq_one.mp
  apply model_base_trivial
  · change embedding x⁻¹ (embedding y 0) = 0
    rw [←h0]
    exact (embedding x).symm_apply_apply 0
  · change embedding x⁻¹ (embedding y 1) = 1
    rw [←h1]
    exact (embedding x).symm_apply_apply 1
  · change embedding x⁻¹ (embedding y 2) = 2
    rw [←h2]
    exact (embedding x).symm_apply_apply 2

private theorem embedding_pair_word (w : Word Bool) :
    embedding (eval pairGenerator w) = eval pairPermutation w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [eval_cons,eval_cons,map_mul,ih]
    congr 1
    cases a with
    | mk i b => cases b <;> simp only [Bool.false_eq_true,↓reduceIte,map_inv]
      <;> rfl

private def firstStabilizerWord : Word Bool :=
  [(true,true),(false,false),(true,false),(true,false),(false,true)]
private def secondStabilizerWord : Word Bool :=
  [(false,false),(false,false),(true,true),(false,true),(true,false),
   (true,false),(false,false),(true,true),(false,true),(false,true)]

private theorem firstStabilizerWord_eq :
    eval pairGenerator firstStabilizerWord = stabilizerGenerator 0 := by
  apply equal_of_base
  all_goals
    rw [embedding_pair_word]
    change eval pairPermutation firstStabilizerWord _ = L1Gen 0 _
    decide +kernel

private theorem secondStabilizerWord_eq :
    eval pairGenerator secondStabilizerWord = stabilizerGenerator 1 := by
  apply equal_of_base
  all_goals
    rw [embedding_pair_word]
    change eval pairPermutation secondStabilizerWord _ = L1Gen 1 _
    decide +kernel

private theorem pair_word_mem (w : Word Bool) : eval pairGenerator w ∈ firstLocalModel := by
  have hg (b : Bool) : pairGenerator b ∈ firstLocalModel := by
    cases b <;> apply subset_closure <;> simp [pairGenerator]
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [eval_cons]
    apply firstLocalModel.mul_mem _ ih
    split
    · exact hg a.1
    · exact firstLocalModel.inv_mem (hg a.1)

/-- Equality with the already certified full first-point stabilizer in the
faithful permutation realization. -/
theorem firstLocalModel_image : firstLocalModel.map embedding = H1 := by
  apply le_antisymm
  · rw [firstLocalModel,MonoidHom.map_closure]
    apply (closure_le _).mpr
    rintro _ ⟨g,hg,rfl⟩
    rcases hg with rfl | hg
    · change L0Rep 0 * (L1Rep 348 * L2Rep 1) ∈ H1
      rw [L0Rep_base,one_mul]
      exact H1.mul_mem (L1Rep_mem _) (H2_le (L2Rep_mem _))
    · have he : g = modelGenerator 1 := hg
      subst g
      change L0Rep 0 * (L1Rep 70 * L2Rep 0) ∈ H1
      rw [L0Rep_base,one_mul]
      exact H1.mul_mem (L1Rep_mem _) (H2_le (L2Rep_mem _))
  · have h0 : L1Gen 0 ∈ firstLocalModel.map embedding := by
      exact mem_map_of_mem embedding (firstStabilizerWord_eq ▸ pair_word_mem _)
    have h1 : L1Gen 1 ∈ firstLocalModel.map embedding := by
      exact mem_map_of_mem embedding (secondStabilizerWord_eq ▸ pair_word_mem _)
    have hg (i : Fin 4) : L1Gen i ∈ firstLocalModel.map embedding := by
      fin_cases i
      · exact h0
      · exact h1
      · exact (firstLocalModel.map embedding).inv_mem h0
      · exact (firstLocalModel.map embedding).inv_mem h1
    rintro x ⟨w,rfl⟩
    induction w with
    | nil => exact (firstLocalModel.map embedding).one_mem
    | cons i w ih => exact (firstLocalModel.map embedding).mul_mem (hg i) ih

theorem firstLocalModel_card : Nat.card firstLocalModel = 8160 := by
  rw [←card_map_of_injective embedding_injective,firstLocalModel_image,H1_card]

end Sporadic.Janko3.AmalgamPresentation.ModelCoordinates
