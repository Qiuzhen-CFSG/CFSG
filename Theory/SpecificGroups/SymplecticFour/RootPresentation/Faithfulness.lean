module
public import Theory.SpecificGroups.SymplecticFour.RootPresentation.WeylCollection
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

/-!
# Faithfulness of the finite characteristic-two C₂ presentation

Every Weyl word is a two-coroot torus element times one of eight fixed
representatives. Each nonidentity representative has a zero diagonal entry;
torus multiplication preserves that zero, whereas every positive unipotent
matrix has diagonal entries one. The remaining diagonal torus matrix is
therefore the identity, and the already proved torus faithfulness kills it.
Bruhat coverage and positive faithfulness now kill the entire matrix kernel.
The resulting equivalence is with the whole Sp₄, including fields two and four.

Source: Steinberg, Lectures on Chevalley Groups, §6, Theorems 8–9,
printed pp.68–74, in the project's literal eight-root matrix convention.
-/

@[expose] public noncomputable section
open Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.RootPresentation
open PositiveRelations
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private def shortMatrix (t : Fˣ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks !![0,t; (t⁻¹ : Fˣ),0] 0 0 !![0,(t⁻¹ : Fˣ); t,0]

private def longMatrix (t : Fˣ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks !![1,0;0,0] !![0,0;0,t] !![0,0;0,(t⁻¹ : Fˣ)] !![1,0;0,0]

omit [Finite F] in
private theorem matrix_shortWord (t : Fˣ) :
    (matrixMap (simpleWord generator 0 t)).val = shortMatrix t := by
  change (matrixMap (generator 6 (t : F) * generator (F := F) 7 ((t⁻¹ : Fˣ) : F) * generator 6 (t : F))).val = _
  simp only [map_mul,matrixMap_generator]
  change rootMatrix 6 (t : F) * rootMatrix 7 ((t⁻¹ : Fˣ) : F) * rootMatrix 6 (t : F) = _
  ext i j
  rcases i with i|i <;> rcases j with j|j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix,shortMatrix,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,
      Matrix.single,Matrix.fromBlocks,CharTwo.neg_eq,CharTwo.add_self_eq_zero]

omit [Finite F] in
private theorem matrix_longWord (t : Fˣ) :
    (matrixMap (simpleWord generator 1 t)).val = longMatrix t := by
  change (matrixMap (generator 2 (t : F) * generator (F := F) 3 ((t⁻¹ : Fˣ) : F) * generator 2 (t : F))).val = _
  simp only [map_mul,matrixMap_generator]
  change rootMatrix 2 (t : F) * rootMatrix 3 ((t⁻¹ : Fˣ) : F) * rootMatrix 2 (t : F) = _
  ext i j
  rcases i with i|i <;> rcases j with j|j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix,longMatrix,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,
      Matrix.single,Matrix.fromBlocks,CharTwo.add_self_eq_zero]

def torusDiagonal (s t : Fˣ) : Fin 2 ⊕ Fin 2 → F :=
  Sum.elim ![(s : F),(s⁻¹*t : Fˣ)] ![(s⁻¹ : Fˣ),(s*t⁻¹ : Fˣ)]

/-- The literal two-coroot torus evaluates to its independent diagonal entries. -/
theorem matrixMap_torus_diagonal (s t : Fˣ) :
    (matrixMap (generator_relations.torusPairHom (s,t))).val = Matrix.diagonal (torusDiagonal s t) := by
  simp only [Relations.torusPairHom_apply,torusWord,map_mul]
  change (matrixMap (simpleWord generator 0 s)).val * (matrixMap (simpleWord generator 0 1)).val *
    ((matrixMap (simpleWord generator 1 t)).val * (matrixMap (simpleWord generator 1 1)).val) = _
  rw [matrix_shortWord,matrix_shortWord,matrix_longWord,matrix_longWord]
  ext i j
  rcases i with i|i <;> rcases j with j|j <;> fin_cases i <;> fin_cases j <;>
    simp [shortMatrix,longMatrix,torusDiagonal,Matrix.mul_apply,Fintype.sum_sum_type,
      Fin.sum_univ_two,Matrix.fromBlocks,Matrix.diagonal]

omit [Finite F] in
private theorem representative_zero_diagonal {k : Fin 8} (hk : k ≠ 0) :
    ∃ i : Fin 2 ⊕ Fin 2, (matrixMap (weylRepresentative (generator (F := F)) k)).val i i = 0 := by
  fin_cases k
  · exact (hk rfl).elim
  · refine ⟨Sum.inl 0,?_⟩
    simp [weylRepresentative,matrix_shortWord,shortMatrix,Matrix.fromBlocks]
  · refine ⟨Sum.inl 1,?_⟩
    simp [weylRepresentative,matrix_longWord,longMatrix,Matrix.fromBlocks]
  all_goals refine ⟨Sum.inl 0,?_⟩
  all_goals simp [weylRepresentative,matrix_shortWord,matrix_longWord,shortMatrix,longMatrix,Matrix.mul_apply,Fintype.sum_sum_type,
    Fin.sum_univ_two,Matrix.fromBlocks]

private theorem unipotent_diagonal (u : unipotent (F := F)) (i : Fin 2 ⊕ Fin 2) :
    u.val.val i i = 1 := by
  obtain ⟨⟨b,k,w,v⟩,rfl⟩ := CentralRootGeometry.element_surjective u
  rw [CentralRootGeometry.element_matrix]
  rcases i with i|i <;> fin_cases i <;> rfl

/-- A word in the literal Weyl subgroup whose matrix is positive unipotent
is the identity of the abstract presentation. -/
theorem weyl_eq_one_of_matrix_unipotent {w : SteinbergGroup F}
    (hw : w ∈ weylSubgroup generator) (hu : matrixMap w ∈ unipotent (F := F)) : w = 1 := by
  obtain ⟨⟨s,t⟩,k,rfl⟩ := generator_relations.weyl_normal_form hw
  have hm : (matrixMap (generator_relations.torusPairHom (s,t) * weylRepresentative generator k)).val =
      Matrix.diagonal (torusDiagonal s t) * (matrixMap (weylRepresentative generator k)).val := by
    rw [map_mul]
    change (matrixMap (generator_relations.torusPairHom (s,t))).val * _ = _
    rw [matrixMap_torus_diagonal]
  have hk : k = 0 := by
    by_contra hn
    obtain ⟨i,hi⟩ := representative_zero_diagonal (F := F) hn
    have hd := unipotent_diagonal ⟨_,hu⟩ i
    rw [hm,Matrix.diagonal_mul,hi,mul_zero] at hd
    exact zero_ne_one hd
  subst k
  simp only [weylRepresentative,Matrix.cons_val_zero,mul_one] at hu ⊢
  have he : matrixMap (generator_relations.torusPairHom (s,t)) = 1 := by
    apply Subtype.ext
    rw [matrixMap_torus_diagonal]
    have hd (i : Fin 2 ⊕ Fin 2) : torusDiagonal s t i = 1 := by
      have hh := unipotent_diagonal ⟨_,hu⟩ i
      rw [matrixMap_torus_diagonal,Matrix.diagonal_apply_eq] at hh
      exact hh
    ext i j
    simp [Matrix.diagonal,hd,Matrix.one_apply]
  exact matrixMap_injective_on_torus ⟨(s,t),rfl⟩ (one_mem _) (by simpa using he)

/-- Evaluation of the finite characteristic-two C₂ presentation is faithful. -/
theorem matrixMap_injective : Function.Injective (matrixMap (F := F)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro g hg
  have he : matrixMap g = 1 := hg
  have hgen : closure {g : SteinbergGroup F | ∃ r t, generator r t = g} = ⊤ := by
    apply top_unique
    intro y _
    apply PresentedGroup.generated_by _ _ _ y
    rintro ⟨r,t⟩
    exact subset_closure ⟨r,t,rfl⟩
  obtain ⟨u,w,v,hg⟩ := generator_relations.bruhat hgen g
  have hw : matrixMap w.val ∈ unipotent (F := F) := by
    have hew : matrixMap w.val = matrixMap (u.val⁻¹*v.val⁻¹) := by
      rw [hg,map_mul,map_mul] at he
      rw [map_mul,map_inv,map_inv]
      calc
        _ = (matrixMap u.val)⁻¹ * (matrixMap u.val * matrixMap w.val * matrixMap v.val) * (matrixMap v.val)⁻¹ := by group
        _ = _ := by rw [he]; simp
    rw [hew]
    exact matrixMap_positive.le ⟨_,mul_mem (inv_mem u.property) (inv_mem v.property),rfl⟩
  have hw1 := weyl_eq_one_of_matrix_unipotent w.property hw
  have hpos : g ∈ positiveSubgroup generator := by
    rw [hg,hw1,mul_one]
    exact mul_mem u.property v.property
  exact (mem_bot.mpr (matrixMap_injective_on_positive hpos (one_mem _) (by simpa using he)))

/-- The explicit C₂ presentation is the whole Sp₄, including the binary field. -/
def matrixEquiv : SteinbergGroup F ≃* Sp F :=
  MulEquiv.ofBijective matrixMap ⟨matrixMap_injective,matrixMap_surjective⟩

@[simp] theorem matrixEquiv_generator (r : Fin 8) (t : F) :
    matrixEquiv (generator r t) = rootElement r t := matrixMap_generator r t

end Theory.SpecificGroups.SymplecticFour.RootPresentation
