module
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual.Descent
public import Theory.SpecificGroups.PSp4Three.Transvections
public import Mathlib.FieldTheory.Perfect
/-!
# The normalizer of the literal coefficient symplectic subgroup

Conjugating each unit coordinate transvection by an ambient matrix yields a
transvection in its corresponding column direction. An off-diagonal matrix
entry of that transvection is the square of a coordinate of the column.
Consequently a matrix normalizing Sp4(K) has all its entry squares in K.
Finite characteristic-two fields are perfect, so all entries lie in K, and
the matrix itself descends to the literal coefficient copy.

Thus recognizing a normal subgroup as a conjugate of this coefficient copy
also identifies the whole original ambient subgroup. This is the final
normalizer step in Aschbacher--Smith G.4.7 and the conclusion of G.4.1,
printed pp.340--342. It assumes an already recognized matrix copy; it does
not classify an arbitrary transvection subgroup.
-/

public noncomputable section
open Matrix Subgroup
namespace Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
open DiagramAutomorphisms.FieldFixedResidual
variable {F : Type*} [Field F] [CharP F 2]

private theorem form_single_swap (v : Vector F) (i : Fin 2 ⊕ Fin 2) :
    Matrix.PSp4Three.form (Pi.single (Sum.swap i) 1) v=v i := by
  cases i with
  | inl i => simp [Matrix.PSp4Three.form_apply,Pi.single_apply,CharTwo.neg_eq]
  | inr i => simp [Matrix.PSp4Three.form_apply,Pi.single_apply]

private theorem transvection_square_entry (v : Vector F) (i : Fin 2 ⊕ Fin 2) :
    (Matrix.PSp4Three.transvection v 1).val i (Sum.swap i)=(v i)^2 := by
  change LinearMap.toMatrix' (Matrix.PSp4Three.transvectionMap v 1) i (Sum.swap i)=_
  rw [LinearMap.toMatrix'_apply]
  simp only [Matrix.PSp4Three.transvectionMap_apply,one_mul,form_single_swap]
  cases i <;> simp [smul_eq_mul,pow_two]

omit [CharP F 2] in
private theorem inclusion_transvection_single (K : Subfield F) (j : Fin 2 ⊕ Fin 2) :
    coefficientInclusion K (Matrix.PSp4Three.transvection (Pi.single j (1:K)) 1)=
      Matrix.PSp4Three.transvection (Pi.single j (1:F)) 1 := by
  apply Subtype.ext
  ext i k
  fin_cases j <;> fin_cases i <;> fin_cases k <;>
    simp [coefficientInclusion_apply,Matrix.PSp4Three.transvection,
    LinearMap.toMatrix'_apply,Matrix.PSp4Three.transvectionMap_apply,
    Matrix.PSp4Three.form_apply,Pi.single_apply]

omit [CharP F 2] in
theorem mem_coefficient_range_iff (K : Subfield F) (g : Sp F) :
    g ∈ (coefficientInclusion K).range ↔ ∀ i j, g.val i j∈K := by
  constructor
  · rintro ⟨x,rfl⟩ i j
    rw [coefficientInclusion_apply]
    exact (x.val i j).property
  · intro h
    let A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := fun i j => ⟨g.val i j,h i j⟩
    have hA : A.map K.subtype=g.val := by ext i j; rfl
    have hm : A∈Matrix.symplecticGroup (Fin 2) K := by
      apply Matrix.map_injective K.subtype.injective
      change (A * Matrix.J (Fin 2) K * Aᵀ).map K.subtype=(Matrix.J (Fin 2) K).map K.subtype
      simpa only [Matrix.map_mul,Matrix.transpose_map,Matrix.map_J,hA] using
        SymplecticGroup.mem_iff.mp g.property
    refine ⟨⟨A,hm⟩,?_⟩
    apply Subtype.ext
    ext i j
    exact coefficientInclusion_apply K ⟨A,hm⟩ i j

private theorem mem_of_square_mem [Finite F] (K : Subfield F) {a : F} (ha:a^2∈K) : a∈K := by
  obtain ⟨b,hb⟩ := (frobeniusEquiv K 2).surjective ⟨a^2,ha⟩
  have hb' : (b:F)^2=a^2 := congrArg (fun x:K => (x:F)) hb
  have he : (b:F)=a := (frobenius F 2).injective hb'
  exact he ▸ b.property

/-- The coefficient copy is its literal normalizer inside the ambient Sp4. -/
theorem coefficient_range_normalizer [Finite F] (K : Subfield F) :
    normalizer ((coefficientInclusion K).range : Set (Sp F))=(coefficientInclusion K).range := by
  apply le_antisymm
  · intro g hg
    apply (mem_coefficient_range_iff K g).mpr
    intro i j
    apply mem_of_square_mem K
    have ht : Matrix.PSp4Three.transvection (Pi.single j (1:F)) 1∈(coefficientInclusion K).range :=
      ⟨Matrix.PSp4Three.transvection (Pi.single j (1:K)) 1,inclusion_transvection_single K j⟩
    have hc := (Subgroup.mem_normalizer_iff.mp hg _).mp ht
    rw [Matrix.PSp4Three.transvection_conjugate] at hc
    have he := (mem_coefficient_range_iff K _).mp hc i (Sum.swap i)
    rw [transvection_square_entry] at he
    simpa [smul_eq_mulVec,Matrix.mulVec_single] using he
  · exact Subgroup.le_normalizer

/-- Every internal conjugate of the coefficient copy is self-normalizing. -/
theorem conjugate_coefficient_range_normalizer [Finite F] (K : Subfield F) (c : Sp F) :
    normalizer (((coefficientInclusion K).range.map (MulAut.conj c).toMonoidHom) : Set (Sp F))=
      (coefficientInclusion K).range.map (MulAut.conj c).toMonoidHom := by
  rw [←Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj c).bijective,
    coefficient_range_normalizer]

/-- Recognition of a normal subgroup as a coefficient copy identifies its
original ambient subgroup as that same literal copy. -/
theorem eq_coefficient_copy_of_normal_recognized [Finite F]
    (H : Subgroup (Sp F)) (N : Subgroup H) [N.Normal]
    (K : Subfield F) (c : Sp F)
    (he : N.map H.subtype=(coefficientInclusion K).range.map (MulAut.conj c).toMonoidHom) :
    H=(coefficientInclusion K).range.map (MulAut.conj c).toMonoidHom := by
  have hn := N.le_normalizer_map H.subtype
  rw [Subgroup.normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,he,
    conjugate_coefficient_range_normalizer] at hn
  apply le_antisymm hn
  rw [←he]
  rintro x ⟨n,_,rfl⟩
  exact n.property

end Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
