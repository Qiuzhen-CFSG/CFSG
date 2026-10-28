module

public import Theory.SpecificGroups.PSL3.UniversalProjection.Faithfulness.Bruhat.Setup

/-!
# Positive-root collection in the degree-three Steinberg presentation

Every positive word collects to `x₁₂(b) x₀₂(c) x₀₁(a)`. The chain relation
exchanges `x₀₁(a)` and `x₁₂(b)`, adding the central factor `x₀₂(ab)`.
In this descending-row order the three matrix entries recover the three
parameters directly, proving faithfulness on the literal upper subgroup.
Removing either simple root also gives the complement factorization needed
by Bruhat word induction.

Source: Steinberg, *Lectures on Chevalley Groups*, §6, Lemma 36, printed
p.69; GLS3 §2.9, printed pp.97–98. No global faithfulness is used.
-/

@[expose] public section

open Theory.SpecificGroups.LinearHigher SteinbergWords
namespace Matrix.PSL3.UniversalProjection.Faithfulness
variable {F : Type*} [Field F]
namespace PositiveCollection
abbrev x01 (a : F) := generator (root (0 : Fin 3) 1 (by decide)) a
abbrev x02 (a : F) := generator (root (0 : Fin 3) 2 (by decide)) a
abbrev x12 (a : F) := generator (root (1 : Fin 3) 2 (by decide)) a

private theorem commute_01_02 (a b : F) : Commute (x01 a) (x02 b) :=
  generator_relations.commute _ _ _ _ (by decide) (by decide)
private theorem commute_12_02 (a b : F) : Commute (x12 a) (x02 b) :=
  generator_relations.commute _ _ _ _ (by decide) (by decide)
private theorem exchange (a b : F) : x01 a * x12 b = x12 b * x02 (a * b) * x01 a := by
  have h := generator_relations.conj_chain (0 : Fin 3) 1 2
    (by decide) (by decide) (by decide) a b
  rw [(commute_12_02 b (a * b)).eq.symm] at h
  exact mul_inv_eq_iff_eq_mul.mp h

def normal (a b c : F) : SteinbergGroup 3 F := x12 b * x02 c * x01 a

private theorem normal_zero : normal (0 : F) 0 0 = 1 := by
  simp [normal, x01, x02, x12, generator_relations.zero]

private theorem normal_mul_01 (a b c d : F) : normal a b c * x01 d = normal (a+d) b c := by
  simp only [normal, mul_assoc, x01, generator_relations.add]

private theorem normal_mul_02 (a b c d : F) : normal a b c * x02 d = normal a b (c+d) := by
  simp only [normal, mul_assoc]
  rw [(commute_01_02 a d).eq, ← mul_assoc (x02 c), generator_relations.add]

private theorem normal_mul_12 (a b c d : F) :
    normal a b c * x12 d = normal a (b+d) (c+a*d) := by
  simp only [normal, mul_assoc]
  rw [exchange, ← mul_assoc (x02 c), ← mul_assoc (x02 c),
    (commute_12_02 d c).eq.symm]
  simp only [mul_assoc]
  rw [← mul_assoc (x12 b), generator_relations.add,
    ← mul_assoc (x02 c), generator_relations.add]

theorem exists_normal {g : SteinbergGroup 3 F} (hg : g ∈ upperSubgroup F) :
    ∃ a b c : F, g = normal a b c := by
  have step (g : SteinbergGroup 3 F) (ih : ∃ a b c : F, g = normal a b c)
      (r : Root 3) (hr : r.val.1 < r.val.2) (d : F) :
      ∃ a b c : F, g * generator r d = normal a b c := by
    obtain ⟨a,b,c,rfl⟩ := ih
    obtain ⟨⟨i,j⟩,hij⟩ := r
    fin_cases i <;> fin_cases j <;> first
    | exact (by contradiction)
    | exact ⟨a+d,b,c,normal_mul_01 a b c d⟩
    | exact ⟨a,b,c+d,normal_mul_02 a b c d⟩
    | exact ⟨a,b+d,c+a*d,normal_mul_12 a b c d⟩
  induction hg using Subgroup.closure_induction_right with
  | one => exact ⟨0,0,0,normal_zero.symm⟩
  | mul_right g _ y hy ih =>
    obtain ⟨r,a,hr,rfl⟩ := hy
    exact step g ih r hr a
  | mul_inv_cancel g _ y hy ih =>
    obtain ⟨r,a,hr,rfl⟩ := hy
    rw [← generator_relations.neg]
    exact step g ih r hr (-a)

theorem matrix_normal (a b c : F) :
    (matrixMap (normal a b c) : Matrix (Fin 3) (Fin 3) F) =
      !![1,a,c; 0,1,b; 0,0,1] := by
  simp only [normal, x01, x02, x12, map_mul, matrixMap_generator,
    Matrix.SpecialLinearGroup.coe_mul, matrixRoot,
    Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [root, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.single, Matrix.one_apply]

abbrev simpleRoot (k : Fin 2) : Root 3 := root k.castSucc k.succ (by
  intro he
  have := congrArg Fin.val he
  simp only [Fin.val_castSucc, Fin.val_succ] at this
  omega)

def complement (k : Fin 2) : Subgroup (SteinbergGroup 3 F) :=
  Subgroup.closure {g | ∃ (r : Root 3) (a : F),
    r.val.1 < r.val.2 ∧ r ≠ simpleRoot k ∧ g = generator r a}

theorem complement_le (k : Fin 2) : complement (F := F) k ≤ upperSubgroup F := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨r,a,hr,_,rfl⟩
  exact generator_mem_upper hr a

theorem complement_generator (k : Fin 2) (r : Root 3)
    (hr : r.val.1 < r.val.2) (hne : r ≠ simpleRoot k) (a : F) :
    generator r a ∈ complement (F := F) k :=
  Subgroup.subset_closure ⟨r,a,hr,hne,rfl⟩

theorem factor_simple (k : Fin 2) {g : SteinbergGroup 3 F}
    (hg : g ∈ upperSubgroup F) :
    ∃ (a : F) (c : complement (F := F) k), g = generator (simpleRoot k) a * c.val := by
  obtain ⟨a,b,c,rfl⟩ := exists_normal hg
  fin_cases k
  · refine ⟨a, ⟨x12 b * x02 (c-a*b), ?_⟩, ?_⟩
    · exact (complement 0).mul_mem
        (complement_generator 0 _ (by decide) (by decide) b)
        (complement_generator 0 _ (by decide) (by decide) (c-a*b))
    · change normal a b c = x01 a * (x12 b * x02 (c-a*b))
      rw [← mul_assoc, exchange]
      simp only [mul_assoc]
      rw [(commute_01_02 a (c-a*b)).eq,
        ← mul_assoc (x02 (a*b)), generator_relations.add]
      have he : a*b + (c-a*b) = c := by ring
      rw [he]
      exact mul_assoc _ _ _
  · refine ⟨b, ⟨x02 c * x01 a, ?_⟩, ?_⟩
    · exact (complement 1).mul_mem
        (complement_generator 1 _ (by decide) (by decide) c)
        (complement_generator 1 _ (by decide) (by decide) a)
    · exact mul_assoc _ _ _

end PositiveCollection

/-- The matrix map is injective on the literal positive-root subgroup. -/
theorem upperFaithful : UpperFaithful F := by
  intro g h he
  obtain ⟨a,b,c,hg⟩ := PositiveCollection.exists_normal g.property
  obtain ⟨d,e,f,hh⟩ := PositiveCollection.exists_normal h.property
  change matrixMap g.val = matrixMap h.val at he
  rw [hg, hh] at he
  have hm := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 3) F => (z : Matrix (Fin 3) (Fin 3) F)) he
  rw [PositiveCollection.matrix_normal, PositiveCollection.matrix_normal] at hm
  have ha := congrArg (fun z : Matrix (Fin 3) (Fin 3) F => z 0 1) hm
  have hb := congrArg (fun z : Matrix (Fin 3) (Fin 3) F => z 1 2) hm
  have hc := congrArg (fun z : Matrix (Fin 3) (Fin 3) F => z 0 2) hm
  change a = d at ha
  change b = e at hb
  change c = f at hc
  apply Subtype.ext
  rw [hg, hh, ha, hb, hc]
end Matrix.PSL3.UniversalProjection.Faithfulness
