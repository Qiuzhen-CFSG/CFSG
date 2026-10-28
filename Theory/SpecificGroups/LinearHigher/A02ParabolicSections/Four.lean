module

public import Theory.SpecificGroups.HigherLinear.ParabolicGeometry
public import Theory.SpecificGroups.LinearHigher.A02ParabolicSections
public import Theory.SpecificGroups.ProjectiveLinear.RootNormalizerTorus
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Mathlib.GroupTheory.IsPerfect

/-!
# An actual PSL4 section of a proper binary-field root normalizer

The first four coordinates support the literal block SL4 group. It preserves
its four-space and normalizes the elementary radical which fixes that space
and its quotient pointwise. A transvection from the complement proves the
radical nontrivial. The actual PSL group is nonabelian simple and perfect,
so this two-group cannot be normal in the whole group; its normalizer is
therefore a proper two-local subgroup.

The nonzero identity complement makes the block map injective after the
ambient central quotient. In characteristic two SL4 has trivial scalar
center, giving the exact PSL4 embedding into that normalizer. The source
consumer uses this genuine normalizer directly; equality with the entire
four-space stabilizer is unnecessary.
Source: GLS3 §2.6; Aschbacher--Smith A.2.15(2), A.2.18, printed pp.37--40.
-/

public noncomputable section
open Matrix Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.SpecificGroups.LinearHigher.FourBlock
variable {F : Type*} [Field F]

def blockSL (m : ℕ) : SL(4,F) →* SL(4+m,F) where
  toFun g := ⟨reindex finSumFinEquiv finSumFinEquiv
    (fromBlocks g.val 0 0 (1 : Matrix (Fin m) (Fin m) F)), by
      rw [det_reindex_self, det_fromBlocks_zero₂₁, det_one, mul_one]
      exact g.prop⟩
  map_one' := by
    apply Subtype.ext
    change reindex finSumFinEquiv finSumFinEquiv (fromBlocks 1 0 0 1) = 1
    rw [fromBlocks_one]
    exact (reindexAlgEquiv F F finSumFinEquiv).map_one
  map_mul' g h := by
    apply Subtype.ext
    change reindex finSumFinEquiv finSumFinEquiv (fromBlocks (g.val * h.val) 0 0 1) =
      reindex finSumFinEquiv finSumFinEquiv (fromBlocks g.val 0 0 1) *
      reindex finSumFinEquiv finSumFinEquiv (fromBlocks h.val 0 0 1)
    simp only [reindex_apply]
    rw [submatrix_mul_equiv]
    congr 1
    simp [fromBlocks_multiply]

theorem blockSL_injective (m : ℕ) : Function.Injective (blockSL (F:=F) m) := by
  intro g h he
  have hm := (reindex finSumFinEquiv finSumFinEquiv).injective (congrArg Subtype.val he)
  apply Subtype.ext
  exact congrArg (fun M => M.submatrix Sum.inl Sum.inl) hm

def fourSpace (m : ℕ) : Submodule F (Fin (4+m) → F) where
  carrier := {v | ∀ j : Fin m, v (finSumFinEquiv (Sum.inr j)) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy j
    change x (finSumFinEquiv (Sum.inr j)) + y (finSumFinEquiv (Sum.inr j)) = 0
    rw [hx j, hy j, zero_add]
  smul_mem' := by
    intro a x hx j
    change a * x (finSumFinEquiv (Sum.inr j)) = 0
    rw [hx j, mul_zero]

theorem blockSL_tail (m : ℕ) (g : SL(4,F)) (v : Fin (4+m) → F) (j : Fin m) :
    SpecialLinearGroup.toLin' (blockSL m g) v (finSumFinEquiv (Sum.inr j)) =
      v (finSumFinEquiv (Sum.inr j)) := by
  change (∑ k, (reindex finSumFinEquiv finSumFinEquiv
    (fromBlocks g.val 0 0 (1 : Matrix (Fin m) (Fin m) F)))
      (finSumFinEquiv (Sum.inr j)) k * v k) = _
  rw [← Equiv.sum_comp finSumFinEquiv]
  simp [reindex_apply, fromBlocks, Fintype.sum_sum_type, Matrix.one_apply]

theorem blockSL_mem_parabolic (m : ℕ) (g : SL(4,F)) :
    blockSL m g ∈ Matrix.HigherLinear.parabolicSL (fourSpace (F:=F) m) := by
  intro v
  change (∀ j : Fin m, SpecialLinearGroup.toLin' (blockSL m g) v
    (finSumFinEquiv (Sum.inr j)) = 0) ↔ _
  simp only [blockSL_tail]
  rfl

theorem transvection_action {n : ℕ} {i j : Fin n} (hij : i ≠ j) (v : Fin n → F) :
    SpecialLinearGroup.toLin' (SpecialLinearGroup.transvection hij (1 : F)) v =
      v + Pi.single i (v j) := by
  change (1 + Matrix.single i j (1 : F)) *ᵥ v = v + Pi.single i (v j)
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec, one_mul]
  rfl

theorem radical_ne_bot (m : ℕ) (hm : 0 < m) :
    Matrix.HigherLinear.radical (fourSpace (F:=F) m) ≠ ⊥ := by
  let i : Fin (4+m) := finSumFinEquiv (Sum.inl (0 : Fin 4))
  let j : Fin (4+m) := finSumFinEquiv (Sum.inr (⟨0,hm⟩ : Fin m))
  have hij : i ≠ j := by
    intro h
    have hh : (Sum.inl (0 : Fin 4) : Fin 4 ⊕ Fin m) = Sum.inr ⟨0,hm⟩ :=
      finSumFinEquiv.injective h
    cases hh
  let t : SL(4+m,F) := SpecialLinearGroup.transvection hij 1
  have ht : t ∈ Matrix.HigherLinear.radicalSL (fourSpace (F:=F) m) := by
    constructor
    · intro v hv
      change ∀ k : Fin m, v (finSumFinEquiv (Sum.inr k)) = 0 at hv
      rw [show SpecialLinearGroup.toLin' t v = v + Pi.single i (v j) from transvection_action hij v]
      simp only [show v j = 0 from hv ⟨0,hm⟩, Pi.single_zero, add_zero]
    · intro v
      rw [show SpecialLinearGroup.toLin' t v = v + Pi.single i (v j) from transvection_action hij v]
      change ∀ k : Fin m, (v (finSumFinEquiv (Sum.inr k)) +
        (Pi.single i (v j) : Fin (4+m) → F) (finSumFinEquiv (Sum.inr k))) - v (finSumFinEquiv (Sum.inr k)) = 0
      intro k
      have hki : finSumFinEquiv (Sum.inr k) ≠ i := by
        intro h
        have hh : (Sum.inr k : Fin 4 ⊕ Fin m) = Sum.inl 0 := finSumFinEquiv.injective h
        cases hh
      simp only [Pi.single_apply, if_neg hki, add_zero, sub_self]
  have hmemb : Matrix.HigherLinear.projection (4+m) F t ∈
      Matrix.HigherLinear.radical (fourSpace (F:=F) m) := ⟨t,ht,rfl⟩
  intro he
  rw [he, Subgroup.mem_bot] at hmemb
  change QuotientGroup.mk t = 1 at hmemb
  have hc := (QuotientGroup.eq_one_iff t).mp hmemb
  exact one_ne_zero ((Matrix.SpecialLinearGroup.transvection_mem_center_iff hij (1 : F)).mp hc)

variable [CharP F 2]
theorem center_four_eq_bot : center SL(4,F) = ⊥ := by
  apply le_bot_iff.mp
  intro g hg
  obtain ⟨a,ha,hga⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  norm_num only [Fintype.card_fin] at ha
  have hsq : a ^ 2 = 1 := by
    have hh : (a ^ 2) ^ 2 = 1 := by simpa [← pow_mul] using ha
    rcases sq_eq_one_iff.mp hh with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  have ha1 : a = 1 := by
    rcases sq_eq_one_iff.mp hsq with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  apply Subtype.ext
  simpa [ha1] using hga.symm

def fourNormalizer (m : ℕ) : Subgroup PSL(4+m,F) :=
  Subgroup.normalizer (Matrix.HigherLinear.radical (fourSpace (F:=F) m) : Set PSL(4+m,F))

theorem fourNormalizer_twoLocal (m : ℕ) (hm : 0 < m) :
    IsTwoLocal (fourNormalizer (F:=F) m) :=
  ⟨Matrix.HigherLinear.radical (fourSpace (F:=F) m), radical_ne_bot m hm,
    Matrix.HigherLinear.radical_isPGroup _, rfl⟩

theorem fourNormalizer_ne_top [Finite F] (m : ℕ) (hm : 0 < m) :
    fourNormalizer (F:=F) m ≠ ⊤ := by
  let : IsSimpleGroup PSL(4+m,F) := Atlas.psl_simple_high_rank (4+m) (by omega)
  let : Group.IsPerfect SL(4+m,F) := Atlas.sl_perfect (4+m) (by omega)
  intro ht
  have hn : (Matrix.HigherLinear.radical (fourSpace (F:=F) m)).Normal :=
    Subgroup.normalizer_eq_top_iff.mp ht
  rcases hn.eq_bot_or_eq_top with hbot | htop
  · exact radical_ne_bot m hm hbot
  · have hp := Matrix.HigherLinear.radical_isPGroup (F:=F) (fourSpace (F:=F) m)
    rw [htop] at hp
    have hp' : IsPGroup 2 PSL(4+m,F) := hp.of_equiv Subgroup.topEquiv
    let : Group.IsNilpotent PSL(4+m,F) := hp'.isNilpotent
    exact Group.IsPerfect.not_isSolvable PSL(4+m,F) inferInstance

def blockProjective (m : ℕ) : SL(4,F) →* PSL(4+m,F) :=
  (Matrix.HigherLinear.projection (4+m) F).comp (blockSL m)

omit [CharP F 2] in
theorem blockProjective_injective (m : ℕ) (hm : 0 < m) :
    Function.Injective (blockProjective (F:=F) m) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : blockSL m g ∈ center SL(4+m,F) := (QuotientGroup.eq_one_iff _).mp hg
  obtain ⟨a, _, hga⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have haa := congrArg (fun M : Matrix (Fin (4+m)) (Fin (4+m)) F =>
    M (finSumFinEquiv (Sum.inr (⟨0,hm⟩ : Fin m)))
      (finSumFinEquiv (Sum.inr (⟨0,hm⟩ : Fin m)))) hga
  have htail : (blockSL m g).val
      (finSumFinEquiv (Sum.inr (⟨0,hm⟩ : Fin m)))
      (finSumFinEquiv (Sum.inr (⟨0,hm⟩ : Fin m))) = 1 := by
    change (fromBlocks g.val 0 0 (1 : Matrix (Fin m) (Fin m) F))
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr ⟨0,hm⟩)))
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr ⟨0,hm⟩))) = 1
    simp only [Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂, Matrix.one_apply_eq]
  have ha : a = 1 := by
    rw [htail] at haa
    simpa only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] using haa
  apply blockSL_injective m
  rw [map_one]
  apply Subtype.ext
  simpa [ha] using hga.symm

def slFourProjectiveEquiv : SL(4,F) ≃* PSL(4,F) :=
  MulEquiv.ofBijective (QuotientGroup.mk' (center SL(4,F)))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', center_four_eq_bot]),
      QuotientGroup.mk'_surjective _⟩

def fourToNormalizer (m : ℕ) : PSL(4,F) →* fourNormalizer (F:=F) m :=
  ((blockProjective m).comp slFourProjectiveEquiv.symm.toMonoidHom).codRestrict _ (by
    intro g
    apply Matrix.HigherLinear.parabolic_le_normalizer (fourSpace (F:=F) m)
    exact ⟨blockSL m (slFourProjectiveEquiv.symm g), blockSL_mem_parabolic m _, rfl⟩)

theorem fourToNormalizer_injective (m : ℕ) (hm : 0 < m) :
    Function.Injective (fourToNormalizer (F:=F) m) := by
  intro g h he
  exact slFourProjectiveEquiv.symm.injective
    (blockProjective_injective m hm (congrArg Subtype.val he))

end Theory.SpecificGroups.LinearHigher.FourBlock
