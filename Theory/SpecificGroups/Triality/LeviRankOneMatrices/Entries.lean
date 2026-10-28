module
public import Theory.SpecificGroups.Triality.LeviRankOneMatrices.Geometry
/-!
# Integral entries of the D4 simple-root divided powers

The explicit root-string coordinates identify both degree-one Geck operators.
The positive degree-two operator has a single entry from −α to α, the negative
one reverses that entry, and both degree-three operators vanish. These identities
hold over ℤ, before specialization to the coefficient field.

Source: GLS3 §2.6, Proposition 2.6.2, using the same root curves on the full
Cartan-plus-root lattice (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace Triality.Standard.Parabolics.RankOneMatrices
noncomputable section
abbrev FlatIndex := Fin 4 ⊕ Fin 24

def flatEquiv (i : Fin 4) : FlatIndex ≃ LatticeIndex :=
  Equiv.sumCongr (typeDRootPairing_baseEquiv 2) ((rootOrder i).trans rootEnumeration)

def eData (i : Fin 4) : Matrix FlatIndex FlatIndex ℤ
  | .inl _, .inl _ => 0
  | .inl k, .inr s => if k = i ∧ s = 1 then 1 else 0
  | .inr r, .inl j => if r = 0 then |typeDCartanMatrix 2 i j| else 0
  | .inr r, .inr s => if raisingEdge r s then 1 else 0

def fData (i : Fin 4) : Matrix FlatIndex FlatIndex ℤ
  | .inl _, .inl _ => 0
  | .inl k, .inr s => if k = i ∧ s = 0 then 1 else 0
  | .inr r, .inl j => if r = 1 then |typeDCartanMatrix 2 i j| else 0
  | .inr r, .inr s => if raisingEdge s r then 1 else 0

lemma orderedRoot_eq_simple (i : Fin 4) (r : Fin 24) :
    orderedRoot i r = typeDSimpleRootIndex 2 i ↔ r = 0 := by
  rw [← orderedRoot_zero i, (orderedRoot_injective i).eq_iff]

lemma orderedRoot_eq_neg (i : Fin 4) (r : Fin 24) :
    orderedRoot i r = (typeDRootPairing 2).reflectionPerm
      (typeDSimpleRootIndex 2 i) (typeDSimpleRootIndex 2 i) ↔ r = 1 := by
  rw [← orderedRoot_one i, (orderedRoot_injective i).eq_iff]

@[simp] lemma flatEquiv_inl (i r : Fin 4) : flatEquiv i (.inl r) =
    .inl (typeDRootPairing_baseEquiv 2 r) := rfl
@[simp] lemma flatEquiv_inr (i : Fin 4) (r : Fin 24) : flatEquiv i (.inr r) =
    .inr (orderedRoot i r) := rfl

lemma eMatrix_entry (i : Fin 4) (r s : FlatIndex) :
    eMatrix (typeDRootPairing_baseEquiv 2 i) (flatEquiv i r) (flatEquiv i s) =
      eData i r s := by
  classical
  rcases r with r | r <;> rcases s with s | s
  · rfl
  · change (if (typeDRootPairing_baseEquiv 2 r) = (typeDRootPairing_baseEquiv 2 i) ∧
        orderedRoot i s = (typeDRootPairing 2).reflectionPerm
          (typeDSimpleRootIndex 2 i) (typeDSimpleRootIndex 2 i) then (1 : ℤ) else 0) = _
    simp [eData, orderedRoot_eq_neg]
  · change (if orderedRoot i r = typeDSimpleRootIndex 2 i then
        |(typeDRootPairing_base 2).cartanMatrix
          (typeDRootPairing_baseEquiv 2 i) (typeDRootPairing_baseEquiv 2 s)| else 0) = _
    simp [eData, orderedRoot_eq_simple, typeDRootPairing_base_cartanMatrix]
  · simp only [flatEquiv_inr]
    simp only [eMatrix, Matrix.fromBlocks_apply₂₂, Matrix.of_apply,
      typeDRootPairing_baseEquiv_val]
    simp only [root_add_simple_iff]
    by_cases h : raisingEdge r s
    · simp [eData, h, chainBot_zero i r s h]
    · simp [eData, h]

lemma fMatrix_entry (i : Fin 4) (r s : FlatIndex) :
    fMatrix (typeDRootPairing_baseEquiv 2 i) (flatEquiv i r) (flatEquiv i s) =
      fData i r s := by
  classical
  rcases r with r | r <;> rcases s with s | s
  · rfl
  · change (if (typeDRootPairing_baseEquiv 2 r) = (typeDRootPairing_baseEquiv 2 i) ∧
        orderedRoot i s = typeDSimpleRootIndex 2 i then (1 : ℤ) else 0) = _
    simp [fData, orderedRoot_eq_simple]
  · change (if orderedRoot i r = (typeDRootPairing 2).reflectionPerm
        (typeDSimpleRootIndex 2 i) (typeDSimpleRootIndex 2 i) then
        |(typeDRootPairing_base 2).cartanMatrix
          (typeDRootPairing_baseEquiv 2 i) (typeDRootPairing_baseEquiv 2 s)| else 0) = _
    simp [fData, orderedRoot_eq_neg, typeDRootPairing_base_cartanMatrix]
  · simp only [flatEquiv_inr]
    simp only [fMatrix, Matrix.fromBlocks_apply₂₂, Matrix.of_apply,
      typeDRootPairing_baseEquiv_val]
    simp only [root_sub_simple_iff]
    by_cases h : raisingEdge s r
    · simp [fData, h, chainTop_zero i r s h]
    · simp [fData, h]

lemma eTwo_entry (i : Fin 4) (r s : FlatIndex) :
    eDividedPower (typeDRootPairing_baseEquiv 2 i) 2 (flatEquiv i r) (flatEquiv i s) =
      if r = .inr 0 ∧ s = .inr 1 then 1 else 0 := by
  rcases r with r | r <;> rcases s with s | s
  · simp [eDividedPower, flatEquiv]
  · simp [eDividedPower, flatEquiv]
  · simp [eDividedPower, flatEquiv]
  · simp only [flatEquiv_inr]
    simp only [eDividedPower, Matrix.of_apply, typeDRootPairing_baseEquiv_val]
    simp only [root_add_nsmul_iff, Nat.reduceAdd, ordered_add_two]
    by_cases h : r = 0 ∧ s = 1
    · obtain ⟨rfl, rfl⟩ := h
      simp [chainBot_one]
    · simp [h]

lemma eThree_entry (i : Fin 4) (r s : FlatIndex) :
    eDividedPower (typeDRootPairing_baseEquiv 2 i) 3 (flatEquiv i r) (flatEquiv i s) = 0 := by
  rcases r with r | r <;> rcases s with s | s
  · rfl
  · rfl
  · rfl
  · simp only [flatEquiv_inr]
    simp only [eDividedPower, Matrix.of_apply, typeDRootPairing_baseEquiv_val]
    simp only [root_add_nsmul_iff, Nat.reduceAdd, ordered_add_three, if_false]

lemma fTwo_entry (i : Fin 4) (r s : FlatIndex) :
    fDividedPower (typeDRootPairing_baseEquiv 2 i) 2 (flatEquiv i r) (flatEquiv i s) =
      if r = .inr 1 ∧ s = .inr 0 then 1 else 0 := by
  rcases s with s | s
  · have h := congrFun (fDividedPower_add_two_mulVec_u
      (typeDRootPairing_baseEquiv 2 i) (typeDRootPairing_baseEquiv 2 s) 0) (flatEquiv i r)
    simpa only [u, Matrix.mulVec_single_one, flatEquiv_inl, Matrix.col_apply,
      Sum.inl_ne_inr, and_false, if_false, Pi.zero_apply] using h
  · by_cases hs : s = 0
    · subst s
      have hroot : (typeDRootPairing 2).root (orderedRoot i 1) =
          (typeDRootPairing 2).root (orderedRoot i 0) -
            (0 + 2) • (typeDRootPairing 2).root (typeDSimpleRootIndex 2 i) := by
        apply eq_sub_iff_add_eq.mpr
        exact ((root_add_nsmul_iff i 0 1 2).mpr
          ((ordered_add_two i 0 1).mpr ⟨rfl, rfl⟩)).symm
      have h := congrFun (fDividedPower_add_two_mulVec_v
        (i := typeDRootPairing_baseEquiv 2 i) 0 hroot) (flatEquiv i r)
      simp only [typeDRootPairing_baseEquiv_val, chainTop_zero_root, zero_add,
        Nat.choose_self, Nat.cast_one, one_smul, v, Matrix.mulVec_single_one] at h
      rcases r with r | r
      · simpa [flatEquiv_inl, Pi.single_apply] using h
      · simpa only [flatEquiv_inr, Pi.single_apply, Sum.inr.injEq,
          (orderedRoot_injective i).eq_iff, and_true, Matrix.col_apply] using h
    · have hno : (typeDRootPairing 2).root (orderedRoot i s) -
          (0 + 2) • (typeDRootPairing 2).root (typeDSimpleRootIndex 2 i) ∉
          Set.range (typeDRootPairing 2).root := by
        rintro ⟨k, hk⟩
        obtain ⟨k, rfl⟩ := orderedRoot_surjective i k
        have he := (eq_sub_iff_add_eq.mp hk).symm
        exact hs ((ordered_add_two i s k).mp ((root_add_nsmul_iff i s k 2).mp he)).1
      have h := congrFun (fDividedPower_add_two_mulVec_v_zero
        (typeDRootPairing_baseEquiv 2 i) (orderedRoot i s) 0 hno) (flatEquiv i r)
      simpa [v, Matrix.mulVec_single_one, flatEquiv, orderedRoot, hs] using h

lemma fThree_entry (i : Fin 4) (r s : FlatIndex) :
    fDividedPower (typeDRootPairing_baseEquiv 2 i) 3 (flatEquiv i r) (flatEquiv i s) = 0 := by
  have he : eDividedPower (typeDRootPairing_baseEquiv 2 i) 3 = 0 := by
    ext a b
    obtain ⟨a, rfl⟩ := (flatEquiv i).surjective a
    obtain ⟨b, rfl⟩ := (flatEquiv i).surjective b
    exact eThree_entry i a b
  simp [fDividedPower, he]

end
end Triality.Standard.Parabolics.RankOneMatrices
