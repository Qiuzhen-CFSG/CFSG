module
public import Theory.AlgebraicGroup.RootSystems.F4WeightAction.Stabilizer.Certificate
public import Theory.AlgebraicGroup.RootSystems.F4WeightAction.Stabilizer.Basic
public import Theory.AlgebraicGroup.RootSystems.AffinePath

/-!
# Interpreting finite certificates in the actual F4 Weyl group

Simple-word induction identifies the checked matrices with the faithful
integral action. Closure under simple reflections gives complete coverage.
Every root label is transported from an actual numbered simple root, and
reflection conjugation identifies its checked reflection matrix. Thus the
certificate is applied to the original root pairing, without an abstract
finite-group identification or a replacement lattice.
-/

open Theory.AlgebraicGroup.StandardRootSystem
namespace Theory.AlgebraicGroup.StandardRootSystem.F4WeightAction.Stabilizer
public noncomputable section


namespace Comparison

def simple (i : Fin 4) : Weyl :=
  RootPairing.weylGroup.ofIdx typeF4RootPairing (typeF4SimpleRootIndex i)

def word (l : List (Fin 4)) : Weyl := (l.map simple).prod

def representative (k : Fin 1152) : Weyl := word (Data.words k)

theorem representative_zero (c : Certificate) : representative 0 = 1 := by
  simp [representative, c.words_zero, word]

private theorem simple_weight (i : Fin 4) :
    rootWeight (typeF4SimpleRootIndex i) = Data.cartan i := by
  ext j
  rw [rootWeight_simple]
  have h : typeF4CartanMatrix = Data.cartan := by decide +kernel
  exact congrFun (congrFun h i) j

private theorem reflection_mulVec (c : Certificate) (k : Fin 1152) (i : Fin 4) (a : Weight) :
    Data.reflection i ((Data.matrix k).mulVec a) = (Data.matrix (Data.next k i)).mulVec a := by
  have hc (x j : Fin 4) := congrFun (c.next_columns k i j) x
  simp only [Data.reflection, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hc
  ext x
  simp only [Data.reflection, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct]
  simp_rw [← hc]
  simp only [Finset.sum_sub_distrib, sub_mul]
  congr 1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem representation_representative (c : Certificate) (k : Fin 1152) (a : Weight) :
    representation (representative k) a = (Data.matrix k).mulVec a := by
  induction k using Fin.strong_induction_on with
  | h k ih =>
    by_cases hk : k = 0
    · subst k
      rw [representative_zero c, map_one, c.matrix_zero, Matrix.one_mulVec]
      rfl
    · obtain ⟨hp, hw, hn⟩ := c.parent_spec k hk
      have he : representative k = simple (Data.step k) * representative (Data.parent k) := by
        simp [representative, word, hw]
      rw [he, map_mul]
      change representation (simple (Data.step k)) (representation (representative (Data.parent k)) a) = (Data.matrix k).mulVec a
      rw [ih _ hp, simple, representation_simple, simple_weight]
      exact (reflection_mulVec c _ _ a).trans (congrArg (fun j => (Data.matrix j).mulVec a) hn)

theorem representative_next (c : Certificate) (k : Fin 1152) (i : Fin 4) :
    representative (Data.next k i) = simple i * representative k := by
  apply representation_injective
  apply LinearEquiv.ext
  intro a
  rw [map_mul]
  change representation (representative _) a =
    representation (simple i) (representation (representative k) a)
  rw [representation_representative c, representation_representative c,
    simple, representation_simple, simple_weight]
  exact (reflection_mulVec c k i a).symm

theorem product_eq (c : Certificate) (a b d e : Fin 1152)
    (h : Data.matrix a * Data.matrix b = Data.matrix d * Data.matrix e) :
    representative a * representative b = representative d * representative e := by
  apply representation_injective
  apply LinearEquiv.ext
  intro x
  simp only [map_mul, LinearEquiv.mul_apply]
  simp only [representation_representative c, Matrix.mulVec_mulVec, h]

theorem exists_representative (c : Certificate) (w : Weyl) : ∃ k, representative k = w := by
  obtain ⟨l, rfl⟩ := typeF4RootPairing_base.exists_wordProd_eq w
  induction l with
  | nil => exact ⟨0, representative_zero c⟩
  | cons j l ih =>
    obtain ⟨k,hk⟩ := ih
    refine ⟨Data.next k (typeF4RootPairing_baseEquiv.symm j), ?_⟩
    rw [representative_next c, hk, RootPairing.Base.wordProd_cons]
    congr 1
    change RootPairing.weylGroup.ofIdx _ (typeF4SimpleRootIndex _) =
      RootPairing.weylGroup.ofIdx _ j.val
    congr 1
    have h := congrArg Subtype.val (typeF4RootPairing_baseEquiv.apply_symm_apply j)
    exact h

def root (r : Fin 24) : typeF4Roots :=
  typeF4RootPairing.weylGroupToPerm (representative (Data.rootRoute r))
    (typeF4SimpleRootIndex (Data.rootSimple r))

theorem root_weight (c : Certificate) (r : Fin 24) : rootWeight (root r) = Data.weights r := by
  rw [root, ← representation_root, representation_representative c, simple_weight,
    c.root_coordinates]

theorem root_reflection (c : Certificate) (r : Fin 24) :
    RootPairing.weylGroup.ofIdx typeF4RootPairing (root r) =
      representative (Data.refIndex r) := by
  apply mul_right_cancel (b := representative (Data.rootRoute r))
  change RootPairing.weylGroup.ofIdx _
    (typeF4RootPairing.weylGroupToPerm _ _) * _ = _
  rw [← reflection_mul]
  have h := product_eq c _ _ _ _ (c.reflection_matrix r)
  rw [representative_next c, representative_zero c, mul_one] at h
  exact h.symm

end Comparison
end
end Theory.AlgebraicGroup.StandardRootSystem.F4WeightAction.Stabilizer
