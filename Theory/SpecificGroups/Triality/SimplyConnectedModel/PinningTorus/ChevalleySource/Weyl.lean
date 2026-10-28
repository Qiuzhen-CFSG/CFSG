module
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.PointGeneration.Weyl
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus

/-!
# Exact normalizer conjugation for every Spin D4 root

Base reflection induction reaches every actual root from a numbered simple
root. Compositions of the already checked simple normalizers transport the
original root curves and their defining normalizer words. Reflection
covariance then supplies the all-root conjugation laws, with sign one in
characteristic two. The coroot law follows from its original two-word formula.

Source: GLS3, Chapter 1, Theorem 1.12.1(h,i,j).
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.SimplyConnected.Pinning.ChevalleySource
public noncomputable section
private def indexAction : List (Fin 4) → Equiv.Perm RootIndex
 | [] => Equiv.refl _
 | i::l => (indexAction l).trans ((typeDRootPairing 2).reflectionPerm (simpleRoot i))

private theorem indexAction_append (l m : List (Fin 4)) (r : RootIndex) :
    indexAction (l ++ m) r = indexAction l (indexAction m r) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change (typeDRootPairing 2).reflectionPerm (simpleRoot i) (indexAction (l ++ m) r) = _
    rw [ih]
    rfl

private theorem indexAction_negative (l : List (Fin 4)) (r : RootIndex) :
    indexAction l (negativeRoot r) = negativeRoot (indexAction l r) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change (typeDRootPairing 2).reflectionPerm (simpleRoot i) (indexAction l (negativeRoot r)) = _
    rw [ih, reflection_negativeRoot]
    rfl

private theorem root_simple_word (r : RootIndex) :
    ∃ (l : List (Fin 4)) (i : Fin 4), indexAction l (simpleRoot i) = r := by
  apply (typeDRootPairing_base 2).induction_reflect r
  · intro a ha
    obtain ⟨l,i,hi⟩ := ha
    refine ⟨l ++ [i], i, ?_⟩
    rw [indexAction_append]
    change indexAction l ((typeDRootPairing 2).reflectionPerm (simpleRoot i) (simpleRoot i)) = _
    rw [reflection_self_negativeRoot, indexAction_negative, hi, reflection_self_negativeRoot]
  · intro a ha
    obtain ⟨i,hi⟩ := (typeDRootPairing_baseEquiv 2).surjective ⟨a,ha⟩
    exact ⟨[],i,congrArg Subtype.val hi⟩
  · intro a b ha hb
    obtain ⟨l,i,hi⟩ := ha
    obtain ⟨j,hj⟩ := (typeDRootPairing_baseEquiv 2).surjective ⟨b,hb⟩
    refine ⟨j::l,i,?_⟩
    change (typeDRootPairing 2).reflectionPerm (simpleRoot j) (indexAction l (simpleRoot i)) = _
    rw [hi]
    exact congrArg (fun z => (typeDRootPairing 2).reflectionPerm z a) (congrArg Subtype.val hj)

private theorem reflection_covariance (s r t : RootIndex) :
    (typeDRootPairing 2).reflectionPerm s ((typeDRootPairing 2).reflectionPerm r t) =
      (typeDRootPairing 2).reflectionPerm ((typeDRootPairing 2).reflectionPerm s r) ((typeDRootPairing 2).reflectionPerm s t) := by
  apply (typeDRootPairing 2).root.injective
  simp only [RootPairing.root_reflectionPerm, RootPairing.reflection_reflectionPerm,
    LinearEquiv.mul_apply]
  rw [(typeDRootPairing 2).reflection_same]

private theorem indexAction_reflection (l : List (Fin 4)) (r t : RootIndex) :
    indexAction l ((typeDRootPairing 2).reflectionPerm r t) =
      (typeDRootPairing 2).reflectionPerm (indexAction l r) (indexAction l t) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change (typeDRootPairing 2).reflectionPerm (simpleRoot i) (indexAction l ((typeDRootPairing 2).reflectionPerm r t)) = _
    rw [ih, reflection_covariance]
    rfl

universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]
private def pointAction : List (Fin 4) → MulAut (Points k)
 | [] => 1
 | i::l => MulAut.conj ((simpleNormalizer k i)⁻¹) * pointAction l

private theorem pointAction_root (l : List (Fin 4)) (r : RootIndex) (a : k) :
    pointAction k l (rootPoint k r a) = rootPoint k (indexAction l r) a := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change (simpleNormalizer k i)⁻¹ * pointAction k l (rootPoint k r a) *
      ((simpleNormalizer k i)⁻¹)⁻¹ = _
    rw [ih, inv_inv, simpleNormalizer_rootPoint_conjugation]
    rfl

private theorem pointAction_normalizer (l : List (Fin 4)) (r : RootIndex) (t : kˣ) :
    pointAction k l (normalizerWord k r t) = normalizerWord k (indexAction l r) t := by
  simp only [normalizerWord, map_mul, pointAction_root, indexAction_negative]

/-- Every original root normalizer has its exact reflection action. -/
theorem normalizer_root_conjugation (r s : RootIndex) (a : k) :
    (normalizerWord k s 1)⁻¹ * rootPoint k r a * normalizerWord k s 1 =
      rootPoint k ((typeDRootPairing 2).reflectionPerm s r) a := by
  obtain ⟨l,i,hi⟩ := root_simple_word s
  obtain ⟨t,ht⟩ := (indexAction l).surjective r
  have h := congrArg (pointAction k l) (simpleNormalizer_rootPoint_conjugation k i t a)
  simp only [map_mul, map_inv, pointAction_root, pointAction_normalizer] at h
  rw [indexAction_reflection, hi, ht] at h
  exact h

theorem normalizer_normalizer_conjugation (r s : RootIndex) (t : kˣ) :
    (normalizerWord k s 1)⁻¹ * normalizerWord k r t * normalizerWord k s 1 =
      normalizerWord k ((typeDRootPairing 2).reflectionPerm s r) t := by
  let f := MulAut.conj ((normalizerWord k s 1)⁻¹)
  have hx (r : RootIndex) (a : k) : f (rootPoint k r a) = rootPoint k ((typeDRootPairing 2).reflectionPerm s r) a := by
    simpa only [f, MulAut.conj_apply, inv_inv] using normalizer_root_conjugation k r s a
  have hn : f (normalizerWord k r t) = normalizerWord k ((typeDRootPairing 2).reflectionPerm s r) t := by
    simp only [normalizerWord, map_mul, hx, reflection_negativeRoot]
  simpa only [f, MulAut.conj_apply, inv_inv] using hn

theorem normalizer_coroot_conjugation (r s : RootIndex) (t : kˣ) :
    (normalizerWord k s 1)⁻¹ * corootWord k r t * normalizerWord k s 1 =
      corootWord k ((typeDRootPairing 2).reflectionPerm s r) t := by
  let f := MulAut.conj ((normalizerWord k s 1)⁻¹)
  have hn (u : kˣ) : f (normalizerWord k r u) = normalizerWord k ((typeDRootPairing 2).reflectionPerm s r) u := by
    simpa only [f, MulAut.conj_apply, inv_inv] using normalizer_normalizer_conjugation k r s u
  have hh : f (corootWord k r t) = corootWord k ((typeDRootPairing 2).reflectionPerm s r) t := by
    simp only [corootWord, map_mul, map_inv, hn]
  simpa only [f, MulAut.conj_apply, inv_inv] using hh

end
end Triality.SimplyConnected.Pinning.ChevalleySource
