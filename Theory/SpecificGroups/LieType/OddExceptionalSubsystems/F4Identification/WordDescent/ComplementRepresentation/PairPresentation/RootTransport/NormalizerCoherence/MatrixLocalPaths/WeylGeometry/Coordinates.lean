module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairPresentation.RootTransport.NormalizerCoherence.MatrixLocalPaths
/-!
# Integer coordinates for the actual F4 Weyl action

The Bourbaki Cartan matrix computes simple reflections on integral simple-root
coordinates. The coordinate map into the existing real F4 root space is injective,
and intertwines every numbered word with its actual Weyl-group element. Equality
on all four simple-root coordinate vectors therefore proves equality of Weyl
elements, retaining the complete root stabilizer.

These lemmas check the finite Schreier corrections used to prove the two-node
factorization in GLS3 Lemma 2.9.4, `refs/KGroup/GLS3/chapter2.tex`, lines 1399–1427.
No matrix-cover or Curtis–Tits presentation assumption enters this argument.
-/

@[expose] public section

open Theory.AlgebraicGroup.StandardRootSystem
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.MatrixLocalPaths.WeylGeometry
abbrev Mark := Bool × Fin 4
abbrev Coeff := Fin 4 → ℤ

def reflectCoeff (i : Fin 4) (c : Coeff) : Coeff :=
  fun j => if j = i then c i - ∑ k, c k * typeF4CartanMatrix k i else c j

def wordCoeff : List (Fin 4) → Coeff → Coeff
  | [], c => c
  | i :: w, c => reflectCoeff i (wordCoeff w c)

def markCoeff (x : Mark) : Coeff :=
  fun k => if k = x.2 then if x.1 then 1 else -1 else 0

noncomputable def numberedProd (w : List (Fin 4)) : typeF4RootPairing.weylGroup :=
  typeF4RootPairing_base.wordProd (w.map sourceIndex)

noncomputable def coeffVector (c : Coeff) : Vec 4 :=
  ∑ k, (c k : ℝ) • typeF4SimpleRoot k

lemma coeffVector_injective : Function.Injective coeffVector := by
  intro c d h
  have he : (fun k => (c k : ℝ)) = (fun k => (d k : ℝ)) :=
    typeF4SimpleRoots_linearIndependent.fintypeLinearCombination_injective h
  funext i
  exact_mod_cast congrFun he i

lemma coeffVector_mark (x : Mark) :
    coeffVector (markCoeff x) = typeF4RootPairing.root (signedRoot x.1 x.2) := by
  let := typeF4RootPairing.indexNeg
  rcases x with ⟨s, i⟩
  cases s
  · change coeffVector (markCoeff (false, i)) =
      typeF4RootPairing.root (-(sourceIndex i) : typeF4Roots)
    change coeffVector (markCoeff (false, i)) =
      typeF4RootPairing.root (typeF4RootPairing.reflectionPerm (sourceIndex i) (sourceIndex i))
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
    simp [coeffVector, markCoeff, sourceIndex]
  · simp [coeffVector, markCoeff, signedRoot, sourceIndex]

lemma simple_smul_coeffVector (i : Fin 4) (c : Coeff) :
    typeF4RootPairing_base.simpleReflection (sourceIndex i) • coeffVector c =
      coeffVector (reflectCoeff i c) := by
  change typeF4RootPairing.reflection (sourceIndex i) (coeffVector c) = _
  rw [RootPairing.reflection_apply]
  have hc (k : Fin 4) : typeF4RootPairing.coroot' (sourceIndex i)
      (typeF4SimpleRoot k) = (typeF4CartanMatrix k i : ℝ) := by
    change typeF4RootPairing.coroot' (sourceIndex i)
      (typeF4RootPairing.root (sourceIndex k)) = _
    rw [RootPairing.root_coroot'_eq_pairing]
    exact typeF4RootPairing_simpleIndex_pairing k i
  simp only [coeffVector, map_sum, map_smul, hc]
  change _ - _ • typeF4SimpleRoot i = _
  fin_cases i <;>
    simp [reflectCoeff, typeF4CartanMatrix, Fin.sum_univ_four, sub_smul, add_smul,
      mul_smul] <;> module

lemma numberedProd_smul_coeffVector (w : List (Fin 4)) (c : Coeff) :
    numberedProd w • coeffVector c = coeffVector (wordCoeff w c) := by
  induction w with
  | nil => simp [numberedProd, wordCoeff]
  | cons i w ih =>
    change (typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd w) •
      coeffVector c = _
    rw [mul_smul, ih, simple_smul_coeffVector]
    rfl

lemma numberedProd_eq_of_coeff (v w : List (Fin 4))
    (h : ∀ j : Fin 4, wordCoeff v (markCoeff (true, j)) =
      wordCoeff w (markCoeff (true, j))) : numberedProd v = numberedProd w := by
  apply Subtype.ext
  apply RootPairing.Equiv.weightHom_injective typeF4RootPairing
  apply LinearEquiv.toLinearMap_injective
  apply typeF4RootPairing_base.toWeightBasis.ext
  intro j
  obtain ⟨i, rfl⟩ := typeF4RootPairing_baseEquiv.surjective j
  rw [RootPairing.Base.toWeightBasis_apply]
  change numberedProd v • typeF4RootPairing.root (sourceIndex i) =
    numberedProd w • typeF4RootPairing.root (sourceIndex i)
  have hm : typeF4RootPairing.root (sourceIndex i) =
      coeffVector (markCoeff (true, i)) := (coeffVector_mark (true, i)).symm
  rw [hm, numberedProd_smul_coeffVector, numberedProd_smul_coeffVector, h]

lemma numberedProd_endpoint_iff (w : List (Fin 4)) (x y : Mark) :
    typeF4RootPairing.weylGroupToPerm (numberedProd w) (signedRoot x.1 x.2) =
        signedRoot y.1 y.2 ↔ wordCoeff w (markCoeff x) = markCoeff y := by
  rw [← typeF4RootPairing.root.injective.eq_iff,
    ← RootPairing.weylGroup_apply_root, ← coeffVector_mark, ← coeffVector_mark,
    numberedProd_smul_coeffVector, coeffVector_injective.eq_iff]

@[simp] lemma numberedProd_nil : numberedProd [] = 1 :=
  typeF4RootPairing_base.wordProd_nil

lemma numberedProd_cons (i : Fin 4) (w : List (Fin 4)) :
    numberedProd (i :: w) =
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd w := rfl

lemma numberedProd_append (v w : List (Fin 4)) :
    numberedProd (v ++ w) = numberedProd v * numberedProd w := by
  simp only [numberedProd, List.map_append, RootPairing.Base.wordProd_append]

lemma numberedProd_reverse (w : List (Fin 4)) :
    numberedProd w.reverse = (numberedProd w)⁻¹ := by
  induction w with
  | nil => simp
  | cons i w ih =>
    simp [List.reverse_cons, numberedProd_append, numberedProd_cons, ih]

lemma pair_path (i j : Fin 4) (v : List Bool) (s k z l : Bool)
    (h : wordCoeff (v.map (pairNode i j)) (markCoeff (s, pairNode i j k)) =
      markCoeff (z, pairNode i j l)) :
    WeylPairPath (numberedProd (v.map (pairNode i j)))
      (s, pairNode i j k) (z, pairNode i j l) := by
  have he : numberedProd (v.map (pairNode i j)) =
      typeF4RootPairing_base.wordProd (pairTransportNodes i j v) := by
    simp only [numberedProd, List.map_map, pairTransportNodes, Function.comp_def]
  rw [← numberedProd_endpoint_iff] at h
  rw [he] at h ⊢
  exact WeylPairPath.localStep i j v s k z l h

lemma path_append (v w : List (Fin 4)) {x y z : Mark}
    (hw : WeylPairPath (numberedProd w) x y)
    (hv : WeylPairPath (numberedProd v) y z) :
    WeylPairPath (numberedProd (v ++ w)) x z := by
  rw [numberedProd_append]
  exact hw.trans hv

lemma edge_from_path (u v p : List (Fin 4)) (i : Fin 4) (x y : Mark)
    (hp : WeylPairPath (numberedProd p) x y)
    (he : ∀ j : Fin 4, wordCoeff p (markCoeff (true, j)) =
      wordCoeff (v.reverse ++ i :: u) (markCoeff (true, j))) :
    WeylPairPath ((numberedProd v)⁻¹ *
      typeF4RootPairing_base.simpleReflection (sourceIndex i) * numberedProd u) x y := by
  have h := numberedProd_eq_of_coeff p (v.reverse ++ i :: u) he
  rw [numberedProd_append, numberedProd_reverse, numberedProd_cons, ← mul_assoc] at h
  rw [← h]
  exact hp

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.MatrixLocalPaths.WeylGeometry
