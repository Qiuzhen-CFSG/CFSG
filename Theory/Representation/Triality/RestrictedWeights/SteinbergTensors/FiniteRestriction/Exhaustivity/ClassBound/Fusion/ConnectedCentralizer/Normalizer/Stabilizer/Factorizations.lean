module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Normalizer.Stabilizer.Lattice
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Normalizer.Stabilizer.Factorizations.Checks
public import Theory.AlgebraicGroup.RootSystems.AffinePath

/-!
# Doubled-displacement reflection factorizations in D4

Every element of the actual D4 Weyl group is a product of root reflections
whose doubled root weights lie in its integral displacement lattice. The
statement applies to every representation with the numbered Cartan formulas.

Pairings with simple coroots distinguish roots. Equivariance of these pairings
therefore makes every compatible weight representation faithful. The checked
192-entry table is closed under all simple reflections, so generation by the
root pairing's base proves coverage of the actual Weyl group. The twelve root
reflections are identified by their actions on the simple roots. Finally, the
checked paths give reflection products and their integral displacement witnesses.

This is the finite lattice input for `Normalizer.Stabilizer`; it uses no torus
points, normalizer lifts or connectedness assumptions. All finite calculations
are checked by kernel reduction in `Factorizations.Checks`.

Source: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, 4.2, 5.3, 6.4(b), and
8.2(6)–(7), specialized to the marked D4 weight lattice.
-/

noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.ConnectedCentralizer.Normalizer.Stabilizer
open Theory.AlgebraicGroup.StandardRootSystem D4RestrictedWeight
open scoped BigOperators
open FactorizationData

private abbrev P := typeDRootPairing 2
private abbrev Weyl := AmbientCount.Weyl
private abbrev simple (i : Fin 4) : Weyl := RootPairing.weylGroup.ofIdx P (typeDSimpleRootIndex 2 i)
private def word (l : List (Fin 4)) : Weyl := (l.map simple).prod

private lemma word_nil : word [] = 1 := rfl
private lemma word_cons (i : Fin 4) (l : List (Fin 4)) : word (i :: l) = simple i * word l := rfl
private lemma word_base (l : List (Fin 4)) :
    word l = (typeDRootPairing_base 2).wordProd (l.map (typeDRootPairing_baseEquiv 2)) := by
  simp only [word, RootPairing.Base.wordProd, List.map_map]
  congr 1
private lemma exists_word (w : Weyl) : ∃ l, word l = w := by
  obtain ⟨l, rfl⟩ := (typeDRootPairing_base 2).exists_wordProd_eq w
  refine ⟨l.map (typeDRootPairing_baseEquiv 2).symm, ?_⟩
  rw [word_base, List.map_map]
  simp

private lemma rootWeight_inj : Function.Injective rootWeight := by
  intro r s h
  apply (typeDRootPairing_base 2).injective_pairingIn
  funext i
  obtain ⟨i, rfl⟩ := (typeDRootPairing_baseEquiv 2).surjective i
  exact congrFun h i

private lemma rootWeight_simple (i : Fin 4) :
    rootWeight (typeDSimpleRootIndex 2 i) = typeDCartanMatrix 2 i := by
  ext j
  exact typeDRootPairing_base_cartanMatrix 2 i j

private lemma rootWeight_reflection (r s : TypeDRootIndex 4) :
    rootWeight (P.reflectionPerm r s) =
      rootWeight s - (P.pairingIn ℤ s r) • rootWeight r := by
  ext j
  apply FaithfulSMul.algebraMap_injective ℤ ℝ
  simp only [rootWeight, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul,
    RootPairing.algebraMap_pairingIn]
  rw [← RootPairing.root_coroot_eq_pairing, RootPairing.root_reflectionPerm,
    RootPairing.reflection_apply_root]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, RootPairing.root_coroot_eq_pairing]

private lemma rootWeight_simple_reflection (i : Fin 4) (r : TypeDRootIndex 4) :
    rootWeight (P.reflectionPerm (typeDSimpleRootIndex 2 i) r) =
      reflection i (rootWeight r) := by
  rw [rootWeight_reflection, rootWeight_simple]
  rfl

private lemma rootWeight_weyl (ρ : AmbientCount.WeightRepresentation)
    (hρ : AmbientCount.ReflectionCompatible ρ) (w : Weyl) (r : TypeDRootIndex 4) :
    rootWeight (P.weylGroupToPerm w r) = ρ w (rootWeight r) := by
  obtain ⟨l, rfl⟩ := exists_word w
  induction l generalizing r with
  | nil => simp [word]
  | cons i l ih =>
    rw [word_cons, map_mul, map_mul]
    change rootWeight (P.reflectionPerm (typeDSimpleRootIndex 2 i)
      (P.weylGroupToPerm (word l) r)) = ρ (simple i) (ρ (word l) (rootWeight r))
    rw [rootWeight_simple_reflection, ih, hρ]

private lemma weyl_ext {w v : Weyl}
    (h : ∀ i : Fin 4, P.weylGroupToPerm w (typeDSimpleRootIndex 2 i) =
      P.weylGroupToPerm v (typeDSimpleRootIndex 2 i)) : w = v := by
  apply Subtype.ext
  apply RootPairing.Equiv.weightHom_injective P
  apply LinearEquiv.toLinearMap_inj.mp
  apply (typeDRootPairing_base 2).toWeightBasis.ext
  intro i
  obtain ⟨i, rfl⟩ := (typeDRootPairing_baseEquiv 2).surjective i
  simp only [RootPairing.Base.toWeightBasis_apply, typeDRootPairing_baseEquiv_val]
  change w • P.root (typeDSimpleRootIndex 2 i) = v • P.root (typeDSimpleRootIndex 2 i)
  rw [P.weylGroup_apply_root, P.weylGroup_apply_root, h]

private lemma representation_inj (ρ : AmbientCount.WeightRepresentation)
    (hρ : AmbientCount.ReflectionCompatible ρ) : Function.Injective ρ := by
  intro w v h
  apply weyl_ext
  intro i
  apply rootWeight_inj
  rw [rootWeight_weyl ρ hρ, rootWeight_weyl ρ hρ, h]

private lemma rootWeight_root (r : Fin 12) : rootWeight (root r) = weights r := by
  ext i
  apply FaithfulSMul.algebraMap_injective ℤ ℝ
  change algebraMap ℤ ℝ (P.pairingIn ℤ (root r) (typeDSimpleRootIndex 2 i)) = _
  rw [RootPairing.algebraMap_pairingIn, typeDRootPairing_pairing,
    typeDRootEmbedding_typeDSimpleRootIndex]
  rw [dot, Fin.sum_univ_four]
  fin_cases r <;> fin_cases i <;>
    norm_num [root, weights, typeDRootEmbedding, typeDRootVector, typeDSimpleRoot,
      basisVector, Pi.single_apply, Fin.ext_iff,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Fin.val_zero, Fin.val_one, Fin.val_succ]

private lemma pairing_symm (r s : TypeDRootIndex 4) :
    P.pairingIn ℤ r s = P.pairingIn ℤ s r := by
  apply FaithfulSMul.algebraMap_injective ℤ ℝ
  rw [RootPairing.algebraMap_pairingIn, RootPairing.algebraMap_pairingIn,
    typeDRootPairing_pairing, typeDRootPairing_pairing]
  simp only [dot, mul_comm]

private lemma representation_matrix (ρ : AmbientCount.WeightRepresentation)
    (hρ : AmbientCount.ReflectionCompatible ρ) (k : Fin 192) :
    (ρ (word (words k))).toLinearMap = (matrix k).mulVecLin := by
  induction k using Fin.strong_induction_on with
  | h k ih =>
    by_cases hk : k = 0
    · subst k
      simp [words_zero, word_nil, matrix_zero]
    · obtain ⟨hlt, hw, hn⟩ := parent_spec k hk
      have hp := ih (parent k) hlt
      apply (Pi.basisFun ℤ (Fin 4)).ext
      intro j
      simp only [Pi.basisFun_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply]
      rw [hw, word_cons, map_mul]
      change ρ (simple (step k)) (ρ (word (words (parent k))) (Pi.single j 1)) = _
      rw [show ρ (word (words (parent k))) (Pi.single j 1) =
        (matrix (parent k)).mulVec (Pi.single j 1) from LinearMap.congr_fun hp _]
      rw [hρ, Matrix.mulVec_single_one, Matrix.mulVec_single_one]
      ext a
      have hh := congrFun (matrix_next (parent k) (step k) j) a
      simpa only [reflection, Matrix.col_apply, hn] using hh

private lemma representation_apply (ρ : AmbientCount.WeightRepresentation)
    (hρ : AmbientCount.ReflectionCompatible ρ) (k : Fin 192) (a : Weight) :
    ρ (word (words k)) a = (matrix k).mulVec a :=
  LinearMap.congr_fun (representation_matrix ρ hρ k) a

private lemma word_next (ρ : AmbientCount.WeightRepresentation)
    (hρ : AmbientCount.ReflectionCompatible ρ) (k : Fin 192) (i : Fin 4) :
    word (words (next k i)) = simple i * word (words k) := by
  apply representation_inj ρ hρ
  apply LinearEquiv.toLinearMap_inj.mp
  apply (Pi.basisFun ℤ (Fin 4)).ext
  intro j
  simp only [Pi.basisFun_apply]
  change ρ (word (words (next k i))) (Pi.single j 1) =
    ρ (simple i * word (words k)) (Pi.single j 1)
  rw [map_mul]
  change ρ (word (words (next k i))) (Pi.single j 1) =
    ρ (simple i) (ρ (word (words k)) (Pi.single j 1))
  rw [representation_apply ρ hρ, representation_apply ρ hρ, hρ,
    Matrix.mulVec_single_one, Matrix.mulVec_single_one]
  ext a
  simpa only [reflection, Matrix.col_apply] using congrFun (matrix_next k i j).symm a

private lemma representatives_cover (ρ : AmbientCount.WeightRepresentation)
    (hρ : AmbientCount.ReflectionCompatible ρ) (w : Weyl) :
    ∃ k, word (words k) = w := by
  obtain ⟨l, rfl⟩ := exists_word w
  induction l with
  | nil => exact ⟨0, rfl⟩
  | cons i l ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨next k i, by rw [word_next ρ hρ, hk, word_cons]⟩

private lemma reflection_representative (ρ : AmbientCount.WeightRepresentation)
    (hρ : AmbientCount.ReflectionCompatible ρ) (r : Fin 12) :
    word (words (refIndex r)) = RootPairing.weylGroup.ofIdx P (root r) := by
  apply weyl_ext
  intro i
  apply rootWeight_inj
  rw [rootWeight_weyl ρ hρ, representation_apply ρ hρ, rootWeight_simple]
  change _ = rootWeight (P.reflectionPerm (root r) (typeDSimpleRootIndex 2 i))
  rw [rootWeight_reflection, rootWeight_simple, pairing_symm]
  change _ = typeDCartanMatrix 2 i - rootWeight (root r) i • rootWeight (root r)
  rw [rootWeight_root]
  exact matrix_reflection r i

private lemma path_product (ρ : AmbientCount.WeightRepresentation)
    (hρ : AmbientCount.ReflectionCompatible ρ) (k : Fin 192)
    (l : List (Fin 12 × Fin 192 × Weight)) (hl : pathValid k l) :
    ((l.map (fun p => root p.1)).map (RootPairing.weylGroup.ofIdx P)).prod =
      word (words k) := by
  induction l generalizing k with
  | nil =>
    change k = 0 at hl
    subst k
    rfl
  | cons p l ih =>
    rcases p with ⟨r, t, a⟩
    obtain ⟨hm, ht⟩ := hl
    simp only [List.map_cons, List.prod_cons]
    rw [ih t ht, ← reflection_representative ρ hρ]
    apply representation_inj ρ hρ
    apply LinearEquiv.ext
    intro x
    rw [map_mul]
    change ρ (word (words (refIndex r))) (ρ (word (words t)) x) =
      ρ (word (words k)) x
    rw [representation_apply ρ hρ, representation_apply ρ hρ,
      representation_apply ρ hρ, Matrix.mulVec_mulVec, ← hm]

/-- Every element of the actual D4 Weyl group has a reflection factorization
whose doubled root weights have integral displacement witnesses. -/
public theorem doubledRootFactorization (ρ : AmbientCount.WeightRepresentation)
    (hρ : AmbientCount.ReflectionCompatible ρ) (w : AmbientCount.Weyl) :
    DoubledRootFactorization ρ w := by
  obtain ⟨k, rfl⟩ := representatives_cover ρ hρ w
  refine ⟨(path k).map (fun p => root p.1), path_product ρ hρ k _ (paths_valid k), ?_⟩
  intro r hr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  refine ⟨p.2.2, ?_⟩
  rw [representation_apply ρ hρ, rootWeight_root]
  exact displacements k p hp


end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.ConnectedCentralizer.Normalizer.Stabilizer
