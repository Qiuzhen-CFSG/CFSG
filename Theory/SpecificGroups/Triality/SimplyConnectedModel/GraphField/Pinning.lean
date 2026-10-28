module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.Diagram
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.Frobenius

/-!
# Root and coroot compatibility for the concrete Spin graph-field action

Coordinate field automorphisms preserve the explicit even-orthogonal root
matrices. Faithfulness of the Spin natural action therefore gives Frobenius
on every actual pinned root parameter. The signed-simple-root diagram formulas
extend to all roots by reflection induction and the proved Weyl conjugation
identities. Generation then proves diagram/Frobenius commutation.

The source normalizer and coroot words give coordinatewise powers on the
constructed Spin torus. Its regular restriction is realized in the actual
coroot coordinate isomorphism, without transporting regularity through the
Spin-to-Omega point bijection. No simple or universal group premise is used.

Sources: GLS3, Chapter 1, 1.12.1 and 1.15.2–4; Chapter 2, §§2.1–2.3
(`refs/KGroup/GLS3/Chapter1.tex` and `refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
open Theory Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.SimplyConnected.Pinning.PointGeneration
open Theory.AlgebraicGroup.HyperbolicFieldAutomorphisms
noncomputable section
namespace Triality.SimplyConnected.GraphField
variable (k : Type*) [Field k] [IsAlgClosed k] [CharP k 2]

omit [IsAlgClosed k] [CharP k 2] in
private theorem coordinates_rootAction (σ : k ≃+* k) (r : RootIndex) (a : k)
    (v : QuadraticSpace k) :
    coordinates 4 σ (rootAction k r a v) =
      rootAction k r (σ a) (coordinates 4 σ v) := by
  unfold rootAction
  split_ifs <;> apply Prod.ext <;> funext i <;>
    simp only [coordinates, AddEquiv.coe_mk, Equiv.coe_fn_mk, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  all_goals split_ifs <;> simp only [map_add, map_sub, map_mul, map_one, map_zero]

theorem coefficientPointAut_rootPoint (σ : k ≃+* k) (r : RootIndex) (a : k) :
    coefficientPointAut k σ (rootPoint k r a) = rootPoint k r (σ a) := by
  apply naturalAction_injective k
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  rw [naturalAction_coefficientPointAut, naturalAction_rootPoint,
    naturalAction_rootPoint, rootAction_spec, coordinates_rootAction,
    coordinates_apply_symm, rootAction_spec]

theorem frobenius_rootPoint (n : ℕ) (r : RootIndex) (a : k) :
    frobeniusPointAut k n (rootPoint k r a) = rootPoint k r (a ^ (2 ^ n)) :=
  coefficientPointAut_rootPoint k (iterateFrobeniusEquiv k 2 n) r a

private theorem diagram_pairing (r s : RootIndex) :
    (typeDRootPairing 2).pairing (typeD4DiagramEquiv.indexEquiv r)
      (typeD4DiagramEquiv.indexEquiv s) = (typeDRootPairing 2).pairing r s := by
  exact typeD4DiagramEquiv.pairing_eq r s

private theorem diagram_reflection (r s : RootIndex) :
    typeD4DiagramEquiv.indexEquiv ((typeDRootPairing 2).reflectionPerm r s) =
      (typeDRootPairing 2).reflectionPerm (typeD4DiagramEquiv.indexEquiv r)
        (typeD4DiagramEquiv.indexEquiv s) := by
  apply (typeDRootPairing 2).root.injective
  rw [← RootPairing.Hom.root_weightMap_apply, RootPairing.root_reflectionPerm,
    RootPairing.reflection_apply_root, map_sub, map_smul,
    RootPairing.Hom.root_weightMap_apply, RootPairing.Hom.root_weightMap_apply,
    RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root, diagram_pairing]

private theorem diagram_negative (r : RootIndex) :
    typeD4DiagramEquiv.indexEquiv (negativeRoot r) =
      negativeRoot (typeD4DiagramEquiv.indexEquiv r) := by
  apply (typeDRootPairing 2).root.injective
  rw [← RootPairing.Hom.root_weightMap_apply, root_negativeRoot, map_neg,
    RootPairing.Hom.root_weightMap_apply, root_negativeRoot]

theorem diagram_rootPoint (r : RootIndex) (a : k) :
    Diagram.pinnedAut k (rootPoint k r a) =
      rootPoint k (typeD4DiagramEquiv.indexEquiv r) a := by
  have h : (∀ a, Diagram.pinnedAut k (rootPoint k r a) =
      rootPoint k (typeD4DiagramEquiv.indexEquiv r) a) ∧
      (∀ a, Diagram.pinnedAut k (rootPoint k (negativeRoot r) a) =
      rootPoint k (typeD4DiagramEquiv.indexEquiv (negativeRoot r)) a) := by
    apply (typeDRootPairing_base 2).induction_reflect r
    · intro s hs
      simpa only [reflection_self_negativeRoot, negativeRoot_negativeRoot] using hs.symm
    · intro s hs
      obtain ⟨i, hi⟩ := (typeDRootPairing_baseEquiv 2).surjective ⟨s, hs⟩
      have his : simpleRoot i = s := congrArg Subtype.val hi
      rw [← his]
      constructor
      · intro a
        simpa only [simpleRoot, typeD4DiagramEquiv_numbered] using
          Diagram.pinnedAut_positiveSimple k i a
      · intro a
        rw [diagram_negative]
        simpa only [simpleRoot, typeD4DiagramEquiv_numbered] using
          Diagram.pinnedAut_negativeSimple k i a
    · intro s j hs hj
      obtain ⟨i, hi⟩ := (typeDRootPairing_baseEquiv 2).surjective ⟨j, hj⟩
      have hij : simpleRoot i = j := congrArg Subtype.val hi
      rw [← hij]
      have hconj (s : RootIndex) (a : k)
          (ha : Diagram.pinnedAut k (rootPoint k s a) =
            rootPoint k (typeD4DiagramEquiv.indexEquiv s) a) :
          Diagram.pinnedAut k
            (rootPoint k ((typeDRootPairing 2).reflectionPerm (simpleRoot i) s) a) =
          rootPoint k (typeD4DiagramEquiv.indexEquiv
            ((typeDRootPairing 2).reflectionPerm (simpleRoot i) s)) a := by
        rw [← simpleNormalizer_rootPoint_conjugation, map_mul, map_mul, map_inv, ha]
        have hn : Diagram.pinnedAut k (simpleNormalizer k i) =
            simpleNormalizer k (typeD4DiagramPermutation i) :=
          (Diagram.pinnedAut_isPinned k).simpleNormalizer k i 1
        rw [hn, simpleNormalizer_rootPoint_conjugation, diagram_reflection]
        simp only [simpleRoot, typeD4DiagramEquiv_numbered]
      refine ⟨fun a => hconj s a (hs.1 a), fun a => ?_⟩
      rw [← reflection_negativeRoot]
      exact hconj (negativeRoot s) a (hs.2 a)
  exact h.1 a

/-- Frobenius preserves every actual pinned root parameter. -/
theorem frobenius_rootParameter (n : ℕ) (r : (pinnedRootData k).Root) (a : k) :
    (regularFrobeniusLift k n).onPoints
      (((pinnedRootData k).rootSubgroup r).includePoint
        ((pinnedRootParametrization k r).value a)) =
      ((pinnedRootData k).rootSubgroup r).includePoint
        ((pinnedRootParametrization k r).value (a ^ (2 ^ n))) := by
  simp only [regularFrobeniusLift_onPoints, pinnedRootParametrization_inclusion,
    frobenius_rootPoint]

/-- The full D4 permutation formula on the actual regular root curves. -/
theorem diagram_rootParameter (r : (pinnedRootData k).Root) (a : k) :
    (Diagram.pinnedIso k).toMulEquiv
      (((pinnedRootData k).rootSubgroup r).includePoint
        ((pinnedRootParametrization k r).value a)) =
      let s := pinnedRootIndex k (typeD4DiagramEquiv.indexEquiv r.down)
      ((pinnedRootData k).rootSubgroup s).includePoint
        ((pinnedRootParametrization k s).value a) := by
  change Diagram.pinnedAut k _ = _
  simp only [pinnedRootParametrization_inclusion, diagram_rootPoint]
  rfl

@[simp] theorem frobenius_positiveSimple (n : ℕ) (i : Fin 4) (a : k) :
    frobeniusPointAut k n (positiveSimplePoint k i a) =
      positiveSimplePoint k i (a ^ (2 ^ n)) := frobenius_rootPoint k n _ a

@[simp] theorem frobenius_negativeSimple (n : ℕ) (i : Fin 4) (a : k) :
    frobeniusPointAut k n (negativeSimplePoint k i a) =
      negativeSimplePoint k i (a ^ (2 ^ n)) := frobenius_rootPoint k n _ a

/-- Both endomorphisms are determined by their common signed-simple-root formulas. -/
theorem frobenius_diagram_commute (n : ℕ) (g : Points k) :
    frobeniusPointAut k n (Diagram.pinnedAut k g) =
      Diagram.pinnedAut k (frobeniusPointAut k n g) := by
  have h : (frobeniusPointAut k n).toMonoidHom.comp (Diagram.pinnedAut k).toMonoidHom =
      (Diagram.pinnedAut k).toMonoidHom.comp (frobeniusPointAut k n).toMonoidHom := by
    apply Diagram.hom_ext k <;> intro i t <;>
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        Diagram.pinnedAut_positiveSimple, Diagram.pinnedAut_negativeSimple,
        frobenius_positiveSimple, frobenius_negativeSimple]
  exact DFunLike.congr_fun h g

/-- Commutation holds for the independently regular algebraic morphisms. -/
theorem regularFrobenius_diagram_commute (n : ℕ) :
    (regularFrobeniusLift k n).comp (Diagram.pinnedIso k).hom =
      (Diagram.pinnedIso k).hom.comp (regularFrobeniusLift k n) := by
  apply AlgebraicGroup.Morphism.ext
  funext g
  change (regularFrobeniusLift k n).onPoints (Diagram.pinnedAut k g) =
    Diagram.pinnedAut k ((regularFrobeniusLift k n).onPoints g)
  simp only [regularFrobeniusLift_onPoints, frobenius_diagram_commute]

/-- Frobenius acts on the source normalizer word by powering its unit parameter. -/
theorem frobenius_normalizerWord (n : ℕ) (r : RootIndex) (t : kˣ) :
    frobeniusPointAut k n (normalizerWord k r t) =
      normalizerWord k r (t ^ (2 ^ n)) := by
  simp only [normalizerWord, map_mul, frobenius_rootPoint, Units.val_pow_eq_pow_val, CharTwo.neg_eq, inv_pow]

/-- This preserves the source convention `h(t) = n(1)⁻¹ n(t)`. -/
theorem frobenius_corootWord (n : ℕ) (r : RootIndex) (t : kˣ) :
    frobeniusPointAut k n (corootWord k r t) =
      corootWord k r (t ^ (2 ^ n)) := by
  simp only [corootWord, map_mul, map_inv, frobenius_normalizerWord, one_pow]

/-- The actual simple-coroot coordinates transform coordinatewise. -/
theorem frobenius_parameter (n : ℕ) (t : Fin 4 → kˣ) :
    frobeniusPointAut k n (CorootTorus.parameter k t) =
      CorootTorus.parameter k (fun i => t i ^ (2 ^ n)) := by
  simp only [CorootTorus.parameter, List.ofFn_succ, List.ofFn_zero,
    List.prod_cons, List.prod_nil, map_mul, map_one, simpleCoroot, frobenius_corootWord]

/-- The regular power map in the actual Spin coroot coordinates. -/
def torusFrobenius (n : ℕ) :
    AlgebraicGroup.Morphism (CorootTorus.closedSubgroup k).carrierVariety
      (CorootTorus.closedSubgroup k).carrierVariety :=
  (CorootTorus.coordinateIso k).hom.comp
    ((dCharacterTupleMorphism 4 4 (fun j i =>
      if i = j then (2 ^ n : ℕ) else (0 : ℤ))).comp (CorootTorus.coordinateIso k).inv)

/-- The regular torus map has the expected power formula. -/
theorem torusFrobenius_parameter (n : ℕ) (t : Fin 4 → kˣ) :
    (torusFrobenius k n).onPoints (CorootTorus.parameterPoint k t) =
      CorootTorus.parameterPoint k (fun i => t i ^ (2 ^ n)) := by
  change (CorootTorus.coordinateIso k).hom.onPoints
    ((dCharacterTupleMorphism 4 4 _).onPoints
      ((CorootTorus.coordinateIso k).inv.onPoints (CorootTorus.parameterPoint k t))) = _
  rw [CorootTorus.coordinateIso_inv_parameter, CorootTorus.coordinateIso_hom_apply]
  congr 1
  funext j
  rw [dCharacterTupleMorphism_apply, Equiv.apply_symm_apply]
  simp
  norm_cast

/-- The ambient Frobenius restricts regularly to this precise coroot power map. -/
theorem regularFrobenius_torus (n : ℕ) :
    (regularFrobeniusLift k n).comp (CorootTorus.closedSubgroup k).inclusion =
      (CorootTorus.closedSubgroup k).inclusion.comp (torusFrobenius k n) := by
  apply AlgebraicGroup.Morphism.ext
  funext t
  obtain ⟨x, rfl⟩ := (CorootTorus.coordinateIso k).toMulEquiv.surjective t
  change (regularFrobeniusLift k n).onPoints
      ((CorootTorus.closedSubgroup k).inclusion.onPoints
        ((CorootTorus.coordinateIso k).hom.onPoints x)) =
    (CorootTorus.closedSubgroup k).inclusion.onPoints
      ((torusFrobenius k n).onPoints ((CorootTorus.coordinateIso k).hom.onPoints x))
  simp only [CorootTorus.coordinateIso_hom_apply, torusFrobenius_parameter,
    CorootTorus.inclusion_parameterPoint, regularFrobeniusLift_onPoints, frobenius_parameter]

/-- Compatibility with every actual root cocharacter. -/
theorem frobenius_rootCocharacter (n : ℕ) (r : (pinnedRootData k).Root)
    (t : Variety.Point (KMult k)) :
    (regularFrobeniusLift k n).onPoints
      ((CorootTorus.closedSubgroup k).includePoint
        (((pinnedRootData k).rootCocharacter r).onPoints t)) =
      (CorootTorus.closedSubgroup k).includePoint
        (((pinnedRootData k).rootCocharacter r).onPoints (t ^ (2 ^ n))) := by
  simp only [regularFrobeniusLift_onPoints, pinnedRootData_rootCocharacter,
    frobenius_corootWord, dPointEquiv_pow, Pi.pow_apply]

end Triality.SimplyConnected.GraphField
