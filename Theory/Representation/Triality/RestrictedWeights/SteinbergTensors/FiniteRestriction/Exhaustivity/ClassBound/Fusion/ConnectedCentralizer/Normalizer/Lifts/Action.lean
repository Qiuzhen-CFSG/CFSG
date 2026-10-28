module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Normalizer.Inputs
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Normalizer.Characters
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TorusGeometry.WeylRealization.NormalizerAction
public import Theory.AlgebraicGroup.RootSystems.AffinePath

/-!
# Faithfulness and identification of the actual D4 torus action

The simple-reflection character equations imply that every Weyl element pulls
back actual root characters by its inverse permutation of the roots. Injectivity
of the realized root characters and spanning of the root space then prove
faithfulness on torus points.

Every Weyl element is a word in the marked simple reflections, so their point
formulas also determine the whole action. Consequently any actual normalizer
realization has exactly the supplied `TorusData` action. This proves compatibility
without inferring a uniform conjugator from pointwise ambient conjugacy.

Source: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, 6.1--6.4; GLS3,
Chapter 1, Theorem 1.9.5(f). Existence of the normalizer realization is a
separate geometric obligation.
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight
namespace ConnectedCentralizer.Normalizer
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

omit [IsAlgClosed k] in
/-- Pullback by a simple reflection is the actual reflected root character. -/
theorem simple_root_character (S : Geometry K) {n : ℕ}
    (D : AmbientCount.TorusData S n) (i : Fin 4) (a : S.roots.Root)
    (t : Variety.Point S.torus.carrierVariety) :
    letI := D.action
    (S.roots.rootWeight a).pointCharacter
      (rootReflection S (S.simpleRoot i).val • t) =
    (S.roots.rootWeight (S.roots.reflect (S.simpleRoot i).val a)).pointCharacter t := by
  let := D.action
  obtain ⟨b, hb⟩ := S.weight.surjective (S.roots.rootWeight a)
  change S.weight (Multiplicative.ofAdd b.toAdd) = _ at hb
  have hi : b.toAdd i = S.roots.pairing a (S.simpleRoot i).val := by
    rw [← S.weight_coordinate b.toAdd i, hb, S.realized.weightPairing_rootWeight]
  rw [← hb, rootReflection, S.simpleRoot_index, D.reflection_weight,
    AmbientCount.TorusGeometry.reflection_character, hb, hi]
  rw [S.realized.2.2.2.2.2.1]

omit [IsAlgClosed k] in
/-- Pullback by a Weyl element permutes actual roots by its inverse. -/
theorem weyl_root_character (S : Geometry K) {n : ℕ}
    (D : AmbientCount.TorusData S n) (w : AmbientCount.Weyl)
    (a : S.roots.Root) (t : Variety.Point S.torus.carrierVariety) :
    letI := D.action
    (S.roots.rootWeight a).pointCharacter (w • t) =
      (S.roots.rootWeight (S.rootIndex.symm
        ((typeDRootPairing 2).weylGroupToPerm w⁻¹ (S.rootIndex a)))).pointCharacter t := by
  let := D.action
  obtain ⟨l, rfl⟩ := (typeDRootPairing_base 2).exists_wordProd_eq w
  induction l generalizing a with
  | nil => simp
  | cons j l ih =>
    obtain ⟨i, rfl⟩ := (typeDRootPairing_baseEquiv 2).surjective j
    rw [RootPairing.Base.wordProd_cons, mul_smul]
    have hs : (typeDRootPairing_base 2).simpleReflection
        (typeDRootPairing_baseEquiv 2 i) = rootReflection S (S.simpleRoot i).val := by
      change RootPairing.weylGroup.ofIdx (typeDRootPairing 2)
        (typeDSimpleRootIndex 2 i) = _
      rw [rootReflection, S.simpleRoot_index]
    rw [hs, simple_root_character, ih]
    rw [← hs]
    simp only [mul_inv_rev, RootPairing.Base.simpleReflection_inv, map_mul,
      Equiv.Perm.coe_mul, Function.comp_apply, S.based.2.1, S.simpleRoot_index]
    rfl

private theorem weyl_index_injective :
    Function.Injective (typeDRootPairing 2).weylGroupToPerm := by
  intro g h hgh
  apply Subtype.ext
  apply RootPairing.Equiv.weightHom_injective (typeDRootPairing 2)
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext_on_range (v := (typeDRootPairing 2).root)
    (RootPairing.IsRootSystem.span_root_eq_top (P := typeDRootPairing 2))
  intro i
  change g • (typeDRootPairing 2).root i = h • (typeDRootPairing 2).root i
  rw [RootPairing.weylGroup_apply_root, RootPairing.weylGroup_apply_root, hgh]

omit [IsAlgClosed k] in
/-- The supplied action on actual torus points is faithful. Root characters
detect the root permutation, which determines the Weyl element. -/
theorem weyl_eq_of_smul (S : Geometry K) {n : ℕ}
    (D : AmbientCount.TorusData S n) {v w : AmbientCount.Weyl}
    (h : letI := D.action; ∀ t : Variety.Point S.torus.carrierVariety, v • t = w • t) :
    v = w := by
  let := D.action
  apply inv_injective
  apply weyl_index_injective
  apply Equiv.ext
  intro i
  have hc : S.roots.rootWeight (S.rootIndex.symm
      ((typeDRootPairing 2).weylGroupToPerm v⁻¹ i)) =
    S.roots.rootWeight (S.rootIndex.symm
      ((typeDRootPairing 2).weylGroupToPerm w⁻¹ i)) := by
    apply TorusCharacter.pointCharacter_injective
    apply MonoidHom.ext
    intro t
    have hv := weyl_root_character S D v (S.rootIndex.symm i) t
    have hw := weyl_root_character S D w (S.rootIndex.symm i) t
    simpa only [Equiv.apply_symm_apply] using hv.symm.trans ((congrArg
      (S.roots.rootWeight (S.rootIndex.symm i)).pointCharacter (h t)).trans hw)
  exact S.rootIndex.symm.injective (S.realized.1 hc)

/-- The character equations in `TorusData` uniquely determine its entire
point action among actions with the same simple-root reflection formula. -/
theorem action_eq_of_simple (S : Geometry K) {n : ℕ}
    (D : AmbientCount.TorusData S n)
    (A : MulAction AmbientCount.Weyl (Variety.Point S.torus.carrierVariety))
    (hA : letI := A; ∀ (i : Fin 4) t,
      rootReflection S (S.simpleRoot i).val • t =
        AmbientCount.TorusGeometry.simpleReflection S i t)
    (w : AmbientCount.Weyl) (t : Variety.Point S.torus.carrierVariety) :
    @SMul.smul _ _ D.action.toSMul w t = @SMul.smul _ _ A.toSMul w t := by
  let := D.action
  obtain ⟨l, rfl⟩ := (typeDRootPairing_base 2).exists_wordProd_eq w
  induction l with
  | nil => exact (D.action.one_smul t).trans (A.one_smul t).symm
  | cons j l ih =>
    obtain ⟨i, rfl⟩ := (typeDRootPairing_baseEquiv 2).surjective j
    rw [RootPairing.Base.wordProd_cons]
    have hmD := D.action.mul_smul
      ((typeDRootPairing_base 2).simpleReflection (typeDRootPairing_baseEquiv 2 i))
      ((typeDRootPairing_base 2).wordProd l) t
    have hmA := A.mul_smul
      ((typeDRootPairing_base 2).simpleReflection (typeDRootPairing_baseEquiv 2 i))
      ((typeDRootPairing_base 2).wordProd l) t
    refine hmD.trans (Eq.trans ?_ hmA.symm)
    have hs : (typeDRootPairing_base 2).simpleReflection
        (typeDRootPairing_baseEquiv 2 i) = rootReflection S (S.simpleRoot i).val := by
      change RootPairing.weylGroup.ofIdx (typeDRootPairing 2)
        (typeDSimpleRootIndex 2 i) = _
      rw [rootReflection, S.simpleRoot_index]
    rw [hs]
    exact (simple_reflection_point S D i _).trans
      ((congrArg (AmbientCount.TorusGeometry.simpleReflection S i) ih).trans
        (hA i _).symm)

/-- A normalizer realization acts on the actual torus exactly as the
supplied `TorusData`, independently of how that data was constructed. -/
theorem normalizer_conjugation (S : Geometry K) {n : ℕ}
    (D : AmbientCount.TorusData S n)
    (R : AmbientCount.TorusGeometry.NormalizerRealization S)
    (g : S.torus.normalizer.toSubgroup) (t : Variety.Point S.torus.carrierVariety) :
    letI := D.action
    S.torus.includePoint (R.toWeyl g • t) =
      (g : Variety.Point K) * S.torus.includePoint t * (g : Variety.Point K)⁻¹ := by
  have hA : letI := R.action; ∀ (i : Fin 4) t,
      rootReflection S (S.simpleRoot i).val • t =
        AmbientCount.TorusGeometry.simpleReflection S i t := by
    intro i t
    simpa only [rootReflection, S.simpleRoot_index] using R.reflection_point i t
  exact (congrArg S.torus.includePoint
    (action_eq_of_simple S D R.action hA (R.toWeyl g) t)).trans (R.smul_include g t)

end ConnectedCentralizer.Normalizer
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
