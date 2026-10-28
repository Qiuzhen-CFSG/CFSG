module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.PointGeneration.RootReflection
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.PointGeneration.CorootReflection

/-!
# Pinned Weyl conjugation on the Clifford Spin points

The checked coordinate permutations conjugate each elementary root matrix to
its reflected root matrix. The faithful natural action lifts this equality to
the concrete Spin carrier. Conjugating the defining source words then proves
the normalizer and coroot identities with exactly the same parametrizations.

Source: GLS3, Chapter 1, Theorem 1.12.1(h,i,j), with
`nα(t) = xα(t) x−α(−t⁻¹) xα(t)` and `hα(t) = nα(1)⁻¹ nα(t)`.
-/

@[expose] public section
noncomputable section
namespace Triality.SimplyConnected.Pinning
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open PointGeneration

/-- The explicit negative index is the negative root of the actual root pairing. -/
theorem root_negativeRoot (r : RootIndex) :
    (typeDRootPairing 2).root (negativeRoot r) = -(typeDRootPairing 2).root r := by
  apply Subtype.ext
  exact negativeRoot_vector r

/-- Reflection in a root takes that root to the explicit negative index. -/
theorem reflection_self_negativeRoot (r : RootIndex) :
    (typeDRootPairing 2).reflectionPerm r r = negativeRoot r := by
  apply (typeDRootPairing 2).root.injective
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, root_negativeRoot]

/-- The root-index reflection commutes with the source's explicit negation. -/
theorem reflection_negativeRoot (s r : RootIndex) :
    (typeDRootPairing 2).reflectionPerm s (negativeRoot r) =
      negativeRoot ((typeDRootPairing 2).reflectionPerm s r) := by
  apply (typeDRootPairing 2).root.injective
  rw [RootPairing.root_reflectionPerm, root_negativeRoot, map_neg,
    root_negativeRoot, RootPairing.root_reflectionPerm]

universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

/-- Source relation 1.12.1(h), with the signs equal to one in characteristic two. -/
theorem simpleNormalizer_rootPoint_conjugation (i : Fin 4) (r : RootIndex) (a : k) :
    (simpleNormalizer k i)⁻¹ * rootPoint k r a * simpleNormalizer k i =
      rootPoint k ((typeDRootPairing 2).reflectionPerm (simpleRoot i) r) a := by
  obtain ⟨r, rfl⟩ := rootAt_surjective r
  rw [reflection_rootAt]
  rw [show (simpleNormalizer k i)⁻¹ = simpleNormalizer k i from normalizerWord_inv k _ _]
  apply naturalAction_injective k
  simp only [map_mul, naturalAction_rootPoint]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, simpleNormalizer_apply, rootAction_spec]
  exact rootAction_conjugation k i r a z

/-- Source relation 1.12.1(j) for the prescribed normalizer words. -/
theorem simpleNormalizer_normalizerWord_conjugation (i : Fin 4) (r : RootIndex) (t : kˣ) :
    (simpleNormalizer k i)⁻¹ * normalizerWord k r t * simpleNormalizer k i =
      normalizerWord k ((typeDRootPairing 2).reflectionPerm (simpleRoot i) r) t := by
  let f := MulAut.conj ((simpleNormalizer k i)⁻¹)
  have hx (s : RootIndex) (a : k) : f (rootPoint k s a) =
      rootPoint k ((typeDRootPairing 2).reflectionPerm (simpleRoot i) s) a := by
    simpa only [f, MulAut.conj_apply, inv_inv] using
      simpleNormalizer_rootPoint_conjugation k i s a
  have hn : f (normalizerWord k r t) =
      normalizerWord k ((typeDRootPairing 2).reflectionPerm (simpleRoot i) r) t := by
    simp only [normalizerWord, map_mul, hx, reflection_negativeRoot]
  simpa only [f, MulAut.conj_apply, inv_inv] using hn

/-- Source relation 1.12.1(i), derived from the ordered source coroot word. -/
theorem simpleNormalizer_corootWord_conjugation (i : Fin 4) (r : RootIndex) (t : kˣ) :
    (simpleNormalizer k i)⁻¹ * corootWord k r t * simpleNormalizer k i =
      corootWord k ((typeDRootPairing 2).reflectionPerm (simpleRoot i) r) t := by
  let f := MulAut.conj ((simpleNormalizer k i)⁻¹)
  have hn (u : kˣ) : f (normalizerWord k r u) =
      normalizerWord k ((typeDRootPairing 2).reflectionPerm (simpleRoot i) r) u := by
    simpa only [f, MulAut.conj_apply, inv_inv] using
      simpleNormalizer_normalizerWord_conjugation k i r u
  have hh : f (corootWord k r t) =
      corootWord k ((typeDRootPairing 2).reflectionPerm (simpleRoot i) r) t := by
    simp only [corootWord, map_mul, map_inv, hn]
  simpa only [f, MulAut.conj_apply, inv_inv] using hh

/-- The reflected simple coroot is the Cartan-prescribed product of source coroots. -/
theorem reflected_simpleCoroot (i j : Fin 4) (t : kˣ) :
    corootWord k ((typeDRootPairing 2).reflectionPerm (simpleRoot i) (simpleRoot j)) t =
      simpleCoroot k j t * simpleCoroot k i (t ^ (-typeDCartanMatrix 2 j i)) := by
  rw [← simpleNormalizer_corootWord_conjugation]
  exact simpleNormalizer_simpleCoroot_conjugation k i j t

end Triality.SimplyConnected.Pinning
