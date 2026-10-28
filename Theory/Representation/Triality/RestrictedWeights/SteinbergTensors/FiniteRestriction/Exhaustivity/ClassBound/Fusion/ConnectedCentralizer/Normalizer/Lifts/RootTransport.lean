module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Normalizer.Lifts.Inputs
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Normalizer.Lifts.Action
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedOpposition.AmbientNormalizer.SimpleReflections
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Normalizer.Lifts.RootTransport.UniquenessInput
public import Theory.AlgebraicGroup.RootSubgroups.Conjugation

/-!
# Transport of supported D4 reflection words

Every actual root is a Weyl translate of a marked simple root. The normalizer
realization identifies left conjugation on the actual torus with the supplied
Weyl action. Pulling an arbitrary parametrization back along a conjugation
isomorphism shows that the conjugated root subgroup has the transported weight.
Root-subgroup uniqueness then identifies the subgroup itself, so conjugating a
simple coroot word gives a representative in the required opposite-root pair.
The reflection conjugation identity supplies its action on every torus point.

The final theorem in this module is conditional on `RootSubgroupUniqueness`.
That geometric input must still be proved from `Geometry` to establish the
transport theorem with only the normalizer realization and simple coroot words.
Character permutation is not used as a substitute for subgroup equivariance.

Sources: GLS3, `refs/KGroup/GLS3/Chapter1.tex`, Theorem 1.9.5(b,f),
Remarks 1.9.6 and Section 1.12; Steinberg, `Chapter2St2.tex`, 6.1--6.4,
8.2(4)--(5) and 8.3(c). Closed-subgroup conjugation here is left conjugation;
root-weight equations retain the source's inverse-conjugation convention.
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ConnectedCentralizer.Normalizer
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- The actual root indexed by the Weyl translate. -/
def transportedRoot (S : Geometry K) (w : AmbientCount.Weyl) (a : S.roots.Root) :
    S.roots.Root :=
  S.rootIndex.symm ((typeDRootPairing 2).weylGroupToPerm w (S.rootIndex a))

omit [IsAlgClosed k] in
/-- Weyl transport commutes with the actual opposite-root operation. -/
theorem transportedRoot_neg (S : Geometry K) (w : AmbientCount.Weyl)
    (a : S.roots.Root) :
    transportedRoot S w (S.roots.neg a) = S.roots.neg (transportedRoot S w a) := by
  let := (typeDRootPairing 2).indexNeg
  have hn (b : S.roots.Root) : S.rootIndex (S.roots.neg b) = -S.rootIndex b :=
    S.based.2.2.1 b
  apply S.rootIndex.injective
  simp only [transportedRoot, Equiv.apply_symm_apply, hn,
    RootPairing.weylGroupToPerm_neg]

omit [IsAlgClosed k] in
/-- Root reflections conjugate according to the same root permutation. -/
theorem rootReflection_transportedRoot (S : Geometry K) (w : AmbientCount.Weyl)
    (a : S.roots.Root) :
    rootReflection S (transportedRoot S w a) = w * rootReflection S a * w⁻¹ := by
  obtain ⟨l, rfl⟩ := (typeDRootPairing_base 2).exists_wordProd_eq w
  have h := (typeDRootPairing_base 2).wordProd_mul_ofIdx l (S.rootIndex a)
  simp only [rootReflection, transportedRoot, Equiv.apply_symm_apply]
  rw [h, mul_inv_cancel_right]

omit [IsAlgClosed k] in
/-- Every actual root is a Weyl translate of a marked simple root. -/
theorem exists_transported_simpleRoot (S : Geometry K) (a : S.roots.Root) :
    ∃ (i : Fin 4) (w : AmbientCount.Weyl),
      transportedRoot S w (S.simpleRoot i).val = a := by
  have h : ∀ b : TypeDRootIndex 4, ∃ (i : Fin 4) (w : AmbientCount.Weyl),
      (typeDRootPairing 2).weylGroupToPerm w (typeDSimpleRootIndex 2 i) = b := by
    intro b
    apply (typeDRootPairing_base 2).induction_reflect b
    · rintro c ⟨i, w, hw⟩
      refine ⟨i, RootPairing.weylGroup.ofIdx (typeDRootPairing 2) c * w, ?_⟩
      change (typeDRootPairing 2).reflectionPerm c
        ((typeDRootPairing 2).weylGroupToPerm w (typeDSimpleRootIndex 2 i)) = _
      rw [hw]
    · intro c hc
      obtain ⟨i, hi⟩ := (typeDRootPairing_baseEquiv 2).surjective ⟨c, hc⟩
      refine ⟨i, 1, ?_⟩
      exact congrArg Subtype.val hi
    · rintro c d ⟨i, w, hw⟩ _
      refine ⟨i, RootPairing.weylGroup.ofIdx (typeDRootPairing 2) d * w, ?_⟩
      change (typeDRootPairing 2).reflectionPerm d
        ((typeDRootPairing 2).weylGroupToPerm w (typeDSimpleRootIndex 2 i)) = _
      rw [hw]
  obtain ⟨i, w, hw⟩ := h (S.rootIndex a)
  refine ⟨i, w, ?_⟩
  apply S.rootIndex.injective
  simpa only [transportedRoot, Equiv.apply_symm_apply, S.simpleRoot_index] using hw

/-- The action equation on the canonical domain of the realization map. -/
theorem realization_conjugation (S : Geometry K) {n : ℕ}
    (D : AmbientCount.TorusData S n)
    (R : AmbientCount.TorusGeometry.NormalizerRealization S)
    (g : AmbientCount.TorusGeometry.TorusNormalizer S)
    (t : Variety.Point S.torus.carrierVariety) :
    letI := D.action
    S.torus.includePoint (R.toWeyl g • t) =
      (g : Variety.Point K) * S.torus.includePoint t * (g : Variety.Point K)⁻¹ :=
  normalizer_conjugation S D R g t

/-- The normalizer conjugate has the transported root weight. This proves
its character, without identifying it with the chosen root subgroup. -/
theorem conjugate_rootWeightEquation (S : Geometry K) {n : ℕ}
    (D : AmbientCount.TorusData S n)
    (R : AmbientCount.TorusGeometry.NormalizerRealization S)
    (g : AmbientCount.TorusGeometry.TorusNormalizer S) (a : S.roots.Root) :
    RootWeightEquation S.torus ((S.roots.rootSubgroup a).conjugate g)
      (S.roots.rootWeight (transportedRoot S (R.toWeyl g) a)) := by
  let := D.action
  intro y z t
  let X := S.roots.rootSubgroup a
  let e := X.conjugateIso (g : Variety.Point K)
  let x : OneParameterParametrization X.carrierVariety :=
    { hom := e.inv.comp y.hom
      inv := y.inv.comp e.hom
      hom_inv_id := by
        intro v
        change y.inv.onPoints (e.hom.onPoints (e.inv.onPoints (y.hom.onPoints v))) = v
        rw [e.inv_hom_id, y.hom_inv_id]
      inv_hom_id := by
        intro v
        change e.inv.onPoints (y.hom.onPoints (y.inv.onPoints (e.hom.onPoints v))) = v
        rw [y.inv_hom_id, e.hom_inv_id] }
  let t₀ := R.toWeyl g⁻¹ • t
  have ht : S.torus.includePoint t₀ =
      (g : Variety.Point K)⁻¹ * S.torus.includePoint t * g := by
    simpa only [Subgroup.coe_inv, inv_inv] using realization_conjugation S D R g⁻¹ t
  have hx (v : k) : X.includePoint (x.value v) =
      (g : Variety.Point K)⁻¹ * (X.conjugate g).includePoint (y.value v) * g :=
    X.conjugateIso_inv_inclusion_apply g (y.value v)
  have hc : (S.roots.rootWeight a).pointCharacter t₀ =
      (S.roots.rootWeight (transportedRoot S (R.toWeyl g) a)).pointCharacter t := by
    simpa only [t₀, map_inv, inv_inv, transportedRoot] using
      weyl_root_character S D (R.toWeyl g⁻¹) a t
  have h := (S.realized.2.2.1 a).2 x z t₀
  apply (MulAut.conj (g : Variety.Point K)⁻¹).injective
  rw [MulAut.conj_apply, MulAut.conj_apply, inv_inv]
  calc
    _ = (S.torus.includePoint t₀)⁻¹ * X.includePoint (x.value z) *
        S.torus.includePoint t₀ := by rw [ht, hx]; dsimp only [X]; group
    _ = X.includePoint (x.value ((S.roots.rootWeight a).pointCharacter t₀ * z)) := h
    _ = _ := by rw [hx, hc]

/-- Actual subgroup equivariance follows from root-weight transport and
uniqueness, rather than character permutation alone. -/
theorem rootSubgroup_conjugate_of_unique (S : Geometry K) {n : ℕ}
    (D : AmbientCount.TorusData S n)
    (R : AmbientCount.TorusGeometry.NormalizerRealization S)
    (hunique : RootSubgroupUniqueness S)
    (g : AmbientCount.TorusGeometry.TorusNormalizer S) (a : S.roots.Root) :
    (S.roots.rootSubgroup a).conjugate g =
      S.roots.rootSubgroup (transportedRoot S (R.toWeyl g) a) := by
  exact hunique _ _
    (IsTorusRootSubgroup.conjugate_of_mem_normalizer
      (g : Variety.Point K) g.property (S.realized.2.2.1 a).1)
    (conjugate_rootWeightEquation S D R g a)

/-- Conjugation transports the subgroup generated by an opposite-root pair. -/
theorem conjugate_mem_opposite_pair_of_unique (S : Geometry K) {n : ℕ}
    (D : AmbientCount.TorusData S n)
    (R : AmbientCount.TorusGeometry.NormalizerRealization S)
    (hunique : RootSubgroupUniqueness S)
    (g : AmbientCount.TorusGeometry.TorusNormalizer S) (a : S.roots.Root)
    (x : Variety.Point K)
    (hx : x ∈ (S.roots.rootSubgroup a).toSubgroup ⊔
      (S.roots.rootSubgroup (S.roots.neg a)).toSubgroup) :
    (g : Variety.Point K) * x * (g : Variety.Point K)⁻¹ ∈
      (S.roots.rootSubgroup (transportedRoot S (R.toWeyl g) a)).toSubgroup ⊔
      (S.roots.rootSubgroup (S.roots.neg (transportedRoot S (R.toWeyl g) a))).toSubgroup := by
  have hmem (b : S.roots.Root) (y : Variety.Point K)
      (hy : y ∈ S.roots.rootSubgroup b) :
      (g : Variety.Point K) * y * (g : Variety.Point K)⁻¹ ∈
        S.roots.rootSubgroup (transportedRoot S (R.toWeyl g) b) := by
    rw [← rootSubgroup_conjugate_of_unique S D R hunique g b,
      ClosedSubgroup.mem_conjugate_iff]
    simp only [inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one]
    exact hy
  let f := (MulAut.conj (g : Variety.Point K)).toMonoidHom
  let H := (S.roots.rootSubgroup (transportedRoot S (R.toWeyl g) a)).toSubgroup ⊔
    (S.roots.rootSubgroup (S.roots.neg (transportedRoot S (R.toWeyl g) a))).toSubgroup
  have hle : (S.roots.rootSubgroup a).toSubgroup ⊔
      (S.roots.rootSubgroup (S.roots.neg a)).toSubgroup ≤ H.comap f := by
    apply sup_le
    · intro y hy
      exact Subgroup.mem_sup_left (hmem a y hy)
    · intro y hy
      have h := hmem (S.roots.neg a) y hy
      rw [transportedRoot_neg] at h
      exact Subgroup.mem_sup_right h
  exact hle hx

/-- A normalized simple word has the expected Weyl image in every
normalizer realization compatible with the actual torus. -/
theorem simpleWord_toWeyl (S : Geometry K) {n : ℕ}
    (D : AmbientCount.TorusData S n)
    (R : AmbientCount.TorusGeometry.NormalizerRealization S)
    (C : FixedOpposition.AmbientNormalizer.SimpleCorootWordData S) (i : Fin 4) :
    R.toWeyl ⟨(C.parameters i).word 1, by exact C.mem_normalizer i⟩ =
      rootReflection S (S.simpleRoot i).val := by
  apply weyl_eq_of_smul S D
  intro t
  apply S.torus.inclusion_injective
  change S.torus.includePoint _ = S.torus.includePoint _
  rw [realization_conjugation S D R, C.left_conjugation,
    simple_reflection_point S D]

/-- Conditional assembly of supported reflection representatives. The
remaining uniqueness hypothesis is kept explicit: its proof from `Geometry`
is required before the two-input transport theorem can be asserted. -/
theorem oppositeReflectionLifts_of_normalizerRealization_of_simpleCorootWords_of_unique
    (S : Geometry K) {n : ℕ} (D : AmbientCount.TorusData S n)
    (R : AmbientCount.TorusGeometry.NormalizerRealization S)
    (C : FixedOpposition.AmbientNormalizer.SimpleCorootWordData S)
    (hunique : RootSubgroupUniqueness S) : OppositeReflectionLifts S D := by
  let := D.action
  intro a
  obtain ⟨i, w, hw⟩ := exists_transported_simpleRoot S a
  obtain ⟨g, hg⟩ := R.surjective w
  let s : AmbientCount.TorusGeometry.TorusNormalizer S :=
    ⟨(C.parameters i).word 1, by exact C.mem_normalizer i⟩
  refine ⟨⟨(g * s * g⁻¹).val, by exact (g * s * g⁻¹).property⟩, ?_, ?_⟩
  · have h := conjugate_mem_opposite_pair_of_unique S D R hunique g
      (S.simpleRoot i).val ((C.parameters i).word 1) ((C.parameters i).word_mem 1)
    rw [hg, hw] at h
    exact h
  · intro t
    have hs : R.toWeyl s = rootReflection S (S.simpleRoot i).val :=
      simpleWord_toWeyl S D R C i
    have ha : rootReflection S a = R.toWeyl (g * s * g⁻¹) := by
      rw [map_mul, map_mul, map_inv, hg, hs, ← hw]
      exact rootReflection_transportedRoot S w (S.simpleRoot i).val
    rw [ha]
    exact realization_conjugation S D R (g * s * g⁻¹) t

end ConnectedCentralizer.Normalizer
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
