module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.RootOperators
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedOpposition.AmbientNormalizer.SimpleReflections
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedOpposition.AmbientNormalizer.SimpleReflections.CorootRealization.Comparison
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TorusGeometry.PinnedMaps
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Normalizer.Lifts.RootTransport.UniquenessInput

/-!
# Simple-root point generation from actual root-subgroup uniqueness

The normalized chart words act by simple reflections on the supplied torus.
Their conjugates of root subgroups have the reflected root character. Actual
root-subgroup uniqueness identifies those conjugates, and reflection induction
puts every root subgroup into the signed-simple-root subgroup. The checked
all-root generation theorem then gives the full original ambient group.

Root-subgroup uniqueness is an explicit remaining geometric premise. Character
transport alone is not used as subgroup transport. In characteristic two every
root point is its own inverse, so subgroup and submonoid generation agree.
Sources: GLS3 1.9.5(b,f), §§1.11–1.12; Steinberg §6.
-/

public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open ClassBound ClassBound.FixedOpposition.AmbientNormalizer
open CorootRealization
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

omit [IsAlgClosed k] in
private theorem rootCurve_inv (S : Geometry K) (a : S.roots.Root) (t : k) :
    ((rootCurve S a).onPoints (kPlusPoint t))⁻¹ =
      (rootCurve S a).onPoints (kPlusPoint t) := by
  rw [← map_inv]
  have h : (kPlusPoint t)⁻¹ = kPlusPoint t := by
    apply (additiveGroupPointEquiv k).injective
    change Multiplicative.ofAdd (-t) = Multiplicative.ofAdd t
    rw [CharTwo.neg_eq]
  rw [h]

private def simpleRootPointSubgroup (S : Geometry K) : Subgroup (Variety.Point K) where
  __ := Submonoid.closure (simpleRootPoints S)
  inv_mem' := by
    intro g hg
    induction hg using Submonoid.closure_induction with
    | mem g hg =>
      obtain ⟨⟨i, b, t⟩, rfl⟩ := hg
      rw [rootCurve_inv]
      exact Submonoid.subset_closure ⟨⟨i, b, t⟩, rfl⟩
    | one =>
      change (1 : K.Point)⁻¹ ∈ Submonoid.closure (simpleRootPoints S)
      rw [inv_one]
      exact (Submonoid.closure (simpleRootPoints S)).one_mem
    | mul x y _ _ hx hy =>
      rw [mul_inv_rev]
      exact (Submonoid.closure (simpleRootPoints S)).mul_mem hy hx

omit [IsAlgClosed k] in
private theorem rootCurve_surjective (S : Geometry K) (a : S.roots.Root)
    (x : K.Point) (hx : x ∈ S.roots.rootSubgroup a) :
    ∃ t, (rootCurve S a).onPoints (kPlusPoint t) = x := by
  obtain ⟨z, hz⟩ := (S.rootParameter a).toMulEquiv.surjective
    ((S.roots.rootSubgroup a).pointEquiv.symm ⟨x, hx⟩)
  refine ⟨Multiplicative.toAdd (additiveGroupPointEquiv k z), ?_⟩
  change (S.roots.rootSubgroup a).includePoint ((S.rootParameter a).hom.onPoints
    ((additiveGroupPointEquiv k).symm (additiveGroupPointEquiv k z))) = x
  rw [Equiv.symm_apply_apply]
  change (S.roots.rootSubgroup a).includePoint ((S.rootParameter a).toMulEquiv z) = x
  rw [hz]
  exact congrArg Subtype.val ((S.roots.rootSubgroup a).pointEquiv.apply_symm_apply ⟨x, hx⟩)

omit [IsAlgClosed k] in
private theorem simpleRoot_le (S : Geometry K) (i : Fin 4) (b : Bool) :
    (S.roots.rootSubgroup (if b then (S.simpleRoot i).val
      else S.roots.neg (S.simpleRoot i).val)).toSubgroup ≤ simpleRootPointSubgroup S := by
  intro x hx
  obtain ⟨t, rfl⟩ := rootCurve_surjective S _ x hx
  exact Submonoid.subset_closure ⟨⟨i, b, t⟩, rfl⟩

omit [IsAlgClosed k] in
private theorem rootWeight_simpleReflection (S : Geometry K) (i : Fin 4)
    (a : S.roots.Root) (t : Variety.Point S.torus.carrierVariety) :
    (S.roots.rootWeight a).pointCharacter (AmbientCount.TorusGeometry.simpleReflection S i t) =
      (S.roots.rootWeight (S.roots.reflect (S.simpleRoot i).val a)).pointCharacter t := by
  rw [AmbientCount.TorusGeometry.simpleReflection, map_mul, map_inv,
    S.realized.rootWeight_rootCocharacter]
  rw [S.realized.2.2.2.2.2.1]
  change _ = ((torusPointEval S.torus.carrierVariety t
    (S.roots.rootWeight a * S.roots.rootWeight (S.simpleRoot i).val ^
      (-S.roots.pairing a (S.simpleRoot i).val))) : k)
  rw [map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, zpow_neg]
  rfl

omit [IsAlgClosed k] in
private theorem conjugate_simple_rootWeightEquation (S : Geometry K)
    (D : SimpleCorootWordData S) (i : Fin 4) (a : S.roots.Root) :
    RootWeightEquation S.torus
      ((S.roots.rootSubgroup a).conjugate ((D.parameters i).word 1))
      (S.roots.rootWeight (S.roots.reflect (S.simpleRoot i).val a)) := by
  intro y z t
  let X := S.roots.rootSubgroup a
  let g := (D.parameters i).word 1
  let e := X.conjugateIso g
  let x : OneParameterParametrization X.carrierVariety := e.symm.comp y
  let t₀ := AmbientCount.TorusGeometry.simpleReflection S i t
  have ht : S.torus.includePoint t₀ = g⁻¹ * S.torus.includePoint t * g := by
    have h := D.conjugation i t
    change S.torus.includePoint t * g = g * S.torus.includePoint t₀ at h
    rw [mul_assoc, h, inv_mul_cancel_left]
  have hx (c : k) : X.includePoint (x.value c) =
      g⁻¹ * (X.conjugate g).includePoint (y.value c) * g :=
    X.conjugateIso_inv_inclusion_apply g (y.value c)
  have hc : (S.roots.rootWeight a).pointCharacter t₀ =
      (S.roots.rootWeight (S.roots.reflect (S.simpleRoot i).val a)).pointCharacter t :=
    rootWeight_simpleReflection S i a t
  apply (MulAut.conj g⁻¹).injective
  rw [MulAut.conj_apply, MulAut.conj_apply, inv_inv]
  calc
    _ = (S.torus.includePoint t₀)⁻¹ * X.includePoint (x.value z) *
        S.torus.includePoint t₀ := by rw [ht, hx]; dsimp only [X, g]; group
    _ = X.includePoint (x.value ((S.roots.rootWeight a).pointCharacter t₀ * z)) :=
      (S.realized.2.2.1 a).2 x z t₀
    _ = _ := by rw [hx, hc]

/-- Actual root-subgroup uniqueness upgrades the character reflection of a
simple chart word to equality of closed root subgroups. -/
theorem simpleWord_conjugate_rootSubgroup_of_unique (S : Geometry K)
    (hu : ConnectedCentralizer.Normalizer.RootSubgroupUniqueness S)
    (D : SimpleCorootWordData S) (i : Fin 4) (a : S.roots.Root) :
    (S.roots.rootSubgroup a).conjugate ((D.parameters i).word 1) =
      S.roots.rootSubgroup (S.roots.reflect (S.simpleRoot i).val a) :=
  hu _ _ ((S.realized.2.2.1 a).1.conjugate_of_mem_normalizer _ (D.mem_normalizer i))
    (conjugate_simple_rootWeightEquation S D i a)

private theorem reflected_root_le (S : Geometry K)
    (hu : ConnectedCentralizer.Normalizer.RootSubgroupUniqueness S)
    (D : SimpleCorootWordData S) (H : Subgroup K.Point)
    (hs : ∀ i : Fin 4, (S.roots.rootSubgroup (S.simpleRoot i).val).toSubgroup ≤ H ∧
      (S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val)).toSubgroup ≤ H)
    (i : Fin 4) (a : S.roots.Root) (ha : (S.roots.rootSubgroup a).toSubgroup ≤ H) :
    (S.roots.rootSubgroup (S.roots.reflect (S.simpleRoot i).val a)).toSubgroup ≤ H := by
  have hg : (D.parameters i).word 1 ∈ H :=
    (sup_le (hs i).1 (hs i).2) ((D.parameters i).word_mem 1)
  rw [← simpleWord_conjugate_rootSubgroup_of_unique S hu D i a]
  intro x hx
  have hx' : ((D.parameters i).word 1)⁻¹ * x * (D.parameters i).word 1 ∈ H :=
    ha ((ClosedSubgroup.mem_conjugate_iff _ _ _).mp hx)
  have he := H.mul_mem (H.mul_mem hg hx') (H.inv_mem hg)
  simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using he

/-- Every root subgroup lies in a subgroup containing the signed simple roots,
provided actual root-subgroup uniqueness is supplied. -/
theorem all_rootSubgroups_le_of_signed_simple_of_unique (S : Geometry K)
    (hu : ConnectedCentralizer.Normalizer.RootSubgroupUniqueness S)
    (D : SimpleCorootWordData S) (H : Subgroup K.Point)
    (hs : ∀ i : Fin 4, (S.roots.rootSubgroup (S.simpleRoot i).val).toSubgroup ≤ H ∧
      (S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val)).toSubgroup ≤ H)
    (a : S.roots.Root) : (S.roots.rootSubgroup a).toSubgroup ≤ H := by
  let P := typeDRootPairing 2
  let := P.indexNeg
  have hneg (b : TypeDRootIndex 4) :
      S.rootIndex.symm (-b) = S.roots.neg (S.rootIndex.symm b) := by
    apply S.rootIndex.injective
    rw [S.based.2.2.1, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rfl
  have href (i : Fin 4) (b : TypeDRootIndex 4) :
      S.rootIndex.symm (P.reflectionPerm (typeDSimpleRootIndex 2 i) b) =
        S.roots.reflect (S.simpleRoot i).val (S.rootIndex.symm b) := by
    apply S.rootIndex.injective
    rw [S.based.2.1, S.simpleRoot_index, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hall (b : TypeDRootIndex 4) :
      (S.roots.rootSubgroup (S.rootIndex.symm b)).toSubgroup ≤ H ∧
        (S.roots.rootSubgroup (S.rootIndex.symm (-b))).toSubgroup ≤ H := by
    apply (typeDRootPairing_base 2).induction_reflect b
    · intro c hc
      change (S.roots.rootSubgroup (S.rootIndex.symm (-c))).toSubgroup ≤ H ∧
        (S.roots.rootSubgroup (S.rootIndex.symm (- -c))).toSubgroup ≤ H
      rw [neg_neg]
      exact hc.symm
    · intro c hc
      obtain ⟨i, hi⟩ := (typeDRootPairing_baseEquiv 2).surjective ⟨c, hc⟩
      have he : typeDSimpleRootIndex 2 i = c := congrArg Subtype.val hi
      rw [← he, ← S.simpleRoot_index, Equiv.symm_apply_apply, hneg,
        Equiv.symm_apply_apply]
      exact hs i
    · intro c d hc hd
      obtain ⟨i, hi⟩ := (typeDRootPairing_baseEquiv 2).surjective ⟨d, hd⟩
      have he : typeDSimpleRootIndex 2 i = d := congrArg Subtype.val hi
      have hn : -(P.reflectionPerm (typeDSimpleRootIndex 2 i) c) =
          P.reflectionPerm (typeDSimpleRootIndex 2 i) (-c) := by
        apply P.root.injective
        have hrootneg (e : TypeDRootIndex 4) : P.root (-e) = -P.root e := by
          change P.root (P.reflectionPerm e e) = _
          rw [P.root_reflectionPerm, P.reflection_apply_self]
        simp only [hrootneg, P.root_reflectionPerm, map_neg]
      rw [← he, hn, href, href]
      exact ⟨reflected_root_le S hu D H hs i _ hc.1,
        reflected_root_le S hu D H hs i _ hc.2⟩
  simpa only [Equiv.symm_apply_apply] using (hall (S.rootIndex a)).1

/-- Generation of the literal ambient points by the literal signed simple-root
parameters, conditional only on the charts and the remaining uniqueness theorem. -/
theorem simpleRootPoints_closure_eq_top_of_unique (S : Geometry K)
    (hcharts : ∀ i : Fin 4, Nonempty (SimpleRootSL2Chart S i))
    (hu : ConnectedCentralizer.Normalizer.RootSubgroupUniqueness S) :
    Submonoid.closure (simpleRootPoints S) = ⊤ := by
  let H := simpleRootPointSubgroup S
  let D := simpleCorootWordData_of_charts S (fun i => Classical.choice (hcharts i))
  have hroot (a : S.roots.Root) : (S.roots.rootSubgroup a).toSubgroup ≤ H :=
    all_rootSubgroups_le_of_signed_simple_of_unique S hu D H
      (fun i => ⟨simpleRoot_le S i true, simpleRoot_le S i false⟩) a
  have htop : (⊤ : Subgroup K.Point) ≤ H := by
    rw [← AmbientCount.TorusGeometry.rootSubgroupGenerated_eq_top S]
    exact RootSubgroupGenerated_le_of_rootSubgroup_le S.roots Set.univ H (fun a _ => hroot a)
  apply top_unique
  intro g _
  exact htop (Subgroup.mem_top g)

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
