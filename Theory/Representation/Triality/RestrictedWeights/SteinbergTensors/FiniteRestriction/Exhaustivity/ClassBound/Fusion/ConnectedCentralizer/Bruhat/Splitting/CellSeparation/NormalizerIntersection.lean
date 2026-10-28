module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Splitting.Inputs

/-!
# The actual positive Borel meets the torus normalizer in the torus

Unique positive-root coordinates imply that a positive unipotent element
centralizing the entire torus is trivial: every nonzero coordinate would
force its root character to be trivial. In the decomposition `B = T U`,
a normalizer element has a unipotent factor normalizing `T`. Its commutators
with `T` lie in both `T` and `U`, hence vanish by opposite-cell separation.
This proves the required intersection for the actual subgroups of `Geometry`.

Source: GLS3 1.11.3 and Steinberg 6.2(b), 6.3(a),
`refs/KGroup/GLS3/Chapter1.tex` and `refs/KGroup/GLS3/Chapter2St2.tex`.
-/

public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.ConnectedCentralizer.Bruhat.Splitting
open Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k] [CharP k 2] [IsAlgClosed k]
  {K : Variety k} [AlgebraicGroup K]

omit [IsAlgClosed k] in
private theorem positive_root_ne_one (S : Geometry K) (a : S.roots.Root)
    (ha : a ∈ S.roots.positive) : S.roots.rootWeight a ≠ 1 := by
  intro h
  have heq : S.roots.neg a = a := S.realized.1 (by
    rw [S.realized.2.2.2.1 a, h, inv_one])
  have hx : a ∈ S.roots.positive ∩ S.roots.neg ⁻¹' S.roots.positive :=
    ⟨ha, by simpa only [Set.mem_preimage, heq] using ha⟩
  rw [S.bigCell.data.positive.1] at hx
  exact hx

omit [CharP k 2] [IsAlgClosed k] in
private theorem parameter_zero {X : Variety k} [AlgebraicGroup X]
    (p : OneParameterParametrization X) : p.value 0 = 1 := by
  have h : kPlusPoint (0 : k) = 1 := by
    apply (additiveGroupPointEquiv k).injective
    rfl
  change p.hom.onPoints (kPlusPoint 0) = 1
  rw [h, map_one]

omit [IsAlgClosed k] in
/-- A positive unipotent element centralizing the whole torus is trivial. -/
theorem positive_centralizer_eq_one (S : Geometry K) (C : Bruhat.PositiveCoordinates S)
    {x : Variety.Point K} (hx : x ∈ positiveGroup S)
    (hcomm : ∀ t : Variety.Point S.torus.carrierVariety,
      S.torus.includePoint t * x = x * S.torus.includePoint t) : x = 1 := by
  obtain ⟨c, rfl⟩ := C.covers x hx
  have hscale (t : Variety.Point S.torus.carrierVariety) :
      (fun i => (S.roots.rootWeight (C.roots.get i)).pointCharacter t * c i) = c := by
    apply C.injective
    rw [← toralOrderedRootProduct_conjugation S.roots S.realized S.rootParameter C.roots c t]
    rw [mul_assoc, ← hcomm t]
    group
  have hc (i : Fin C.roots.length) : c i = 0 := by
    by_contra hi
    apply positive_root_ne_one S (C.roots.get i) ((C.mem_roots _).mp (C.roots.get_mem i))
    apply TorusCharacter.pointCharacter_injective
    ext t
    have hw : (S.roots.rootWeight (C.roots.get i)).pointCharacter t = 1 := by
      apply mul_right_cancel₀ hi
      simpa only [one_mul] using congrFun (hscale t) i
    exact hw
  unfold toralOrderedRootProduct
  apply List.prod_eq_one
  intro z hz
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
  rw [hc i, parameter_zero]
  change (S.roots.rootSubgroup (C.roots.get i)).inclusion.onPoints 1 = 1
  exact map_one _

/-- The actual positive Borel meets the actual torus normalizer in the torus. -/
theorem borel_inf_normalizer (S : Geometry K) (C : Bruhat.PositiveCoordinates S) :
    S.bigCell.data.B.toSubgroup ⊓ S.torus.normalizer.toSubgroup = S.torus.toSubgroup := by
  apply le_antisymm _ (le_inf S.bigCell.torus_le_positive S.torus.toSubgroup.le_normalizer)
  intro n hn
  obtain ⟨t, x, ht, hx, rfl⟩ := (S.bigCell.positive_decomposition n).mp hn.1
  have hxN : x ∈ S.torus.normalizer.toSubgroup := by
    have h := S.torus.normalizer.mul_mem
      (S.torus.normalizer.inv_mem (S.torus.toSubgroup.le_normalizer ht)) hn.2
    simpa only [inv_mul_cancel_left] using h
  have hxone : x = 1 := positive_centralizer_eq_one S C hx (by
    intro s
    let z := S.torus.includePoint s
    have hz : z ∈ S.torus.toSubgroup := (S.torus.pointEquiv s).property
    have hcomT : z⁻¹ * x * z * x⁻¹ ∈ S.torus.toSubgroup := by
      have hxzx := (Subgroup.mem_normalizer_iff.mp hxN z).mp hz
      simpa only [mul_assoc] using S.torus.mul_mem (S.torus.inv_mem hz) hxzx
    have hcomU : z⁻¹ * x * z * x⁻¹ ∈ positiveGroup S := by
      have hzN := torus_le_rootSubgroupGenerated_normalizer S.roots S.realized
        S.roots.positive (S.torus.inv_mem hz)
      have hzx := (Subgroup.mem_normalizer_iff.mp hzN x).mp hx
      simpa only [inv_inv] using (positiveGroup S).mul_mem hzx ((positiveGroup S).inv_mem hx)
    have heq : z⁻¹ * x * z * x⁻¹ = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← S.bigCell.torus_inf_positive_eq_bot S.maximalTorus.1]
      exact ⟨hcomT, hcomU⟩
    have hh := congrArg (fun y => z * y * x) heq
    dsimp [z] at hh ⊢
    simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_right, inv_mul_cancel, mul_one, one_mul] using hh.symm)
  rw [hxone, mul_one]
  exact ht
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.ConnectedCentralizer.Bruhat.Splitting
