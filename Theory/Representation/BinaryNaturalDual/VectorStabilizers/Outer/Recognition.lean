module

public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Outer.KernelAction
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.ThreeAutomorphisms


/-!
# The nonsingular stabilizer as an actual automorphism group

Conjugation on the kernel group is faithful by the natural/dual calculation.
Its image contains every inner automorphism and an outer automorphism.
Inner/graph coverage in degree three or four proves surjectivity. Transport
through the actual binary projective-to-linear comparison then identifies the
full stabilizer with Aut(PSL in one lower dimension).

Both the pointwise formula and the subgroup-image equality retain compatibility
with the published inner-stabilizer equivalence. No order comparison is used
in the construction or in its proof of bijectivity.

Source: Aschbacher–Smith, H.9.1(4), printed p.390; the automorphism coverage
uses the binary specializations of GLS3, Theorem 2.5.12 and §2.7.
-/

@[expose] public section

open BinaryLinear.OuterCyclic
namespace BinaryNaturalDual.VectorStabilizers

/-- The actual kernel conjugation action, transported through `kernelCoordinates`. -/
noncomputable def linearConjugation {n : ℕ} (d : CoordinateAction n)
    {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    fullStabilizer d (x,f) →* MulAut (LinearGroup (n - 1)) :=
  (MulAut.congr (kernelGroupCoordinates h)).toMonoidHom.comp (kernelConjugation d h)

/-- The actual embedded kernel group in the published linear coordinates. -/
noncomputable def linearInner {n : ℕ} (d : CoordinateAction n)
    {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    LinearGroup (n - 1) →* fullStabilizer d (x,f) :=
  (kernelInner d h).comp (kernelGroupCoordinates h).symm.toMonoidHom

/-- Coordinate transport preserves the inner conjugation action. -/
theorem linearConjugation_inner {n : ℕ} (d : CoordinateAction n)
    {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1)
    (g : LinearGroup (n - 1)) : linearConjugation d h (linearInner d h g) = MulAut.conj g := by
  change MulAut.congr (kernelGroupCoordinates h)
    (kernelConjugation d h (kernelInner d h ((kernelGroupCoordinates h).symm g))) = _
  rw [kernelConjugation_inner]
  apply MulEquiv.ext
  intro t
  change kernelGroupCoordinates h ((kernelGroupCoordinates h).symm g *
    (kernelGroupCoordinates h).symm t * ((kernelGroupCoordinates h).symm g)⁻¹) = g * t * g⁻¹
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]

/-- Kernel coordinates preserve faithfulness of the stabilizer conjugation action. -/
theorem linearConjugation_injective {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    Function.Injective (linearConjugation d h) :=
  (MulAut.congr (kernelGroupCoordinates h)).injective.comp (kernelConjugation_injective hn d h)

/-- An outer stabilizer element induces an outer automorphism of the kernel group. -/
theorem linearConjugation_outer {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1)
    (a : fullStabilizer d (x,f)) (hout : a.val ∉ MulAut.innerSubgroup (LinearGroup n)) :
    linearConjugation d h a ∉ MulAut.innerSubgroup (LinearGroup (n - 1)) := by
  rintro ⟨g, hg⟩
  have he : linearInner d h g = a :=
    linearConjugation_injective hn d h ((linearConjugation_inner d h g).trans hg)
  have hh := ((innerInFullEquivKernel d h).symm ((kernelGroupCoordinates h).symm g)).property
  change linearInner d h g ∈ innerInFull d (x,f) at hh
  rw [he] at hh
  exact hout ((mem_innerInFull d (x,f) a).mp hh)

private theorem lower_inner_graph {n : ℕ} (hn : n = 4 ∨ n = 5)
    (a : MulAut (LinearGroup (n - 1))) :
    ∃ g : LinearGroup (n - 1), a = MulAut.conj g ∨
      a = graphLinear (n - 1) * MulAut.conj g := by
  rcases hn with rfl | rfl
  · exact BinaryLinear.InvariantNodeActions.ThreeAutomorphisms.inner_graph a
  · exact inner_graph (Or.inl rfl) a

/-- The actual conjugation action exhausts every automorphism of the kernel group. -/
theorem linearConjugation_surjective {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    Function.Surjective (linearConjugation d h) := by
  obtain ⟨s, hs, hout, hsq⟩ := exists_outer_involution (by omega) d h
  let a : fullStabilizer d (x,f) := ⟨s,hs⟩
  obtain ⟨b, hb | hb⟩ := lower_inner_graph hn (linearConjugation d h a)
  · exact False.elim (linearConjugation_outer hn d h a hout ⟨b,hb.symm⟩)
  · intro t
    obtain ⟨g, hg | hg⟩ := lower_inner_graph hn t
    · exact ⟨linearInner d h g, (linearConjugation_inner d h g).trans hg.symm⟩
    · refine ⟨a * linearInner d h (b⁻¹ * g), ?_⟩
      rw [map_mul, linearConjugation_inner, hb, mul_assoc, ← map_mul, mul_inv_cancel_left]
      exact hg.symm

/-- The full stabilizer is the actual automorphism group of the kernel linear group. -/
noncomputable def fullStabilizerEquivAutLinear {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    fullStabilizer d (x,f) ≃* MulAut (LinearGroup (n - 1)) :=
  MulEquiv.ofBijective (linearConjugation d h)
    ⟨linearConjugation_injective hn d h, linearConjugation_surjective hn d h⟩

/-- The actual projective-group identification in the corrected H.9.1(4). -/
noncomputable def fullStabilizerEquivAutProjective {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    fullStabilizer d (x,f) ≃*
      MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin (n - 1)) (ZMod 2)) :=
  (fullStabilizerEquivAutLinear hn d h).trans
    (MulAut.congr (projectiveEquivLinear (by omega)).symm)

/-- The identification restricts to conjugation by the published inner linear coordinates. -/
theorem fullStabilizerEquivAutLinear_inner {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1)
    (a : innerStabilizer d (x,f)) :
    fullStabilizerEquivAutLinear hn d h ⟨a.val,a.property.2⟩ =
      MulAut.conj (innerStabilizerEquivLinear d h a) := by
  let b : innerInFull d (x,f) := ⟨⟨a.val,a.property.2⟩,a.property⟩
  have he : linearInner d h (innerStabilizerEquivLinear d h a) = ⟨a.val,a.property.2⟩ := by
    change kernelInner d h ((kernelGroupCoordinates h).symm
      ((kernelGroupCoordinates h) (innerStabilizerEquivKernel d h a))) = _
    rw [MulEquiv.symm_apply_apply]
    exact congrArg Subtype.val ((innerInFullEquivKernel d h).symm_apply_apply b)
  change linearConjugation d h _ = _
  rw [← he, linearConjugation_inner]

/-- The projective identification agrees pointwise with the published inner-stabilizer map. -/
theorem fullStabilizerEquivAutProjective_inner {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1)
    (a : innerStabilizer d (x,f)) :
    fullStabilizerEquivAutProjective hn d h ⟨a.val,a.property.2⟩ =
      MulAut.conj (innerStabilizerEquivProjective hn d h a) := by
  change MulAut.congr (projectiveEquivLinear (by omega)).symm
    (fullStabilizerEquivAutLinear hn d h ⟨a.val,a.property.2⟩) = _
  rw [fullStabilizerEquivAutLinear_inner]
  apply MulEquiv.ext
  intro t
  change (projectiveEquivLinear (by omega)).symm
    (innerStabilizerEquivLinear d h a * (projectiveEquivLinear (by omega)) t *
      (innerStabilizerEquivLinear d h a)⁻¹) = _
  simp only [map_mul, map_inv, MulEquiv.symm_apply_apply]
  rfl

/-- The actual inner subgroup is carried onto the whole projective inner automorphism subgroup. -/
theorem fullStabilizerEquivAutProjective_map_inner {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    (innerInFull d (x,f)).map (fullStabilizerEquivAutProjective hn d h).toMonoidHom =
      MulAut.innerSubgroup (Matrix.ProjectiveSpecialLinearGroup (Fin (n - 1)) (ZMod 2)) := by
  ext b
  constructor
  · rintro ⟨a,ha,rfl⟩
    let ai : innerStabilizer d (x,f) := ⟨a.val,ha⟩
    exact ⟨innerStabilizerEquivProjective hn d h ai,
      (fullStabilizerEquivAutProjective_inner hn d h ai).symm⟩
  · rintro ⟨g,rfl⟩
    let ai := (innerStabilizerEquivProjective hn d h).symm g
    refine ⟨⟨ai.val,ai.property.2⟩, ai.property, ?_⟩
    change fullStabilizerEquivAutProjective hn d h ⟨ai.val,ai.property.2⟩ = _
    rw [fullStabilizerEquivAutProjective_inner, MulEquiv.apply_symm_apply]

end BinaryNaturalDual.VectorStabilizers
