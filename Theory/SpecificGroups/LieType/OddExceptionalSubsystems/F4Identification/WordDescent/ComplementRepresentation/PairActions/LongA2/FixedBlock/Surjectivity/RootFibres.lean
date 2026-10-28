module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.AdjointRestriction.Coordinates

/-!
# Full root fibres of the E6 to F4 projection

The literal coordinate projection determines the sum of a root and its diagram
image. Its composition with the F4 height functional is E6 root height, so no
root projects to zero. Distinct roots in a fibre consequently have nonpositive
inner product: a positive inner product would make their difference a root in
the kernel. Positivity of the norm of the orbit sum then forces every root in
a fibre to be one of the two diagram translates.

This proves the geometry used to reconstruct the entire fixed Geck space in
`FixedBlock.Surjectivity`, without assuming image containment or a model
isomorphism. Sources: the twisted-root projection in GLS3 §§2.3.1--2.3.2 and
the common-lattice subsystem construction of §2.6.2, used for the F4 inclusions
in Aschbacher--Smith A.2.17, printed p.39 of `refs/quasithin.pdf`.
-/

noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.LongA2.FixedBlock
open AdjointRestriction

private def heightFunctional : Vec 4 →ₗ[ℝ] ℝ where
  toFun x := 8 * x 0 + 3 * x 1 + 2 * x 2 + x 3
  map_add' x y := by simp; ring
  map_smul' c x := by simp; ring

private theorem heightFunctional_simple (i : Fin 6) :
    heightFunctional (rootProjection (typeE6SimpleRoot i)) = 1 := by
  rw [rootProjection_simple]
  fin_cases i <;>
    change 8 * _ + 3 * _ + 2 * _ + _ = (1 : ℝ)
  all_goals norm_num [node, heightFunctional, typeF4SimpleRoot, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

private theorem projection_ne_zero (r : typeE6Roots) : rootProjection r.val ≠ 0 := by
  let h : typeE6RootSpan →ₗ[ℝ] ℝ :=
    heightFunctional.comp (rootProjection.comp typeE6RootSpan.subtype)
  have hs (i : typeE6RootPairing_base.support) : h (typeE6RootPairing.root i) = 1 := by
    obtain ⟨i, rfl⟩ := typeE6RootPairing_baseEquiv.surjective i
    exact heightFunctional_simple i
  obtain ⟨f, _, _, hf⟩ := typeE6RootPairing_base.exists_root_eq_sum_int r
  have hh : h (typeE6RootPairing.root r) = (typeE6RootPairing_base.height r : ℝ) := by
    rw [RootPairing.Base.height_eq_sum hf, hf, map_sum, Int.cast_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_zsmul, hs ⟨i, hi⟩]
    simp
  intro hz
  have he : (typeE6RootPairing_base.height r : ℝ) = 0 := by
    rw [← hh]
    change heightFunctional (rootProjection r.val) = 0
    rw [hz, map_zero]
  exact typeE6RootPairing_base.height_ne_zero r (by exact_mod_cast he)

private def orbitLift : Vec 4 →ₗ[ℝ] Vec 8 where
  toFun x := ![x 0, -x 0, -x 0, x 0, x 1 + x 2 + x 3,
    x 1 + x 2 - x 3, x 1 - x 2 + x 3, x 1 - x 2 - x 3]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp <;> ring

private theorem orbitLift_projection (r : typeE6Roots) :
    orbitLift (rootProjection r.val) = r.val + (typeE6DiagramEquiv.indexEquiv r).val := by
  have he : (orbitLift.comp rootProjection).comp typeE6RootSpan.subtype =
      typeE6RootSpan.subtype + typeE6RootSpan.subtype.comp typeE6DiagramEquiv.weightMap := by
    apply typeE6RootPairing_base.toWeightBasis.ext
    intro i
    obtain ⟨i, rfl⟩ := typeE6RootPairing_baseEquiv.surjective i
    simp only [RootPairing.Base.toWeightBasis_apply, LinearMap.comp_apply,
      LinearMap.add_apply, RootPairing.Hom.root_weightMap_apply,
      typeE6DiagramEquiv_simple, typeE6DiagramBasePermutation_numbered]
    change orbitLift (rootProjection (typeE6SimpleRoot i)) =
      typeE6SimpleRoot i + typeE6SimpleRoot (typeE6DiagramPermutation i)
    rw [rootProjection_simple]
    fin_cases i <;> ext j <;> fin_cases j <;>
      norm_num [orbitLift, typeF4SimpleRoot, node, typeE6SimpleRoot,
        typeE8SimpleRoot, typeE6DiagramPermutation, Fin.castSucc, Fin.castAdd, Fin.castLE,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  have hr := LinearMap.congr_fun he (typeE6RootPairing.root r)
  change orbitLift (rootProjection r.val) = r.val +
    (typeE6DiagramEquiv.weightMap (typeE6RootPairing.root r) : Vec 8) at hr
  rw [RootPairing.Hom.root_weightMap_apply] at hr
  exact hr

private theorem fibre_dot_nonpos (r t : typeE6Roots)
    (hp : rootProjection r.val = rootProjection t.val) (hne : r ≠ t) :
    dot r.val t.val ≤ 0 := by
  by_contra! hpos
  have hi : 0 < typeE6RootPairing.pairingIn ℤ r t := by
    have hc := typeE6RootPairing.algebraMap_pairingIn ℤ r t
    rw [typeE6RootPairing_pairing] at hc
    have : (0 : ℝ) < (typeE6RootPairing.pairingIn ℤ r t : ℝ) := by
      change (0 : ℝ) < (algebraMap ℤ ℝ) (typeE6RootPairing.pairingIn ℤ r t)
      rwa [hc]
    exact_mod_cast this
  obtain ⟨u, hu⟩ := typeE6RootPairing.root_sub_root_mem_of_pairingIn_pos hi hne
  have hv : u.val = r.val - t.val := congrArg Subtype.val hu
  exact projection_ne_zero u (by rw [hv, map_sub, hp, sub_self])

private theorem dot_self_pos (x : Vec 8) (hx : x ≠ 0) : 0 < dot x x := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra! h
    exact hx (funext h)
  exact Finset.sum_pos' (fun i _ => mul_self_nonneg (x i))
    ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩

/-- Two actual E6 roots have the same projection only when they belong to the
same orbit of the literal pinned diagram involution. -/
public theorem rootProjection_fibre (r t : typeE6Roots)
    (hp : rootProjection r.val = rootProjection t.val) :
    t = r ∨ t = typeE6DiagramEquiv.indexEquiv r := by
  by_contra! hn
  have h1 := fibre_dot_nonpos t r hp.symm hn.1
  have h2 := fibre_dot_nonpos t (typeE6DiagramEquiv.indexEquiv r)
    (hp.symm.trans (rootProjection_diagram r).symm) hn.2
  have hs : r.val + (typeE6DiagramEquiv.indexEquiv r).val =
      t.val + (typeE6DiagramEquiv.indexEquiv t).val := by
    rw [← orbitLift_projection, ← orbitLift_projection, hp]
  have hne : t.val + (typeE6DiagramEquiv.indexEquiv t).val ≠ 0 := by
    intro hz
    have hq := congrArg rootProjection hz
    rw [map_add, rootProjection_diagram, map_zero] at hq
    apply projection_ne_zero t
    funext i
    have hi := congrFun hq i
    change rootProjection t.val i + rootProjection t.val i = 0 at hi
    change rootProjection t.val i = 0
    linarith
  have hpos := dot_self_pos _ hne
  have hh := congrArg (dot t.val) hs
  simp only [dot, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib] at hpos hh
  have ht := typeE6Root_dot_self t
  have hd := typeE6Root_dot_self (typeE6DiagramEquiv.indexEquiv t)
  have hc := dot_comm t.val (typeE6DiagramEquiv.indexEquiv t).val
  unfold dot at h1 h2 ht hd hc
  linarith

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.LongA2.FixedBlock
