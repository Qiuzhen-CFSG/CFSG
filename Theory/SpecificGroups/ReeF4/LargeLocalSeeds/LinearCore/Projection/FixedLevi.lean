module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.LinearLeviGeneration
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.LinearQuotient

/-!
# The fixed end-node Levi as PSL₂ over the Ree coefficient field

The faithful long-root SL₂ representation and its image under the supplied
Ree twist commute. Their intersection is trivial because SL₂ has trivial
center in characteristic two. Their product is therefore faithful, and its
diagonal gives an injective map into the fixed group. The proved generation
of the entire fixed Levi by the signed fixed blocks gives surjectivity.
Composing with the characteristic-two SL₂–PSL₂ comparison identifies the
actual fixed Levi, including its torus, with the requested projective group.

The commuting-factor argument follows the private matrix calculation in
`FixedCollection/SeedGeneration/LinearLeviGeneration.lean`; the full fixed
Levi generation theorem from that module is reused without changing its API.
Source: GLS3 §§2.3–2.4, Table 2.4 type VI, and Aschbacher–Smith F.1.12(I)(5),
printed p.263 of `refs/quasithin.pdf`.
-/

public noncomputable section
namespace ReeF4.LargeLocalSeeds.LinearProjection
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open Parabolics Parabolics.Binary.FixedGeometry
open LocalBlockInput.PairRigidity
open LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
open BlockParameters.FieldRecovery RootPairing.IntegralGeckConstruction
private local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
variable {m : ℕ}

private theorem linearSL_induction {P : LinearSL m → Prop}
    (hroot : ∀ p t, P (linearSLRoot m p t))
    (hmul : ∀ a b, P a → P b → P (a * b)) (g : LinearSL m) : P g := by
  apply Matrix.SL2.transvection_induction P ?_ hmul g
  intro i j hij t
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact hroot true t
  · exact hroot false t
  · exact (hij rfl).elim

private theorem pinned_root (C : LinearLongRootMap m) (p : Bool) (t : CoefficientField m) :
    C.hom (linearSLRoot m p t) =
      rootGeneratorInGroup m (signedRoot p (typeF4SimpleRootIndex 0)) t := by
  cases p
  · exact C.negative t
  · exact C.positive t

private def otherHom (d : LocalBlockInput m) (C : LinearLongRootMap m) :
    LinearSL m →* SplitGroup m := d.twist.toMonoidHom.comp C.hom

private theorem otherHom_root (d : LocalBlockInput m) (C : LinearLongRootMap m)
    (p : Bool) (t : CoefficientField m) :
    otherHom d C (linearSLRoot m p t) =
      rootGeneratorInGroup m (signedRoot p (typeF4SimpleRootIndex 3))
        (rootFieldEnd m (typeF4SimpleRootIndex 0) t) := by
  change d.twist (C.hom (linearSLRoot m p t)) = _
  rw [pinned_root, d.twist_root, ← rootFieldEnd_apply]
  cases p <;> simp only [signedRoot, Bool.false_eq_true, ↓reduceIte,
    exceptionalRootPermutation_simple, exceptionalRootPermutation_neg_simple, rootFieldEnd_neg] <;> rfl

private theorem end_commute (p q : Bool) (t u : CoefficientField m) :
    Commute (rootGeneratorInGroup m (signedRoot p (typeF4SimpleRootIndex 0)) t)
      (rootGeneratorInGroup m (signedRoot q (typeF4SimpleRootIndex 3)) u) := by
  have hne : typeF4RootPairing_baseEquiv 0 ≠ typeF4RootPairing_baseEquiv 3 := by
    intro h
    have := typeF4RootPairing_baseEquiv.injective h
    contradiction
  have hc : typeF4RootPairing_base.cartanMatrix
      (typeF4RootPairing_baseEquiv 3) (typeF4RootPairing_baseEquiv 0) = 0 := by
    rw [typeF4RootPairing_base_cartan_apply]
    norm_num [typeF4CartanMatrix, Fin.ext_iff]
  apply Subtype.ext
  cases p <;> cases q
  all_goals
    simp only [signedRoot, Bool.false_eq_true, ↓reduceIte]
    change F4Chevalley.rootCurve _ t * F4Chevalley.rootCurve _ u =
      F4Chevalley.rootCurve _ u * F4Chevalley.rootCurve _ t
    simp only [F4Chevalley.rootCurve, F4Chevalley.integralOperators,
      ← typeF4RootPairing_baseEquiv_val, rootCurveUnit_simple, rootCurveUnit_neg_simple]
  · exact congrArg Subtype.val
      (RootPairing.SimpleGeckGroup.commute_negative_negative_of_cartan_eq_zero _ _ hne hc t u).eq
  · exact congrArg Subtype.val
      (RootPairing.SimpleGeckGroup.commute_positive_negative _ _ hne.symm u t).eq.symm
  · exact congrArg Subtype.val
      (RootPairing.SimpleGeckGroup.commute_positive_negative _ _ hne t u).eq
  · exact congrArg Subtype.val
      (RootPairing.SimpleGeckGroup.commute_positive_positive_of_cartan_eq_zero _ _ hne hc t u).eq

private theorem factors_commute (d : LocalBlockInput m) (C : LinearLongRootMap m)
    (x y : LinearSL m) : Commute (C.hom x) (otherHom d C y) := by
  induction x using linearSL_induction with
  | hroot p t =>
    induction y using linearSL_induction with
    | hroot q u => rw [pinned_root, otherHom_root]; exact end_commute p q t _
    | hmul a b ha hb => rw [map_mul]; exact ha.mul_right hb
  | hmul a b ha hb => rw [map_mul]; exact ha.mul_left hb

private theorem factors_disjoint (d : LocalBlockInput m) (C : LinearLongRootMap m) :
    Disjoint C.hom.range (otherHom d C).range := by
  apply Subgroup.disjoint_def.mpr
  rintro g ⟨x, rfl⟩ ⟨y, hy⟩
  have hx : x ∈ Subgroup.center (LinearSL m) := by
    rw [Subgroup.mem_center_iff]
    intro z
    apply C.injective
    simp only [map_mul]
    rw [← hy]
    exact (factors_commute d C z y).eq
  have hx1 : x = 1 := by
    simpa only [Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot, Subgroup.mem_bot] using hx
  simp [hx1]

private def pairHom (d : LocalBlockInput m) (C : LinearLongRootMap m) :
    LinearSL m × LinearSL m →* SplitGroup m :=
  C.hom.noncommCoprod (otherHom d C) (factors_commute d C)

private theorem pairHom_injective (d : LocalBlockInput m) (C : LinearLongRootMap m) :
    Function.Injective (pairHom d C) :=
  (MonoidHom.noncommCoprod_injective _ _ _).mpr
    ⟨C.injective, d.twist.injective.comp C.injective, factors_disjoint d C⟩

private theorem pairHom_twist (d : LocalBlockInput m) (C : LinearLongRootMap m)
    (x y : LinearSL m) : d.twist (pairHom d C (x, y)) = pairHom d C (y, x) := by
  change d.twist (C.hom x * d.twist (C.hom y)) = C.hom y * d.twist (C.hom x)
  have hs : d.twist (d.twist (C.hom y)) = C.hom y := DFunLike.congr_fun d.twist_sq _
  rw [map_mul, hs]
  exact (factors_commute d C y x).symm.eq

private theorem diagonal_fixed (d : LocalBlockInput m) (C : LinearLongRootMap m)
    (g : LinearSL m) : d.twist (pairHom d C (g, g)) = pairHom d C (g, g) :=
  pairHom_twist d C g g

private def diagonalHom (d : LocalBlockInput m) (C : LinearLongRootMap m) :
    LinearSL m →* d.fixedGroup where
  toFun g := ⟨pairHom d C (g, g), diagonal_fixed d C g⟩
  map_one' := Subtype.ext ((pairHom d C).map_one)
  map_mul' g h := Subtype.ext ((pairHom d C).map_mul (g, g) (h, h))

private theorem diagonalHom_root (d : LocalBlockInput m) (C : LinearLongRootMap m)
    (p : Bool) (t : CoefficientField m) :
    diagonalHom d C (linearSLRoot m p t) = linearElement d p t := by
  apply Subtype.ext
  change C.hom (linearSLRoot m p t) * otherHom d C (linearSLRoot m p t) = _
  rw [pinned_root, otherHom_root]
  cases p
  · exact (linearElement_negative d t).symm
  · exact (linearElement_positive d t).symm


private theorem diagonalHom_mem (d : LocalBlockInput m) (C : LinearLongRootMap m)
    (g : LinearSL m) : diagonalHom d C g ∈ fixedLevi d .linear := by
  induction g using linearSL_induction with
  | hroot p t =>
    rw [diagonalHom_root]
    exact simpleBlock_le_fixedLevi d .linear p (linearElement_mem d p t)
  | hmul a b ha hb => rw [map_mul]; exact mul_mem ha hb

private def diagonalLeviHom (d : LocalBlockInput m) (C : LinearLongRootMap m) :
    LinearSL m →* fixedLevi d .linear :=
  (diagonalHom d C).codRestrict _ (diagonalHom_mem d C)

private theorem diagonalLeviHom_bijective (d : LocalBlockInput m)
    (C : LinearLongRootMap m) : Function.Bijective (diagonalLeviHom d C) := by
  constructor
  · intro a b hab
    have h : pairHom d C (a, a) = pairHom d C (b, b) :=
      congrArg (fun x => x.val.val) hab
    exact congrArg Prod.fst (pairHom_injective d C h)
  · intro x
    have hblock (p : Bool) : simpleBlock d .linear p ≤ (diagonalHom d C).range := by
      intro g hg
      obtain ⟨t, rfl⟩ := linearElement_surjective d p hg
      exact ⟨linearSLRoot m p t, diagonalHom_root d C p t⟩
    obtain ⟨g, hg⟩ := (sup_le (hblock true) (hblock false))
      (fixedLevi_linear_le_signed_of_longRootMap d C x.property)
    exact ⟨g, Subtype.ext hg⟩

/-- The actual fixed Levi is SL₂, via the diagonal of the two commuting,
faithfully represented end-node factors exchanged by the supplied twist. -/
def fixedLeviEquivSL (hm : 1 ≤ m) (d : LocalBlockInput m) :
    fixedLevi d .linear ≃* LinearSL m :=
  (MulEquiv.ofBijective (diagonalLeviHom d (linearLongRootMap m hm))
    (diagonalLeviHom_bijective d (linearLongRootMap m hm))).symm

/-- The actual fixed end-node Levi is the project's PSL₂ over precisely
`CoefficientField m`; characteristic two makes the central quotient injective. -/
def fixedLeviEquivPSL (hm : 1 ≤ m) (d : LocalBlockInput m) :
    fixedLevi d .linear ≃* LinearQuotient m :=
  (fixedLeviEquivSL hm d).trans
    (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := CoefficientField m))

end ReeF4.LargeLocalSeeds.LinearProjection
