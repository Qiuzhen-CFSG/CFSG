module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.Levi
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.LinearLeviGeneration.Pinned
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.LinearLeviGeneration.LongRootMatrices
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.LinearCoordinates
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Fixed end-node Levi generation

The two end-root factors commute. A faithful pinned map from SL₂ to node 0,
followed by the supplied twist, gives the other factor. The trivial center of
SL₂ in characteristic two makes their product injective. The signed root
support of the full split Levi proves product coverage; uniqueness then forces
its fixed elements to have equal coordinates in these two factors. SL₂
transvection generation therefore covers the entire fixed Levi, including its
torus, by the two actual signed fixed blocks.

Independently of that comparison, the specified Weyl word `[0,3]` is the
three-factor word in the parameter-one signed fixed roots. It conjugates the
positive fixed block onto the negative one. Thus the signed-block join equals
the join of the positive block and this exact Weyl representative.

The matrix comparison is constructed in `LongRootMatrices` on the full
52-dimensional F₄ lattice. Instantiating it proves the final inclusion and
equality from `1 ≤ m` and `LocalBlockInput m` alone. The intermediate theorems
retain their explicit `LinearLongRootMap m` input; fixed-point descent uses
the injective product comparison rather than split generation alone.
Source: GLS3, 2.3.4–8 and §2.4, especially Table 2.4 type VI,
`refs/KGroup/GLS3/chapter2.tex`. The Weyl calculation agrees with the literal
parameter-one word in `LocalIndices.LinearCover.RankOne`.
-/

public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open LargeLocalSeeds Parabolics Parabolics.Binary.FixedGeometry
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

private theorem splitLevi_le_pairHom (d : LocalBlockInput m) (C : LinearLongRootMap m) :
    splitLevi m .linear ≤ (pairHom d C).range := by
  have h0 (p : Bool) (t : CoefficientField m) :
      rootGeneratorInGroup m (signedRoot p (typeF4SimpleRootIndex 0)) t ∈
        (pairHom d C).range := by
    refine ⟨(linearSLRoot m p t, 1), ?_⟩
    change C.hom (linearSLRoot m p t) * otherHom d C 1 = _
    rw [map_one, mul_one, pinned_root]
  have h3 (p : Bool) (t : CoefficientField m) :
      rootGeneratorInGroup m (signedRoot p (typeF4SimpleRootIndex 3)) t ∈
        (pairHom d C).range := by
    refine ⟨(1, linearSLRoot m p (rootFieldEnd m (typeF4SimpleRootIndex 3) t)), ?_⟩
    change C.hom 1 * otherHom d C (linearSLRoot m p _) = _
    rw [map_one, one_mul, otherHom_root]
    have h := RadicalCoordinates.rootFieldEnd_twice m (typeF4SimpleRootIndex 3) t
    rw [exceptionalRootPermutation_simple] at h
    change rootFieldEnd m (typeF4SimpleRootIndex 0)
      (rootFieldEnd m (typeF4SimpleRootIndex 3) t) = t at h
    rw [h]
  have hblock (p : Bool) : splitSimpleBlock m .linear p ≤ (pairHom d C).range := by
    apply (closure_le _).mpr
    rintro _ ⟨r, t, hr, rfl⟩
    obtain ⟨i, hi, hri⟩ := BinaryLinear.isLeviRoot_of_middle_coefficients_zero r
      (hr.1 1 (by simp [leviNodes])) (hr.1 2 (by simp [leviNodes]))
    have hi' : i = 0 ∨ i = 3 := by simpa [leviNodes] using hi
    rcases hi' with rfl | rfl <;> rcases hri with rfl | rfl
    · exact h0 true t
    · exact h0 false t
    · exact h3 true t
    · exact h3 false t
  exact sup_le (hblock true) (hblock false)

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

private theorem fixedLevi_linear_le_diagonal (d : LocalBlockInput m) (C : LinearLongRootMap m) :
    fixedLevi d .linear ≤ (diagonalHom d C).range := by
  intro g hg
  obtain ⟨⟨a, b⟩, hab⟩ := splitLevi_le_pairHom d C hg
  have hswap : pairHom d C (b, a) = pairHom d C (a, b) := by
    rw [← pairHom_twist, hab]
    exact g.property
  have hba : b = a := congrArg Prod.fst (pairHom_injective d C hswap)
  subst b
  exact ⟨a, Subtype.ext hab⟩

/-- A pinned faithful matrix comparison gives generation of the whole fixed
Levi by both signed fixed blocks. The proof includes every fixed torus element. -/
theorem fixedLevi_linear_le_signed_of_longRootMap
    (d : LocalBlockInput m) (C : LinearLongRootMap m) :
    fixedLevi d .linear ≤ simpleBlock d .linear true ⊔ simpleBlock d .linear false := by
  intro g hg
  obtain ⟨a, rfl⟩ := fixedLevi_linear_le_diagonal d C hg
  clear hg
  induction a using linearSL_induction with
  | hroot p t =>
    rw [diagonalHom_root]
    cases p
    · exact mem_sup_right (linearElement_mem d false t)
    · exact mem_sup_left (linearElement_mem d true t)
  | hmul a b ha hb => rw [map_mul]; exact mul_mem ha hb

/-- The prescribed `[0,3]` representative is literally the paired rank-one
word at parameter one, as in `LocalIndices.linearPanelWeyl`. -/
theorem relativeWeyl_linear_eq_rootWord (d : LocalBlockInput m) :
    relativeWeyl d .linear =
      linearElement d true 1 * linearElement d false 1 * linearElement d true 1 := by
  apply Subtype.ext
  simp only [relativeWeyl_val, sideWord, simpleWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, Subgroup.coe_mul, linearElement_positive,
    linearElement_negative, linearSplitWord, weylWord, inv_one, map_one, CharTwo.neg_eq]
  have h1 := (end_commute (m := m) false true 1 1).symm
  have h2 := (end_commute (m := m) true false 1 1).symm
  have h3 := (end_commute (m := m) true true 1 1).symm
  simp only [signedRoot, Bool.false_eq_true, ↓reduceIte] at h1 h2 h3
  symm
  simp only [mul_assoc]
  rw [h1.left_comm, h2.left_comm, h3.left_comm]

/-- Conjugation by the prescribed relative Weyl word preserves the parameter
and changes the sign of the actual type VI root element. -/
theorem relativeWeyl_linear_conj_positive (d : LocalBlockInput m) (t : CoefficientField m) :
    relativeWeyl d .linear * linearElement d true t * (relativeWeyl d .linear)⁻¹ =
      linearElement d false t := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, linearElement_positive,
    linearElement_negative, linearSplitWord]
  rw [show ∀ w x y : SplitGroup m, w * (x * y) * w⁻¹ =
      (w * x * w⁻¹) * (w * y * w⁻¹) from fun w x y => by group]
  rw [relativeWeyl_conj_block_root d .linear true _ _
      (isSimpleBlockRoot_simple .linear 0 (by simp [leviNodes])),
    relativeWeyl_conj_block_root d .linear true _ _
      (isSimpleBlockRoot_simple .linear 3 (by simp [leviNodes]))]
  rfl

/-- The exact relative Weyl representative belongs to the signed-block join. -/
theorem relativeWeyl_linear_mem_signed (d : LocalBlockInput m) :
    relativeWeyl d .linear ∈ simpleBlock d .linear true ⊔ simpleBlock d .linear false := by
  rw [relativeWeyl_linear_eq_rootWord]
  exact mul_mem (mul_mem (mem_sup_left (linearElement_mem d true _))
    (mem_sup_right (linearElement_mem d false _))) (mem_sup_left (linearElement_mem d true _))

/-- The entire negative fixed block is generated by the positive block and
the prescribed relative Weyl word; no rank-one matrix comparison is needed. -/
theorem linear_negative_le_positive_weyl (d : LocalBlockInput m) :
    simpleBlock d .linear false ≤
      simpleBlock d .linear true ⊔ Subgroup.zpowers (relativeWeyl d .linear) := by
  intro g hg
  obtain ⟨t, rfl⟩ := linearElement_surjective d false hg
  rw [← relativeWeyl_linear_conj_positive]
  have hw : relativeWeyl d .linear ∈
      simpleBlock d .linear true ⊔ Subgroup.zpowers (relativeWeyl d .linear) :=
    mem_sup_right (Subgroup.mem_zpowers _)
  exact mul_mem (mul_mem hw (mem_sup_left (linearElement_mem d true t))) (inv_mem hw)

/-- The two descriptions of the generated rank-one subgroup agree
unconditionally. This does not yet identify it with the full fixed Levi. -/
theorem linear_signed_eq_positive_weyl (d : LocalBlockInput m) :
    simpleBlock d .linear true ⊔ simpleBlock d .linear false =
      simpleBlock d .linear true ⊔ Subgroup.zpowers (relativeWeyl d .linear) := by
  apply le_antisymm
  · exact sup_le le_sup_left (linear_negative_le_positive_weyl d)
  · exact sup_le le_sup_left ((Subgroup.zpowers_le).mpr (relativeWeyl_linear_mem_signed d))

/-- The required Levi inclusion, conditional only on constructing the pinned
faithful SL₂ comparison at the long end node. -/
theorem fixedLevi_linear_le_of_longRootMap (d : LocalBlockInput m) (C : LinearLongRootMap m) :
    fixedLevi d .linear ≤
      simpleBlock d .linear true ⊔ Subgroup.zpowers (relativeWeyl d .linear) := by
  rw [← linear_signed_eq_positive_weyl]
  exact fixedLevi_linear_le_signed_of_longRootMap d C

/-- The conditional argument identifies the full fixed intersection, not just
a subgroup generated by unipotent elements; in particular it retains its torus. -/
theorem fixedLevi_linear_eq_positive_weyl_of_longRootMap
    (d : LocalBlockInput m) (C : LinearLongRootMap m) :
    fixedLevi d .linear =
      simpleBlock d .linear true ⊔ Subgroup.zpowers (relativeWeyl d .linear) := by
  apply le_antisymm (fixedLevi_linear_le_of_longRootMap d C)
  rw [← linear_signed_eq_positive_weyl]
  exact sup_le (Subgroup.comap_mono le_sup_left) (Subgroup.comap_mono le_sup_right)

/-- The entire fixed end-node Levi, including its torus, is generated by the
positive fixed block and the prescribed `[0,3]` Weyl representative. -/
theorem fixedLevi_linear_le (hm : 1 ≤ m) (d : LocalBlockInput m) :
    fixedLevi d .linear ≤
      simpleBlock d .linear true ⊔ Subgroup.zpowers (relativeWeyl d .linear) :=
  fixedLevi_linear_le_of_longRootMap d (linearLongRootMap m hm)

/-- The positive block and the prescribed Weyl representative generate exactly
the actual fixed intersection of the full split end-node Levi. -/
theorem fixedLevi_linear_eq_positive_weyl (hm : 1 ≤ m) (d : LocalBlockInput m) :
    fixedLevi d .linear =
      simpleBlock d .linear true ⊔ Subgroup.zpowers (relativeWeyl d .linear) :=
  fixedLevi_linear_eq_positive_weyl_of_longRootMap d (linearLongRootMap m hm)

end ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
