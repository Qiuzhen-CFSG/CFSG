module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.Torus.Coordinates

/-!
# Elementary lifts of the fixed coroot words

The pinned rank-one maps send the usual six-transvection torus word to
the original Geck coroot word. The three arm images commute, so the same
word in the folded roots gives the product h₀(t)h₂(F(t))h₃(F²(t)). The
central word uses a fixed-field parameter. Both are words in the already
constructed elementary root elements, including when q = 2.

Consequently every expanded fixed torus tuple has an actual elementary
lift. No assertion that fixed points commute with generated joins is used.
The equivariance of the four-word product uses only arm commutation.

Source: GLS3 2.3.4(c), 2.3.8(a), and the rank-one words of §2.4
(`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section
open Matrix
open scoped MatrixGroups
namespace Triality.Standard.ConcreteBruhat.TorusCoordinates
open Parabolics
open Theory.AlgebraicGroup.StandardRootSystem

private abbrev upper {F : Type*} [Field F] (t : F) : SL(2, F) :=
  SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) t
private abbrev lower {F : Type*} [Field F] (t : F) : SL(2, F) :=
  SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) t

private def rankOneWeyl {F : Type*} [Field F] (t : F) : SL(2, F) :=
  upper t * lower (-t⁻¹) * upper t
private def rankOneTorus {F : Type*} [Field F] (t : Fˣ) : SL(2, F) :=
  rankOneWeyl t.val * rankOneWeyl (-1)

private theorem map_transvection {F K : Type*} [Field F] [Field K]
    (f : F →+* K) {i j : Fin 2} (hij : i ≠ j) (t : F) :
    SpecialLinearGroup.map f (SpecialLinearGroup.transvection hij t) =
      SpecialLinearGroup.transvection hij (f t) := by
  apply Subtype.ext
  change Matrix.map (1 + Matrix.single i j t) f = 1 + Matrix.single i j (f t)
  ext a b
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, map_add]
  split_ifs <;> simp only [map_one, map_zero]

private theorem map_rankOneTorus {F K : Type*} [Field F] [Field K]
    (f : F →+* K) (t : Fˣ) :
    SpecialLinearGroup.map f (rankOneTorus t) =
      rankOneTorus (Units.map f.toMonoidHom t) := by
  simp only [rankOneTorus, rankOneWeyl, map_mul, upper, lower, map_transvection,
    map_neg, map_inv₀, map_one, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe]

private theorem pinned_torus (P : Parameters) (D : PinnedRankOneMaps P)
    (i : Fin 4) (t : (ExtensionField P)ˣ) :
    D.hom i (rankOneTorus t) = torusWord P i t := by
  simp only [rankOneTorus, rankOneWeyl, map_mul, upper, lower,
    D.positive, D.negative, torusWord, weylWord]

/-- Orthogonal arm coroots commute, by the proved pinned rank-one images. -/
theorem commute_arm_torusWord (P : Parameters) (hp : P.prime = 2)
    (i j : Fin 4) (hi : i ≠ 1) (hj : j ≠ 1) (hij : i ≠ j)
    (t u : (ExtensionField P)ˣ) : Commute (torusWord P i t) (torusWord P j u) := by
  let D := pinnedRankOneMaps P hp
  rw [← pinned_torus P D i t, ← pinned_torus P D j u]
  exact D.commute (armRootCommutation P hp) i j hi hj hij _ _

/-- The actual graph-field action on the four coroot coordinates. -/
theorem graphField_product (P : Parameters) (hp : P.prime = 2) (a : Coordinates P) :
    graphFieldAutomorphism P (product P a) = product P (twist P a) := by
  simp only [product, map_mul, graphField_torusWord]
  change torusWord P 2 (frobenius P (a 0)) * torusWord P 3 (frobenius P (a 2)) *
      torusWord P 0 (frobenius P (a 3)) * torusWord P 1 (frobenius P (a 1)) =
    torusWord P 0 (frobenius P (a 3)) * torusWord P 2 (frobenius P (a 0)) *
      torusWord P 3 (frobenius P (a 2)) * torusWord P 1 (frobenius P (a 1))
  rw [((commute_arm_torusWord P hp 0 2 (by decide) (by decide) (by decide) _ _).mul_right
    (commute_arm_torusWord P hp 0 3 (by decide) (by decide) (by decide) _ _)).symm.eq]
  simp only [mul_assoc]

private def foldedMap (P : Parameters) (hp : P.prime = 2) :
    (a : Node) → SL(2, RootField P a) →* SplitGroup P
  | .arms => (pinnedRankOneMaps P hp).armsFixedEmbedding (armRootCommutation P hp)
  | .central => ((pinnedRankOneMaps P hp).hom 1).comp
      (SpecialLinearGroup.map (fixedField P).subtype)

private theorem foldedMap_positive (P : Parameters) (hp : P.prime = 2)
    (a : Node) (t : RootField P a) :
    foldedMap P hp a (upper t) = elementaryInclusion P (rootElementary P hp true a t) := by
  cases a with
  | central =>
    change (pinnedRankOneMaps P hp).hom 1
      (SpecialLinearGroup.map (fixedField P).subtype (upper t)) = positiveRoot P 1 t.val
    rw [upper, map_transvection, (pinnedRankOneMaps P hp).positive]
    rfl
  | arms =>
    change (pinnedRankOneMaps P hp).hom 0 (upper t) *
      (pinnedRankOneMaps P hp).hom 2 (SpecialLinearGroup.map (fieldFrobenius P).toRingHom (upper t)) *
      (pinnedRankOneMaps P hp).hom 3 (SpecialLinearGroup.map (fieldFrobenius P).toRingHom
        (SpecialLinearGroup.map (fieldFrobenius P).toRingHom (upper t))) = _
    simp only [upper, map_transvection, (pinnedRankOneMaps P hp).positive]
    rfl

private theorem foldedMap_negative (P : Parameters) (hp : P.prime = 2)
    (a : Node) (t : RootField P a) :
    foldedMap P hp a (lower t) = elementaryInclusion P (rootElementary P hp false a t) := by
  cases a with
  | central =>
    change (pinnedRankOneMaps P hp).hom 1
      (SpecialLinearGroup.map (fixedField P).subtype (lower t)) = negativeRoot P 1 t.val
    rw [lower, map_transvection, (pinnedRankOneMaps P hp).negative]
    rfl
  | arms =>
    change (pinnedRankOneMaps P hp).hom 0 (lower t) *
      (pinnedRankOneMaps P hp).hom 2 (SpecialLinearGroup.map (fieldFrobenius P).toRingHom (lower t)) *
      (pinnedRankOneMaps P hp).hom 3 (SpecialLinearGroup.map (fieldFrobenius P).toRingHom
        (SpecialLinearGroup.map (fieldFrobenius P).toRingHom (lower t))) = _
    simp only [lower, map_transvection, (pinnedRankOneMaps P hp).negative]
    rfl

/-- The rank-one Weyl word in elementary folded roots, for any parameter. -/
def foldedWeylElementary (P : Parameters) (hp : P.prime = 2)
    (a : Node) (t : RootField P a) : ElementaryGroup P :=
  rootElementary P hp true a t * rootElementary P hp false a (-t⁻¹) *
    rootElementary P hp true a t

/-- The six-root coroot word inside the actual elementary group. -/
def foldedTorusElementary (P : Parameters) (hp : P.prime = 2)
    (a : Node) (t : (RootField P a)ˣ) : ElementaryGroup P :=
  foldedWeylElementary P hp a t.val * foldedWeylElementary P hp a (-1)

private theorem foldedMap_torus (P : Parameters) (hp : P.prime = 2)
    (a : Node) (t : (RootField P a)ˣ) :
    foldedMap P hp a (rankOneTorus t) =
      elementaryInclusion P (foldedTorusElementary P hp a t) := by
  simp only [rankOneTorus, rankOneWeyl, map_mul, foldedMap_positive, foldedMap_negative,
    foldedTorusElementary, foldedWeylElementary]

theorem inclusion_foldedTorus_arms (P : Parameters) (hp : P.prime = 2)
    (t : (ExtensionField P)ˣ) :
    elementaryInclusion P (foldedTorusElementary P hp .arms t) =
      torusWord P 0 t * torusWord P 2 (frobenius P t) *
        torusWord P 3 (frobenius P (frobenius P t)) := by
  rw [← foldedMap_torus]
  change (pinnedRankOneMaps P hp).hom 0 (rankOneTorus t) *
    (pinnedRankOneMaps P hp).hom 2
      (SpecialLinearGroup.map (fieldFrobenius P).toRingHom (rankOneTorus t)) *
    (pinnedRankOneMaps P hp).hom 3
      (SpecialLinearGroup.map (fieldFrobenius P).toRingHom
        (SpecialLinearGroup.map (fieldFrobenius P).toRingHom (rankOneTorus t))) = _
  simp only [map_rankOneTorus, pinned_torus, frobenius]

theorem inclusion_foldedTorus_central (P : Parameters) (hp : P.prime = 2)
    (t : (fixedField P)ˣ) :
    elementaryInclusion P (foldedTorusElementary P hp .central t) =
      torusWord P 1 (fixedUnit P t) := by
  rw [← foldedMap_torus]
  change (pinnedRankOneMaps P hp).hom 1
    (SpecialLinearGroup.map (fixedField P).subtype (rankOneTorus t)) = _
  rw [map_rankOneTorus, pinned_torus]
  rfl

/-- An explicit lift of every orbit tuple, using two folded six-root words. -/
def orbitElementary (P : Parameters) (hp : P.prime = 2) (a : OrbitParameters P) :
    ElementaryGroup P :=
  foldedTorusElementary P hp .arms a.1 * foldedTorusElementary P hp .central a.2

theorem inclusion_orbitElementary (P : Parameters) (hp : P.prime = 2)
    (a : OrbitParameters P) :
    elementaryInclusion P (orbitElementary P hp a) = product P (expand P a) := by
  simp only [orbitElementary, map_mul, inclusion_foldedTorus_arms,
    inclusion_foldedTorus_central]
  rfl

/-- Once product faithfulness is known, its fixed points are exactly the fixed tuples. -/
theorem product_fixed_iff (P : Parameters) (hp : P.prime = 2)
    (hinj : Function.Injective (product P)) (a : Coordinates P) :
    product P a ∈ fixedSubgroup P ↔ twist P a = a := by
  rw [mem_fixedSubgroup, graphField_product P hp]
  exact hinj.eq_iff

/-- Restriction to elementary points loses no torus elements, once the matrix
parametrization is known to be faithful and exhaustive. -/
theorem fixedTorus_le_elementary_of_coordinates (P : Parameters) (hp : P.prime = 2)
    (hinj : Function.Injective (product P))
    (hrange : Set.range (product P) = (splitTorus P : Set (SplitGroup P))) :
    (splitTorus P).comap (fixedSubgroup P).subtype ≤ elementarySubgroup P := by
  intro g hg
  have hg' : g.val ∈ Set.range (product P) := by rw [hrange]; exact hg
  obtain ⟨a, ha⟩ := hg'
  have hfix : twist P a = a := (product_fixed_iff P hp hinj a).mp (by
    rw [ha]
    exact g.property)
  let b := (fixedCoordinatesEquiv P).symm ⟨a, hfix⟩
  have hb : expand P b = a := congrArg Subtype.val
    ((fixedCoordinatesEquiv P).apply_symm_apply ⟨a, hfix⟩)
  have he : (orbitElementary P hp b).val = g := by
    apply Subtype.ext
    exact (inclusion_orbitElementary P hp b).trans ((congrArg (product P) hb).trans ha)
  exact he ▸ (orbitElementary P hp b).property

end Triality.Standard.ConcreteBruhat.TorusCoordinates
