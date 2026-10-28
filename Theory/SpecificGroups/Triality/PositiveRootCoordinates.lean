module

public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Curves
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Collection
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.GraphField
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Injectivity
public import Mathlib.GroupTheory.PGroup

/-!
# Positive-root coordinates for the genuine binary triality subgroup

The scalar coordinates and integral Geck curves are constructed in the imported
modules. An injective ordered product with image the existing positive-simple
subgroup gives that subgroup order q^36, hence makes it a p-group. If the product
also intertwines the actual graph-field automorphism with the scalar twist,
restriction gives the full positive fixed subgroup order q^12.

The binary specialization discharges all three matrix inputs with the imported
collection, uniqueness, and graph-field theorems. It gives the actual positive
subgroup a unique twelve-root normal form. The fixed-coordinate equivalence
then gives three GF(q³) parameters and three q-Frobenius fixed-field parameters,
so the full positive fixed subgroup has order q^12, also when q = 2.
No central quotient or elementary restriction is taken in this count.

Source: GLS3, 2.3.6–8 and §§2.4–2.6 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section

namespace Triality.Standard.PositiveCoordinates
noncomputable section

/-- Restrict a proved matrix normal form to the existing positive subgroup. -/
def positiveEquivOfNormalForm (P : Parameters)
    (hinj : Function.Injective (orderedProduct P))
    (himage : Set.range (orderedProduct P) = (Parabolics.positiveSubgroup P : Set (SplitGroup P))) :
    Coordinates P ≃ Parabolics.positiveSubgroup P :=
  Equiv.ofBijective
    (fun a => ⟨orderedProduct P a, by
      change orderedProduct P a ∈ (Parabolics.positiveSubgroup P : Set (SplitGroup P))
      rw [← himage]
      exact Set.mem_range_self a⟩)
    ⟨fun a b h => hinj (congrArg Subtype.val h), by
      intro g
      have hg : g.val ∈ Set.range (orderedProduct P) := by
        rw [himage]
        exact g.property
      obtain ⟨a, ha⟩ := hg
      exact ⟨a, Subtype.ext ha⟩⟩

theorem card_positiveSubgroup_of_normalForm (P : Parameters)
    (hinj : Function.Injective (orderedProduct P))
    (himage : Set.range (orderedProduct P) = (Parabolics.positiveSubgroup P : Set (SplitGroup P))) :
    Nat.card (Parabolics.positiveSubgroup P) = P.q ^ 36 := by
  rw [← Nat.card_congr (positiveEquivOfNormalForm P hinj himage)]
  exact card_coordinates P

theorem isPGroup_positiveSubgroup_of_normalForm (P : Parameters)
    (hinj : Function.Injective (orderedProduct P))
    (himage : Set.range (orderedProduct P) = (Parabolics.positiveSubgroup P : Set (SplitGroup P))) :
    IsPGroup P.prime (Parabolics.positiveSubgroup P) := by
  apply IsPGroup.of_card (n := P.exponent * 36)
  rw [card_positiveSubgroup_of_normalForm P hinj himage, Parameters.q, pow_mul]

/-- Restrict an equivariant normal form to the full graph-field fixed subgroup. -/
def fixedPositiveEquivOfNormalForm (P : Parameters)
    (hinj : Function.Injective (orderedProduct P))
    (himage : Set.range (orderedProduct P) = (Parabolics.positiveSubgroup P : Set (SplitGroup P)))
    (htwist : ∀ a, graphFieldAutomorphism P (orderedProduct P a) = orderedProduct P (twist P a)) :
    FixedCoordinates P ≃ (Parabolics.positiveSubgroup P).comap (fixedSubgroup P).subtype := by
  let f : FixedCoordinates P →
      (Parabolics.positiveSubgroup P).comap (fixedSubgroup P).subtype := fun a =>
    ⟨⟨orderedProduct P a.1, by
      rw [mem_fixedSubgroup, htwist, a.2]⟩,
      by
        change orderedProduct P a.1 ∈ (Parabolics.positiveSubgroup P : Set (SplitGroup P))
        rw [← himage]
        exact Set.mem_range_self a.1⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b h
    apply Subtype.ext
    apply hinj
    exact congrArg (fun x : (Parabolics.positiveSubgroup P).comap (fixedSubgroup P).subtype =>
      x.val.val) h
  · intro g
    have hg : g.val.val ∈ Set.range (orderedProduct P) := by
      rw [himage]
      exact g.property
    obtain ⟨a, ha⟩ := hg
    have hfix : twist P a = a := by
      apply hinj
      calc
        orderedProduct P (twist P a) = graphFieldAutomorphism P (orderedProduct P a) :=
          (htwist a).symm
        _ = graphFieldAutomorphism P g.val.val := congrArg (graphFieldAutomorphism P) ha
        _ = g.val.val := g.val.property
        _ = orderedProduct P a := ha.symm
    exact ⟨⟨a, hfix⟩, Subtype.ext (Subtype.ext ha)⟩

theorem card_fixedPositive_of_normalForm (P : Parameters)
    (hinj : Function.Injective (orderedProduct P))
    (himage : Set.range (orderedProduct P) = (Parabolics.positiveSubgroup P : Set (SplitGroup P)))
    (htwist : ∀ a, graphFieldAutomorphism P (orderedProduct P a) = orderedProduct P (twist P a)) :
    Nat.card ((Parabolics.positiveSubgroup P).comap (fixedSubgroup P).subtype) = P.q ^ 12 := by
  rw [← Nat.card_congr (fixedPositiveEquivOfNormalForm P hinj himage htwist)]
  exact card_fixedCoordinates P

/-- The actual ordered product parametrizes the binary positive subgroup bijectively. -/
def positiveEquiv_binary (n : ℕ) (hn : 0 < n) :
    Coordinates (binaryParameters n hn) ≃ Parabolics.positiveSubgroup (binaryParameters n hn) :=
  positiveEquivOfNormalForm (binaryParameters n hn)
    (orderedProduct_injective_binary n hn) (range_orderedProduct_binary n hn)

@[simp] theorem positiveEquiv_binary_val (n : ℕ) (hn : 0 < n)
    (a : Coordinates (binaryParameters n hn)) :
    (positiveEquiv_binary n hn a).val = orderedProduct (binaryParameters n hn) a := rfl

/-- Existence and uniqueness of all twelve parameters in the positive subgroup. -/
theorem existsUnique_orderedProduct_binary (n : ℕ) (hn : 0 < n)
    (g : Parabolics.positiveSubgroup (binaryParameters n hn)) :
    ∃! a : Coordinates (binaryParameters n hn), orderedProduct (binaryParameters n hn) a = g.val := by
  have hg : g.val ∈ Set.range (orderedProduct (binaryParameters n hn)) := by
    rw [range_orderedProduct_binary]
    exact g.property
  obtain ⟨a, ha⟩ := hg
  exact ⟨a, ha, fun b hb => orderedProduct_injective_binary n hn (hb.trans ha.symm)⟩

/-- Twelve independent GF(q³) parameters give the split positive subgroup order q^36. -/
theorem card_positiveSubgroup_binary (n : ℕ) (hn : 0 < n) :
    Nat.card (Parabolics.positiveSubgroup (binaryParameters n hn)) =
      (binaryParameters n hn).q ^ 36 :=
  card_positiveSubgroup_of_normalForm (binaryParameters n hn)
    (orderedProduct_injective_binary n hn) (range_orderedProduct_binary n hn)

/-- The positive subgroup is a two-group by its proved order. -/
theorem isPGroup_positiveSubgroup_binary (n : ℕ) (hn : 0 < n) :
    IsPGroup 2 (Parabolics.positiveSubgroup (binaryParameters n hn)) :=
  isPGroup_positiveSubgroup_of_normalForm (binaryParameters n hn)
    (orderedProduct_injective_binary n hn) (range_orderedProduct_binary n hn)

/-- A positive matrix product is fixed exactly when its parameters satisfy the
actual diagram-permutation and coefficient-Frobenius equations. -/
theorem orderedProduct_mem_fixedSubgroup_iff_binary (n : ℕ) (hn : 0 < n)
    (a : Coordinates (binaryParameters n hn)) :
    orderedProduct (binaryParameters n hn) a ∈ fixedSubgroup (binaryParameters n hn) ↔
      ∀ i, a (diagram i) = fieldFrobenius (binaryParameters n hn) (a i) := by
  rw [mem_fixedSubgroup, graphField_orderedProduct_binary, ← twist_eq_self_iff]
  exact ⟨fun h => orderedProduct_injective_binary n hn h,
    fun h => congrArg (orderedProduct (binaryParameters n hn)) h⟩

/-- Fixed tuples parametrizing the full positive graph-field fixed subgroup. -/
def fixedPositiveEquiv_binary (n : ℕ) (hn : 0 < n) :
    FixedCoordinates (binaryParameters n hn) ≃
      (Parabolics.positiveSubgroup (binaryParameters n hn)).comap
        (fixedSubgroup (binaryParameters n hn)).subtype :=
  fixedPositiveEquivOfNormalForm (binaryParameters n hn)
    (orderedProduct_injective_binary n hn) (range_orderedProduct_binary n hn)
    (graphField_orderedProduct_binary n hn)

@[simp] theorem fixedPositiveEquiv_binary_val (n : ℕ) (hn : 0 < n)
    (a : FixedCoordinates (binaryParameters n hn)) :
    (fixedPositiveEquiv_binary n hn a).val.val =
      orderedProduct (binaryParameters n hn) a.val := rfl

/-- Three extension-field parameters and three fixed-field parameters give
coordinates on the actual fixed positive matrices. The triple coordinates
are t, F(t), F²(t), as specified by `expand`. -/
def orbitPositiveEquiv_binary (n : ℕ) (hn : 0 < n) :
    OrbitParameters (binaryParameters n hn) ≃
      (Parabolics.positiveSubgroup (binaryParameters n hn)).comap
        (fixedSubgroup (binaryParameters n hn)).subtype :=
  (fixedCoordinatesEquiv (binaryParameters n hn)).trans (fixedPositiveEquiv_binary n hn)

@[simp] theorem orbitPositiveEquiv_binary_val (n : ℕ) (hn : 0 < n)
    (a : OrbitParameters (binaryParameters n hn)) :
    (orbitPositiveEquiv_binary n hn a).val.val =
      orderedProduct (binaryParameters n hn) (expand (binaryParameters n hn) a) := rfl

/-- The full positive graph-field fixed subgroup has order q^12, including q = 2. -/
theorem card_fixedPositive_binary (n : ℕ) (hn : 0 < n) :
    Nat.card ((Parabolics.positiveSubgroup (binaryParameters n hn)).comap
      (fixedSubgroup (binaryParameters n hn)).subtype) = (binaryParameters n hn).q ^ 12 :=
  card_fixedPositive_of_normalForm (binaryParameters n hn)
    (orderedProduct_injective_binary n hn) (range_orderedProduct_binary n hn)
    (graphField_orderedProduct_binary n hn)

end
end Triality.Standard.PositiveCoordinates
