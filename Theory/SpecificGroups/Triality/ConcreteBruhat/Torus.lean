module
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Torus.Count
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Torus.Borel
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Torus.DiagonalData
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Torus.Diagonal
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Torus.PositiveAction

/-!
# Concrete triality torus and Borel descent

In characteristic two the original Geck coroot words have faithful multiplicative
coordinates in four extension-field units. Their proved diagonal action normalizes
the positive subgroup, and the positive two-group meets the diagonal torus
trivially. This gives the unique split Borel factorization.

Graph-field fixed torus coordinates consist of one extension-field unit and one
unit of the actual q-Frobenius fixed field. Folded rank-one words lift every such
element into the elementary subgroup. Uniqueness makes the factors of a fixed
Borel element fixed, and the positive factor has characteristic-power order.
The proved injectivity of the actual elementary central quotient then preserves
the unique factorization in Carrier. Thus the torus order and the relative index
of U in B are both (q³ - 1)(q - 1), which is odd. Every positive binary exponent,
including q = 2, is covered.

These are the torus and Borel-factorization parts of GLS3 2.3.4(c), 2.3.8(a),
and 2.4.7 (`refs/KGroup/GLS3/chapter2.tex`). Normality is relative to the Borel;
the global Bruhat count and Sylow assertion belong to the Bruhat development.
The earlier conditional assembly remains available with its original interface.
-/

@[expose] public section
noncomputable section
open scoped Pointwise
namespace Triality.Standard.ConcreteBruhat
open Parabolics
open Theory.AlgebraicGroup.StandardRootSystem

/-- The relative Borel index is odd once the split torus's faithful coordinates,
normalization, and trivial intersection have been proved. The positive two-group
premise is supplied by its existing, unconditional twelve-root normal form. -/
theorem odd_borel_relIndex_binary_of_torus (n : ℕ) (hn : 0 < n)
    (hinj : Function.Injective (TorusCoordinates.product (binaryParameters n hn)))
    (hrange : Set.range (TorusCoordinates.product (binaryParameters n hn)) =
      (splitTorus (binaryParameters n hn) : Set (SplitGroup (binaryParameters n hn))))
    (hN : splitTorus (binaryParameters n hn) ≤
      Subgroup.normalizer (positiveSubgroup (binaryParameters n hn)))
    (hD : Disjoint (positiveSubgroup (binaryParameters n hn)) (splitTorus (binaryParameters n hn))) :
    Odd ((unipotent (binaryParameters n hn)).relIndex (borel (binaryParameters n hn))) := by
  rw [borel_relIndex_eq_card_torus_of_split _ rfl
    (PositiveCoordinates.isPGroup_positiveSubgroup_binary n hn) hN hD,
    TorusCoordinates.card_torus_of_coordinates _ rfl hinj hrange]
  exact TorusCoordinates.odd_torus_order _ rfl

/-- The proved binary positive normal form applies to every characteristic-two parameter. -/
theorem isPGroup_positiveSubgroup (P : Parameters) (hp : P.prime = 2) :
    IsPGroup P.prime (positiveSubgroup P) := by
  obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
  exact PositiveCoordinates.isPGroup_positiveSubgroup_binary n hn

/-- Left conjugation by the original coroot word on every positive Geck curve. -/
theorem torusWord_curve_conjugate (P : Parameters) (hp : P.prime = 2)
    (i : Fin 4) (t : (ExtensionField P)ˣ) (j : Fin 12) (s : ExtensionField P) :
    torusWord P i t * PositiveCoordinates.curve P j s * (torusWord P i t)⁻¹ =
      PositiveCoordinates.curve P j (t.val ^ ((typeDRootPairing 2).pairingIn ℤ
        (PositiveCoordinates.rootIndex j) (typeDSimpleRootIndex 2 i)) * s) :=
  torusWord_curve_conjugate_of_diagonal P (TorusCoordinates.torusWord_val P hp) i t j s

/-- The corresponding formula for the original pinned simple generators. -/
theorem torusWord_positiveRoot_conjugate (P : Parameters) (hp : P.prime = 2)
    (i : Fin 4) (t : (ExtensionField P)ˣ) (j : Fin 4) (s : ExtensionField P) :
    torusWord P i t * positiveRoot P j s * (torusWord P i t)⁻¹ =
      positiveRoot P j (t.val ^ ((typeDRootPairing 2).pairingIn ℤ
        (typeDSimpleRootIndex 2 j) (typeDSimpleRootIndex 2 i)) * s) :=
  torusWord_positiveRoot_conjugate_of_diagonal P (TorusCoordinates.torusWord_val P hp) i t j s

theorem splitTorus_le_normalizer_positiveSubgroup (P : Parameters) (hp : P.prime = 2) :
    splitTorus P ≤ Subgroup.normalizer (positiveSubgroup P) :=
  splitTorus_le_normalizer_positiveSubgroup_of_diagonal P (TorusCoordinates.torusWord_val P hp)

theorem disjoint_positiveSubgroup_splitTorus (P : Parameters) (hp : P.prime = 2) :
    Disjoint (positiveSubgroup P) (splitTorus P) :=
  disjoint_positiveSubgroup_splitTorus_of_diagonal P hp (TorusCoordinates.torusWord_val P hp)
    (by simpa only [hp] using isPGroup_positiveSubgroup P hp)

/-- The original split Borel is the positive-times-torus product as sets. -/
theorem splitBorel_eq_mul (P : Parameters) (hp : P.prime = 2) :
    (splitBorel P : Set (SplitGroup P)) =
      (positiveSubgroup P : Set (SplitGroup P)) * splitTorus P :=
  splitBorel_eq_mul_of_normalizes P (splitTorus_le_normalizer_positiveSubgroup P hp)

theorem existsUnique_splitBorel_factors (P : Parameters) (hp : P.prime = 2)
    (g : splitBorel P) :
    ∃! a : positiveSubgroup P × splitTorus P, a.1.val * a.2.val = g.val :=
  existsUnique_splitBorel_factors_of_normalizes P (splitTorus_le_normalizer_positiveSubgroup P hp)
    (disjoint_positiveSubgroup_splitTorus P hp) g

/-- Normality is relative to the split Borel. -/
theorem splitPositive_normal_in_borel (P : Parameters) (hp : P.prime = 2) :
    ((positiveSubgroup P).subgroupOf (splitBorel P)).Normal :=
  splitPositive_normal_in_borel_of_normalizes P (splitTorus_le_normalizer_positiveSubgroup P hp)

namespace TorusCoordinates

/-- The actual graph-field fixed matrices have exactly the fixed scalar coordinates. -/
theorem product_mem_fixedSubgroup_iff (P : Parameters) (hp : P.prime = 2)
    (a : Coordinates P) : product P a ∈ fixedSubgroup P ↔ twist P a = a :=
  product_fixed_iff P hp (product_injective P hp) a

/-- Every fixed torus element is elementary, by the explicit folded rank-one lifts. -/
theorem fixedTorus_le_elementary (P : Parameters) (hp : P.prime = 2) :
    (splitTorus P).comap (fixedSubgroup P).subtype ≤ elementarySubgroup P :=
  fixedTorus_le_elementary_of_coordinates P hp (product_injective P hp) (range_product P hp)

/-- The full fixed torus, before the elementary restriction and central quotient,
is the product of the extension-field units and the actual q-Frobenius-fixed units. -/
def fixedTorusMulEquiv (P : Parameters) (hp : P.prime = 2) :
    OrbitParameters P ≃* (splitTorus P).comap (fixedSubgroup P).subtype := by
  let f : OrbitParameters P →* (splitTorus P).comap (fixedSubgroup P).subtype :=
    { toFun := fun a =>
        ⟨⟨product P (expand P a),
          (product_mem_fixedSubgroup_iff P hp _).mpr (expand_fixed P a)⟩, product_mem P _⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        change product P (expand P 1) = 1
        rw [show expand P 1 = 1 by ext i; fin_cases i <;> simp [expand], product_one P hp]
      map_mul' := fun a b => by
        apply Subtype.ext
        apply Subtype.ext
        change product P (expand P (a * b)) = product P (expand P a) * product P (expand P b)
        rw [expand_mul, product_mul P hp] }
  apply MulEquiv.ofBijective f
  constructor
  · intro a b h
    apply (fixedCoordinatesEquiv P).injective
    apply Subtype.ext
    exact product_injective P hp (congrArg (fun g => g.val.val) h)
  · intro g
    have hg : g.val.val ∈ Set.range (product P) :=
      (Set.ext_iff.mp (range_product P hp) g.val.val).mpr g.property
    obtain ⟨a, ha⟩ := hg
    have hfix : twist P a = a := (product_mem_fixedSubgroup_iff P hp a).mp (by
      rw [ha]
      exact g.val.property)
    let b := (fixedCoordinatesEquiv P).symm ⟨a, hfix⟩
    have hb : expand P b = a := congrArg Subtype.val
      ((fixedCoordinatesEquiv P).apply_symm_apply ⟨a, hfix⟩)
    exact ⟨b, Subtype.ext (Subtype.ext ((congrArg (product P) hb).trans ha))⟩

@[simp] theorem fixedTorusMulEquiv_val (P : Parameters) (hp : P.prime = 2)
    (a : OrbitParameters P) :
    (fixedTorusMulEquiv P hp a).val.val = product P (expand P a) := rfl

/-- Folded elementary words followed by the actual central quotient identify the torus. -/
def torusMulEquiv (P : Parameters) (hp : P.prime = 2) : OrbitParameters P ≃* torus P :=
  torusMulEquivOfCoordinates P hp (product_injective P hp) (range_product P hp) (product_mul P hp)

@[simp] theorem torusMulEquiv_val (P : Parameters) (hp : P.prime = 2)
    (a : OrbitParameters P) :
    (torusMulEquiv P hp a).val = toCarrier P (orbitElementary P hp a) := rfl

theorem card_splitTorus (P : Parameters) (hp : P.prime = 2) :
    Nat.card (splitTorus P) = (P.q ^ 3 - 1) ^ 4 :=
  (Nat.card_congr (splitTorusMulEquiv P hp).toEquiv).symm.trans (card_coordinates P)

theorem card_fixedTorus (P : Parameters) (hp : P.prime = 2) :
    Nat.card ((splitTorus P).comap (fixedSubgroup P).subtype) = (P.q ^ 3 - 1) * (P.q - 1) := by
  rw [← Nat.card_congr (fixedTorusMulEquiv P hp).toEquiv, Nat.card_prod,
    Nat.card_units, Nat.card_units, card_extensionField, card_fixedField]

/-- The original torus in Carrier has the source order, including at q = 2. -/
theorem card_torus (P : Parameters) (hp : P.prime = 2) :
    Nat.card (torus P) = (P.q ^ 3 - 1) * (P.q - 1) :=
  card_torus_of_coordinates P hp (product_injective P hp) (range_product P hp)

end TorusCoordinates

/-- Descent to the original elementary central quotient preserves the product. -/
theorem borel_eq_mul (P : Parameters) (hp : P.prime = 2) :
    (borel P : Set (Carrier P)) = (unipotent P : Set (Carrier P)) * torus P :=
  borel_eq_mul_of_split P (isPGroup_positiveSubgroup P hp)
    (splitTorus_le_normalizer_positiveSubgroup P hp) (disjoint_positiveSubgroup_splitTorus P hp)

theorem disjoint_unipotent_torus (P : Parameters) (hp : P.prime = 2) :
    Disjoint (unipotent P) (torus P) :=
  disjoint_unipotent_torus_of_split P hp (disjoint_positiveSubgroup_splitTorus P hp)

/-- Normality is asserted inside the actual descended Borel. -/
theorem unipotent_normal_in_borel (P : Parameters) (hp : P.prime = 2) :
    ((unipotent P).subgroupOf (borel P)).Normal :=
  unipotent_normal_in_borel_of_split P (splitTorus_le_normalizer_positiveSubgroup P hp)

/-- Unique positive-times-torus coordinates in the actual Carrier. -/
def borelEquiv (P : Parameters) (hp : P.prime = 2) : unipotent P × torus P ≃ borel P :=
  borelEquivOfSplit P hp (isPGroup_positiveSubgroup P hp)
    (splitTorus_le_normalizer_positiveSubgroup P hp) (disjoint_positiveSubgroup_splitTorus P hp)

@[simp] theorem borelEquiv_val (P : Parameters) (hp : P.prime = 2)
    (a : unipotent P × torus P) : (borelEquiv P hp a).val = a.1.val * a.2.val := rfl

theorem existsUnique_borel_factors (P : Parameters) (hp : P.prime = 2) (g : borel P) :
    ∃! a : unipotent P × torus P, a.1.val * a.2.val = g.val := by
  refine ⟨(borelEquiv P hp).symm g,
    congrArg Subtype.val ((borelEquiv P hp).apply_symm_apply g), ?_⟩
  intro b hb
  apply (borelEquiv P hp).injective
  exact (Subtype.ext hb).trans ((borelEquiv P hp).apply_symm_apply g).symm

theorem borel_relIndex_eq_card_torus (P : Parameters) (hp : P.prime = 2) :
    (unipotent P).relIndex (borel P) = Nat.card (torus P) :=
  borel_relIndex_eq_card_torus_of_split P hp (isPGroup_positiveSubgroup P hp)
    (splitTorus_le_normalizer_positiveSubgroup P hp) (disjoint_positiveSubgroup_splitTorus P hp)

theorem borel_relIndex (P : Parameters) (hp : P.prime = 2) :
    (unipotent P).relIndex (borel P) = (P.q ^ 3 - 1) * (P.q - 1) :=
  (borel_relIndex_eq_card_torus P hp).trans (TorusCoordinates.card_torus P hp)

/-- U has odd index in B. This is the local Borel index, not its global index in Carrier. -/
theorem odd_borel_relIndex (P : Parameters) (hp : P.prime = 2) :
    Odd ((unipotent P).relIndex (borel P)) := by
  rw [borel_relIndex P hp]
  exact TorusCoordinates.odd_torus_order P hp

/-- Every positive binary exponent is included, in particular exponent one. -/
theorem odd_borel_relIndex_binary (n : ℕ) (hn : 0 < n) :
    Odd ((unipotent (binaryParameters n hn)).relIndex (borel (binaryParameters n hn))) :=
  odd_borel_relIndex _ rfl

end Triality.Standard.ConcreteBruhat
