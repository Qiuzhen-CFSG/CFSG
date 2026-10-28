module

public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Descent

/-!
# Marked elementary lifts for the odd triality centralizer

The central and three-arm maps lift to the elementary fixed group. The same
central-times-arms Weyl word and its inverse conjugation define the complementary
map before either inclusion or central quotient. This supplies a common boundary
for the integral matrix calculation, the elementary centralizer index calculation,
and the subsequent quotient argument.

No centralizer exhaustion is asserted here. The split commutation and scalar
identities are explicit inputs to the transport lemmas. Sources: GLS3 §§2.4, 2.6
(`refs/KGroup/GLS3/chapter2.tex`); Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public section
noncomputable section
open Matrix
open scoped MatrixGroups

namespace Triality.Standard.OddFundamentalCentralizer
open Parabolics

variable {P : Parameters} (D : PinnedRankOneMaps P) (C : ArmRootCommutation P)

/-- The marked central SL₂ before the central quotient. -/
def fundamentalLift : SL(2, GaloisField P.prime P.exponent) →* ElementaryGroup P :=
  elementaryLift P D.centralFixedEmbedding (centralFixed_mem D)

/-- The fixed three-arm diagonal before the central quotient. -/
def armsLift : SL(2, ExtensionField P) →* ElementaryGroup P :=
  elementaryLift P (D.armsFixedEmbedding C) (armsFixed_mem D C)

/-- The literal central-times-arms Weyl word in the elementary fixed group. -/
def highestLift : ElementaryGroup P :=
  fundamentalLift D (weylMatrix _) * armsLift D C (weylMatrix _)

/-- Inverse conjugation of the three-arm diagonal, before central quotient. -/
def complementLift : SL(2, ExtensionField P) →* ElementaryGroup P :=
  (MulAut.conj (highestLift D C)⁻¹).toMonoidHom.comp (armsLift D C)

/-- The same Weyl word in the split D₄ matrix group. -/
def splitHighestWeyl : SplitGroup P :=
  D.centralFixedEmbedding (weylMatrix _) * D.armsFixedEmbedding C (weylMatrix _)

/-- The precise split map used by the integral geometry calculation. -/
def splitComplementHom : SL(2, ExtensionField P) →* SplitGroup P :=
  (MulAut.conj (splitHighestWeyl D C)⁻¹).toMonoidHom.comp (D.armsFixedEmbedding C)

@[simp] theorem inclusion_fundamentalLift (a : SL(2, GaloisField P.prime P.exponent)) :
    elementaryInclusion P (fundamentalLift D a) = D.centralFixedEmbedding a := rfl

@[simp] theorem inclusion_armsLift (a : SL(2, ExtensionField P)) :
    elementaryInclusion P (armsLift D C a) = D.armsFixedEmbedding C a := rfl

@[simp] theorem inclusion_highestLift :
    elementaryInclusion P (highestLift D C) = splitHighestWeyl D C := rfl

@[simp] theorem inclusion_complementLift (a : SL(2, ExtensionField P)) :
    elementaryInclusion P (complementLift D C a) = splitComplementHom D C a := rfl

@[simp] theorem toCarrier_fundamentalLift (a : SL(2, GaloisField P.prime P.exponent)) :
    toCarrier P (fundamentalLift D a) = fundamentalHom D a := rfl

@[simp] theorem toCarrier_armsLift (a : SL(2, ExtensionField P)) :
    toCarrier P (armsLift D C a) = armsHom D C a := rfl

@[simp] theorem toCarrier_highestLift :
    toCarrier P (highestLift D C) = highestWeyl D C := (toCarrier P).map_mul _ _

@[simp] theorem toCarrier_complementLift (a : SL(2, ExtensionField P)) :
    toCarrier P (complementLift D C a) = complementHom D C a := by
  change toCarrier P ((highestLift D C)⁻¹ * armsLift D C a *
    ((highestLift D C)⁻¹)⁻¹) = _
  simp only [map_mul, map_inv, toCarrier_highestLift, toCarrier_armsLift]
  rfl

/-- Split commutation lifts faithfully through the two subgroup inclusions. -/
theorem fundamentalLift_complementLift_commute
    (hcomm : ∀ a b, Commute (D.centralFixedEmbedding a) (splitComplementHom D C b))
    (a : SL(2, GaloisField P.prime P.exponent)) (b : SL(2, ExtensionField P)) :
    Commute (fundamentalLift D a) (complementLift D C b) := by
  exact Subtype.ext (Subtype.ext (hcomm a b).eq)

/-- The integral calculation supplies the exact commutation input of `residualHom`. -/
theorem fundamentalHom_complementHom_commute_of_split
    (hcomm : ∀ a b, Commute (D.centralFixedEmbedding a) (splitComplementHom D C b))
    (a : SL(2, GaloisField P.prime P.exponent)) (b : SL(2, ExtensionField P)) :
    Commute (fundamentalHom D a) (complementHom D C b) := by
  simpa only [toCarrier_fundamentalLift, toCarrier_complementLift] using
    (fundamentalLift_complementLift_commute D C hcomm a b).map (toCarrier P)

/-- The split scalar identity supplies the scalar input of the exact intersection lemma. -/
theorem fundamentalHom_neg_one_eq_complementHom_of_split
    (hneg : D.centralFixedEmbedding (-1) = splitComplementHom D C (-1)) :
    fundamentalHom D (-1) = complementHom D C (-1) := by
  have he : fundamentalLift D (-1) = complementLift D C (-1) :=
    Subtype.ext (Subtype.ext hneg)
  simpa only [toCarrier_fundamentalLift, toCarrier_complementLift] using
    congrArg (toCarrier P) he

/-- The centralizer of the marked central factor in the elementary fixed group. -/
def elementaryCentralizer : Subgroup (ElementaryGroup P) :=
  Subgroup.centralizer ((fundamentalLift D).range : Set (ElementaryGroup P))

/-- The complementary lift restricted to the actual elementary centralizer. -/
def elementaryCentralizerHom
    (hcomm : ∀ a b, Commute (D.centralFixedEmbedding a) (splitComplementHom D C b)) :
    SL(2, ExtensionField P) →* elementaryCentralizer D :=
  (complementLift D C).codRestrict _ fun b => by
    change ∀ x : ElementaryGroup P, x ∈ (fundamentalLift D).range →
      x * complementLift D C b = complementLift D C b * x
    rintro _ ⟨a, rfl⟩
    exact (fundamentalLift_complementLift_commute D C hcomm a b).eq

private theorem toCarrier_mem_centralizer (x : elementaryCentralizer D) :
    toCarrier P x.val ∈ Subgroup.centralizer (fundamental P : Set (Carrier P)) := by
  have he : toCarrier P '' ((fundamentalLift D).range : Set (ElementaryGroup P)) =
      (fundamental P : Set (Carrier P)) :=
    (Set.range_comp (toCarrier P) (fundamentalLift D)).symm.trans
      (congrArg (fun H : Subgroup (Carrier P) => (H : Set (Carrier P)))
        (range_fundamentalHom D))
  have hx := Subgroup.map_centralizer_le_centralizer_image
    ((fundamentalLift D).range : Set (ElementaryGroup P)) (toCarrier P)
    (show toCarrier P x.val ∈ (elementaryCentralizer D).map (toCarrier P) from
      ⟨x.val, x.property, rfl⟩)
  exact (congrArg (fun S : Set (Carrier P) =>
    toCarrier P x.val ∈ Subgroup.centralizer S) he).mp hx

/-- The central quotient, restricted to the two actual centralizers. Its
surjectivity is a separate coprime-kernel argument, including at q = 3. -/
def centralizerQuotient :
    elementaryCentralizer D →* Subgroup.centralizer (fundamental P : Set (Carrier P)) where
  toFun x := ⟨toCarrier P x.val, by exact toCarrier_mem_centralizer D x⟩
  map_one' := Subtype.ext (map_one (toCarrier P))
  map_mul' x y := Subtype.ext ((toCarrier P).map_mul x.val y.val)

theorem centralizerQuotient_val (x : elementaryCentralizer D) :
    (centralizerQuotient D x).val = toCarrier P x.val := rfl

theorem centralizerQuotient_elementaryCentralizerHom
    (hcomm : ∀ a b, Commute (D.centralFixedEmbedding a) (splitComplementHom D C b))
    (a : SL(2, ExtensionField P)) :
    (centralizerQuotient D (elementaryCentralizerHom D C hcomm a)).val =
      complementHom D C a := toCarrier_complementLift D C a

end Triality.Standard.OddFundamentalCentralizer
