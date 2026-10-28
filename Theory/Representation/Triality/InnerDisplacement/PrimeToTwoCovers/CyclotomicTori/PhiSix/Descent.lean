module

public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.FixedDescent.SubfieldLifts
public import Theory.SpecificGroups.Triality.ConcreteBruhat.FixedDescent

/-!
# Sixth-cyclotomic torus descent through the actual triality fixed group

Work in the original split Geck group over GF(q⁶), with the forward
diagram–q-Frobenius F. The word c is the product of the three arm Weyl
words followed by the central word. Two independent constructions are
needed: a marked plane in the split torus satisfying c F(t) = t c, and
a Lang witness F(x) = x c. Conjugation by x then gives actual F-fixed
matrices. The proved half-field descent and elementary central quotient
identify these with the original carrier over GF(q³).

The ambient actor is the conjugate of c⁴. Its two required eigenvalues
are q² and 1, so its determinant can detect the lifted alternating pairing.
This is conditional descent, not an assertion that either input exists.

Source: GLS3 §2.1 (twisted tori and Lang conjugation), §§2.2–2.4
(graph-field construction and fixed Bruhat descent), and §6.1.
-/

@[expose] public section
noncomputable section
namespace Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiSix
open Standard Standard.EvenField Standard.ConcreteBruhat
open Standard.ConcreteBruhat.FixedDescent

abbrev Plane (d : ℕ) := Multiplicative (ZMod d × ZMod d)

def first (d : ℕ) : Plane d := Multiplicative.ofAdd (1, 0)
def second (d : ℕ) : Plane d := Multiplicative.ofAdd (0, 1)

abbrev largerParameters (n : ℕ) (hn : 0 < n) : Parameters :=
  binaryParameters (2 * n) (by omega)

abbrev halfTwist (n : ℕ) (hn : 0 < n) : MulAut (SplitGroup (largerParameters n hn)) :=
  forwardGraphHalf (2 * n) (by omega) n

/-- The specified folded Coxeter word, embedded coefficientwise in GF(q⁶). -/
def rotation (n : ℕ) (hn : 0 < n) : SplitGroup (largerParameters n hn) :=
  halfSplitMap (2 * n) (by omega) n hn rfl
    (splitRepresentative (binaryParameters n hn) rfl (.r 1))

private theorem mapped_rotation_word (P Q : Parameters) (hp : P.prime = 2)
    (f : ExtensionField P →+* ExtensionField Q) :
    RootPairing.SimpleGeckGroup.map f (splitRepresentative P hp (.r 1)) =
      Parabolics.weylWord Q 0 1 * Parabolics.weylWord Q 2 1 *
      Parabolics.weylWord Q 3 1 * Parabolics.weylWord Q 1 1 := by
  have he : splitRepresentative P hp (.r 1) =
      Parabolics.weylWord P 0 1 * Parabolics.weylWord P 2 1 *
      Parabolics.weylWord P 3 1 * Parabolics.weylWord P 1 1 := by
    change Parabolics.elementaryInclusion P ((_ * _) ^ (1 : ℕ)) = _
    simp only [pow_one, map_mul, elementaryInclusion_simple_arms,
      elementaryInclusion_simple_central]
  simp only [he, Parabolics.weylWord, Parabolics.positiveRoot, Parabolics.negativeRoot,
    map_mul, RootPairing.SimpleGeckGroup.map_positive,
    RootPairing.SimpleGeckGroup.map_negative, map_neg, map_inv₀, map_one]

/-- The chosen word is exactly arms times central in the larger split group. -/
theorem rotation_eq_word (n : ℕ) (hn : 0 < n) :
    rotation n hn =
      Parabolics.weylWord (largerParameters n hn) 0 1 *
      Parabolics.weylWord (largerParameters n hn) 2 1 *
      Parabolics.weylWord (largerParameters n hn) 3 1 *
      Parabolics.weylWord (largerParameters n hn) 1 1 :=
  mapped_rotation_word (binaryParameters n hn) (largerParameters n hn) rfl
    (halfFieldEmbedding (2 * n) (by omega) n hn rfl)

/-- The finite Lang problem has the expected order-six Weyl word. -/
theorem orderOf_rotation (n : ℕ) (hn : 0 < n) : orderOf (rotation n hn) = 6 := by
  rw [rotation_eq_word]
  exact orderOf_splitSimpleProduct _ rfl

theorem rotation_fixed (n : ℕ) (hn : 0 < n) :
    halfTwist n hn (rotation n hn) = rotation n hn := by
  unfold rotation
  rw [← halfSplitMap_forward]
  exact congrArg (halfSplitMap (2 * n) (by omega) n hn rfl)
    (weylElementary (binaryParameters n hn) rfl (.r 1)).val.property

/-- A faithful marked twisted torus plane, before any Lang conjugation.
All equations refer to the literal split Geck matrices over GF(q⁶). -/
structure TwistedPlane (n : ℕ) (hn : 0 < n) (d : ℕ) where
  embedding : Plane d →* SplitGroup (largerParameters n hn)
  injective : Function.Injective embedding
  mem_torus : ∀ z, embedding z ∈ splitTorus (largerParameters n hn)
  twisted : ∀ z, rotation n hn * halfTwist n hn (embedding z) =
    embedding z * rotation n hn
  conjugate_first : rotation n hn ^ 4 * embedding (first d) * (rotation n hn ^ 4)⁻¹ =
    embedding (first d) ^ ((2 ^ n) ^ 2)
  conjugate_second : rotation n hn ^ 4 * embedding (second d) * (rotation n hn ^ 4)⁻¹ =
    embedding (second d)

/-- An actual finite-field solution, with the orientation used in descent. -/
structure LangWitness (n : ℕ) (hn : 0 < n) where
  point : SplitGroup (largerParameters n hn)
  equation : halfTwist n hn point = point * rotation n hn

theorem LangWitness.conjugate_mem_fixed {n : ℕ} {hn : 0 < n}
    (x : LangWitness n hn) (y : SplitGroup (largerParameters n hn))
    (hy : rotation n hn * halfTwist n hn y = y * rotation n hn) :
    x.point * y * x.point⁻¹ ∈ (halfTwist n hn).fixedSubgroup := by
  apply (MulAut.mem_fixedSubgroup _ _).mpr
  calc
    _ = x.point * (rotation n hn * halfTwist n hn y) *
        (rotation n hn)⁻¹ * x.point⁻¹ := by
      simp only [map_mul, map_inv, x.equation]
      group
    _ = _ := by rw [hy]; group

/-- The existing root-word subfield lifts discharge every descent premise. -/
def fixedCarrierEquiv (n : ℕ) (hn : 0 < n) :
    (halfTwist n hn).fixedSubgroup ≃* BinaryCarrier n hn :=
  (halfFixedEquivOfSplitLifts (2 * n) (by omega) n hn rfl
    (halfSplitMap_lift_of_forwardGraphHalf_fixed (2 * n) (by omega) n hn rfl)).symm.trans
      (carrierFixedEquiv (binaryParameters n hn) rfl).symm

namespace TwistedPlane
variable {n d : ℕ} {hn : 0 < n} (D : TwistedPlane n hn d) (x : LangWitness n hn)

def fixedEmbedding : Plane d →* (halfTwist n hn).fixedSubgroup :=
  (((MulAut.conj x.point).toMonoidHom).comp D.embedding).codRestrict
    (halfTwist n hn).fixedSubgroup
    (fun z => x.conjugate_mem_fixed _ (D.twisted z))

theorem fixedEmbedding_injective : Function.Injective (D.fixedEmbedding x) := by
  intro a b h
  exact D.injective ((MulAut.conj x.point).injective (congrArg Subtype.val h))

def fixedActor : (halfTwist n hn).fixedSubgroup :=
  ⟨x.point * rotation n hn ^ 4 * x.point⁻¹, x.conjugate_mem_fixed _ (by
    rw [map_pow, rotation_fixed]
    group)⟩

/-- A homomorphism into the genuine original elementary central quotient. -/
def carrierEmbedding : Plane d →* BinaryCarrier n hn :=
  (fixedCarrierEquiv n hn).toMonoidHom.comp (D.fixedEmbedding x)

theorem carrierEmbedding_injective : Function.Injective (D.carrierEmbedding x) :=
  (fixedCarrierEquiv n hn).injective.comp (D.fixedEmbedding_injective x)

def carrierActor : BinaryCarrier n hn := fixedCarrierEquiv n hn (fixedActor x)

private theorem conjugate_descends (z w : Plane d)
    (h : rotation n hn ^ 4 * D.embedding z * (rotation n hn ^ 4)⁻¹ = D.embedding w) :
    carrierActor x * D.carrierEmbedding x z * (carrierActor x)⁻¹ =
      D.carrierEmbedding x w := by
  have he : fixedActor x * D.fixedEmbedding x z * (fixedActor x)⁻¹ =
      D.fixedEmbedding x w := by
    apply Subtype.ext
    change (MulAut.conj x.point) (rotation n hn ^ 4) *
      (MulAut.conj x.point) (D.embedding z) *
      ((MulAut.conj x.point) (rotation n hn ^ 4))⁻¹ =
      (MulAut.conj x.point) (D.embedding w)
    simpa only [map_mul, map_inv] using congrArg (MulAut.conj x.point) h
  simpa only [carrierActor, carrierEmbedding, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, map_mul, map_inv] using congrArg (fixedCarrierEquiv n hn) he

/-- The first generator has determinant-detecting power q² in the actual carrier. -/
theorem carrier_conjugate_first :
    carrierActor x * D.carrierEmbedding x (first d) * (carrierActor x)⁻¹ =
      D.carrierEmbedding x (first d) ^ ((2 ^ n) ^ 2) := by
  exact (D.conjugate_descends x (first d) (first d ^ ((2 ^ n) ^ 2))
    (D.conjugate_first.trans (map_pow D.embedding (first d) _).symm)).trans
      (map_pow (D.carrierEmbedding x) (first d) _)

/-- The same literal ambient actor fixes the second generator. -/
theorem carrier_conjugate_second :
    carrierActor x * D.carrierEmbedding x (second d) * (carrierActor x)⁻¹ =
      D.carrierEmbedding x (second d) :=
  D.conjugate_descends x (second d) (second d) D.conjugate_second

end TwistedPlane
end Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiSix
