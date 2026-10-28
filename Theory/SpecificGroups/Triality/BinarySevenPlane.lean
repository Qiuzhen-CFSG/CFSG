module

public import Theory.SpecificGroups.Triality.BinarySevenPlane.Lang
public import Theory.SpecificGroups.Triality.BinarySevenPlane.TorusAction
public import Theory.SpecificGroups.Triality.ConcreteBruhat.FixedDescent
public import Theory.SpecificGroups.Triality.Model.QTKE

/-!
# The marked seven-plane in the genuine triality group at q = 2

Conjugate the faithful marked split torus and its two quaternion Weyl words
by the explicit Lang witness. Their proved twisted fixedness becomes genuine
graph-field fixedness. The established equivalence from the original carrier
(the elementary fixed group modulo its own center) to the full fixed group
then transports the embedding and both exact conjugation formulas.

The final `Triality.Standard.binarySevenPlane` has no extra hypothesis. Its
marking is precisely `QuaternionSevenPlane.firstMap` and `secondMap`, so it
can feed the independent degree-24 weight argument directly.
Source: the nonsplit seven-torus normalizer in ³D₄(2), ATLAS printed p.89,
using the explicit full-lattice construction in the descendant modules.
-/

public section
namespace Triality.Standard.BinarySevenPlane
open QuaternionSevenPlane ConcreteBruhat.FixedDescent
noncomputable section
local notation "P" => binaryParameters 1 Nat.zero_lt_one

lemma conjugate_mem_fixed (y : SplitGroup P)
    (hy : twistWord * graphFieldAutomorphism P y = y * twistWord) :
    langWitness * y * langWitness⁻¹ ∈ fixedSubgroup P := by
  change graphFieldAutomorphism P (langWitness * y * langWitness⁻¹) = langWitness * y * langWitness⁻¹
  calc
    _ = langWitness * (twistWord * graphFieldAutomorphism P y) *
        twistWord⁻¹ * langWitness⁻¹ := by
      simp only [map_mul, map_inv, graphField_langWitness]
      group
    _ = _ := by rw [hy]; group

def fixedEmbedding : Multiplicative Plane →* fixedSubgroup P :=
  (((MulAut.conj langWitness).toMonoidHom).comp splitEmbedding).codRestrict
    (fixedSubgroup P) (fun z => conjugate_mem_fixed _ (twist_torus z.toAdd))

lemma fixedEmbedding_val (z : Multiplicative Plane) :
    (fixedEmbedding z).val = langWitness * splitEmbedding z * langWitness⁻¹ := by
  rfl

lemma fixedEmbedding_injective : Function.Injective fixedEmbedding := by
  intro a b h
  exact splitEmbedding_injective ((MulAut.conj langWitness).injective (congrArg Subtype.val h))

def fixedFirst : fixedSubgroup P :=
  ⟨langWitness * firstWord * langWitness⁻¹, conjugate_mem_fixed _ twist_first⟩
def fixedSecond : fixedSubgroup P :=
  ⟨langWitness * secondWord * langWitness⁻¹, conjugate_mem_fixed _ twist_second⟩

lemma fixedFirst_conjugation (z : Plane) :
    fixedFirst * fixedEmbedding (Multiplicative.ofAdd z) * fixedFirst⁻¹ =
      fixedEmbedding (Multiplicative.ofAdd (firstMap z)) := by
  apply Subtype.ext
  change (MulAut.conj langWitness) firstWord *
    (MulAut.conj langWitness) (splitEmbedding (Multiplicative.ofAdd z)) *
    ((MulAut.conj langWitness) firstWord)⁻¹ =
    (MulAut.conj langWitness) (splitEmbedding (Multiplicative.ofAdd (firstMap z)))
  have h := congrArg (MulAut.conj langWitness) (first_conjugates z)
  simpa only [map_mul, map_inv] using h

lemma fixedSecond_conjugation (z : Plane) :
    fixedSecond * fixedEmbedding (Multiplicative.ofAdd z) * fixedSecond⁻¹ =
      fixedEmbedding (Multiplicative.ofAdd (secondMap z)) := by
  apply Subtype.ext
  change (MulAut.conj langWitness) secondWord *
    (MulAut.conj langWitness) (splitEmbedding (Multiplicative.ofAdd z)) *
    ((MulAut.conj langWitness) secondWord)⁻¹ =
    (MulAut.conj langWitness) (splitEmbedding (Multiplicative.ofAdd (secondMap z)))
  have h := congrArg (MulAut.conj langWitness) (second_conjugates z)
  simpa only [map_mul, map_inv] using h

/-- The seven-plane and its two marked ambient conjugators in genuine fixed points. -/
def fixedData : Data (fixedSubgroup P) where
  embedding := fixedEmbedding
  embedding_injective := fixedEmbedding_injective
  first := fixedFirst
  second := fixedSecond
  first_conjugation := fixedFirst_conjugation
  second_conjugation := fixedSecond_conjugation

private def transport {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (d : Data G) : Data H where
  embedding := f.comp d.embedding
  embedding_injective := hf.comp d.embedding_injective
  first := f d.first
  second := f d.second
  first_conjugation z := by
    have h := congrArg f (d.first_conjugation z)
    simpa only [map_mul, map_inv, MonoidHom.comp_apply] using h
  second_conjugation z := by
    have h := congrArg f (d.second_conjugation z)
    simpa only [map_mul, map_inv, MonoidHom.comp_apply] using h

end
end Triality.Standard.BinarySevenPlane

namespace Triality.Standard
open QuaternionSevenPlane ConcreteBruhat.FixedDescent
/-- A marked order-49 plane with quaternion conjugations in the genuine `³D₄(2)`
carrier: the original elementary fixed group modulo its own center. -/
noncomputable def binarySevenPlane : Data (BinaryCarrier 1 Nat.zero_lt_one) :=
  BinarySevenPlane.transport
    (carrierFixedEquiv (binaryParameters 1 Nat.zero_lt_one) BinarySevenPlane.prime_two).symm.toMonoidHom
    (carrierFixedEquiv (binaryParameters 1 Nat.zero_lt_one) BinarySevenPlane.prime_two).symm.injective
    BinarySevenPlane.fixedData

end Triality.Standard
