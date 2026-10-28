module
public import Theory.SpecificGroups.Janko3.SourceRecognition.CubicNormalizerModel
public import Theory.SpecificGroups.Janko3.SourceRecognition.CubicPairConjugacy

/-!
# The canonical full pair in the cubic-normalizer model

The pair is the full preimage of a Sylow-five normalizer in PGL₂(9).
Its order is sixty and every subgroup of that order containing the cubic
kernel is conjugate to it. Thus local model recognition can retain the
entire original pair intersection.
-/

@[expose] public noncomputable section
open Subgroup
namespace Sporadic.Janko3.SourceRecognition.CubicNormalizerModel
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

def five : Sylow 5 P := default

def pair : Subgroup Model := (normalizer (five : Set P)).comap projection

theorem five_card : Nat.card five = 5 := by
  rw [five.card_eq_multiplicity,p_card]
  decide +kernel

theorem projection_kernel_card : Nat.card projection.ker = 3 := by
  rw [projection_ker,←Nat.card_congr
    (MonoidHom.ofInjective (SemidirectProduct.inl_injective (φ := action))).toEquiv]
  simp [Z, Nat.card_eq_fintype_card, Fintype.card_multiplicative]

theorem projection_surjective : Function.Surjective projection := by
  intro p
  exact ⟨SemidirectProduct.inr p,rfl⟩

theorem kernel_le_pair : projection.ker ≤ pair := ker_le_comap _ _

private def preimageEquiv (Q : Subgroup P) : Q.comap projection ≃ Z × Q where
  toFun x := (x.val.left,⟨x.val.right,x.property⟩)
  invFun x := ⟨⟨x.1,x.2⟩,x.2.property⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

theorem pair_card : Nat.card pair = 60 := by
  have hz : Nat.card Z = 3 := by
    simp [Z, Nat.card_eq_fintype_card, Fintype.card_multiplicative]
  change Nat.card ((normalizer (five : Set P)).comap projection) = 60
  rw [Nat.card_congr (preimageEquiv (normalizer (five : Set P))),Nat.card_prod,hz]
  have hn := AlternatingSix.PGLNineFiveNormalizer.five_normalizer_card
    (five : Subgroup P) five_card
  change Nat.card (normalizer (five : Set P)) = 20 at hn
  rw [hn]

/-- Any full pair subgroup containing the cubic kernel can be moved to the
canonical pair by an actual inner automorphism of the cubic model. -/
theorem exists_conjugating_pair (H : Subgroup Model) (hH : projection.ker ≤ H)
    (hcH : Nat.card H = 60) :
    ∃ g : Model, H.map (MulAut.conj g).toMonoidHom = pair :=
  cubic_pair_overgroups_conjugate projection projection_surjective projection_kernel_card
    H pair hH kernel_le_pair hcH pair_card

end Sporadic.Janko3.SourceRecognition.CubicNormalizerModel
