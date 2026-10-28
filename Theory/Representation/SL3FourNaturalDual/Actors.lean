module
public import Theory.Representation.SL3FourNaturalDual
public import Theory.Representation.BinaryOffender.Defs
/-!
# Marked root and graph actors on the SL₃(4) module

The highest-root parameterization is a homomorphism from the additive F₄.
Its image has order four, binary rank two, and fixed codimension four on the
natural-plus-dual module. Interchanging the summands intertwines the matrix
action with inverse transpose, so the displayed interchange is the genuine
graph action. Classification of arbitrary quadratic actors is separate.

Source: Aschbacher--Smith, proof of 13.8.20, printed p.955 (1 March 2004).
-/

@[expose] public section
noncomputable section
namespace Representation.SL3FourNaturalDual

def rootHom : Multiplicative F →* SL where
  toFun a := root a.toAdd
  map_one' := root_zero
  map_mul' a b := (root_mul a.toAdd b.toAdd).symm

def rootGroup : Subgroup SL := rootHom.range

lemma rootGroup_card : Nat.card rootGroup = 4 := by
  have hi : Function.Injective rootHom := fun _ _ h => root_injective h
  unfold rootGroup
  rw [← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv]
  change Nat.card F = 4
  rw [Nat.card_eq_fintype_card, SL2FourNatural.card_field]

lemma rootGroup_rank : BinaryOffender.rank rootGroup = 2 := by
  change Nat.log 2 (Nat.card rootGroup) = 2
  rw [rootGroup_card]
  decide

lemma fixedSpace_rootGroup : BinaryOffender.fixedSpace representation rootGroup = rootFixed := by
  ext v
  constructor
  · intro hv
    apply (mem_rootFixed v).mpr
    intro a
    exact hv ⟨root a, ⟨Multiplicative.ofAdd a, rfl⟩⟩
  · intro hv g
    obtain ⟨g, a, rfl⟩ := g
    exact (mem_rootFixed v).mp hv a.toAdd

lemma fixedCodim_rootGroup : BinaryOffender.fixedCodim representation rootGroup = 4 := by
  change Module.finrank (ZMod 2) (V ⧸ BinaryOffender.fixedSpace representation rootGroup) = 4
  rw [fixedSpace_rootGroup, root_fixedCodim]

lemma inverseTranspose_involutive (g : SL) :
    Matrix.SpecialLinearGroup.inverseTranspose (Matrix.SpecialLinearGroup.inverseTranspose g) = g := by
  change ((Matrix.SpecialLinearGroup.inverseTranspose g)⁻¹).transpose = g
  rw [← map_inv]
  change ((g⁻¹)⁻¹).transpose.transpose = g
  rw [inv_inv]
  apply Subtype.ext
  rfl

lemma graphSwap_equivariant (g : SL) (v : V) :
    graphSwap (representation g v) =
      representation (Matrix.SpecialLinearGroup.inverseTranspose g) (graphSwap v) := by
  change (natural (Matrix.SpecialLinearGroup.inverseTranspose g) v.2, natural g v.1) =
    (natural (Matrix.SpecialLinearGroup.inverseTranspose g) v.2,
      natural (Matrix.SpecialLinearGroup.inverseTranspose
        (Matrix.SpecialLinearGroup.inverseTranspose g)) v.1)
  rw [inverseTranspose_involutive]

end Representation.SL3FourNaturalDual
