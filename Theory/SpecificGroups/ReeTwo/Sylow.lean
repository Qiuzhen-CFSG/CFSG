module

public import Theory.SpecificGroups.ReeTwo.Centralizer

/-!
# A concrete Sylow subgroup of the Ree two centralizer

Restrict the specified five-by-four complement action to its cyclic subgroup
of order four. The resulting semidirect product has order 4096 and embeds
as a subgroup of index five in `ReeTwo.Centralizer`. This supplies an actual
Sylow model, with its core coordinates and root-1 generator retained.

Reduction modulo two on the order-four factor gives a nontrivial binary
character. No invariance under conjugation in an ambient overgroup is
claimed: that is the separate fusion obstruction needed for recognition.

Source: Shinoda (1975), (2.1)–(2.3) and (3.2), pp. 80–83.
-/

@[expose] public section
namespace ReeTwo

abbrev SylowModel :=
  Core ⋊[Core.complementAction.comp SemidirectProduct.inr] FiveFour.Cyclic 4

namespace SylowModel

instance : Fintype SylowModel := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm

theorem card : Nat.card SylowModel = 4096 := by
  rw [SemidirectProduct.card, Core.card]
  change 1024 * Nat.card (ZMod 4) = 4096
  simp

/-- Inclusion of the cyclic-four factor into the specified complement. -/
def complementEmbedding : FiveFour.Cyclic 4 →* Core.complement :=
  Core.complementAction.rangeRestrict.comp SemidirectProduct.inr

theorem complementEmbedding_injective : Function.Injective complementEmbedding := by
  intro x y h
  exact SemidirectProduct.inr_injective
    (Core.complementAction_injective (congrArg Subtype.val h))

/-- The inclusion retains the core and the complement action, not just their orders. -/
def embedding : SylowModel →* Centralizer :=
  SemidirectProduct.map (MonoidHom.id Core) complementEmbedding (fun _ => rfl)

theorem embedding_injective : Function.Injective embedding := by
  intro x y h
  apply SemidirectProduct.ext
  · exact congrArg (fun g : Centralizer => g.left) h
  · exact complementEmbedding_injective (congrArg (fun g : Centralizer => g.right) h)

theorem embedding_range_card : Nat.card embedding.range = 4096 :=
  (Nat.card_congr (MonoidHom.ofInjective embedding_injective).toEquiv.symm).trans card

theorem embedding_range_index : embedding.range.index = 5 := by
  have h := Subgroup.index_mul_card embedding.range
  rw [embedding_range_card, Centralizer.card] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 4096) h

/-- The explicit order-4096 subgroup as a Sylow subgroup of the centralizer. -/
def sylow : Sylow 2 Centralizer :=
  (IsPGroup.of_card (n := 12) embedding_range_card).toSylow
    (by rw [embedding_range_index]; decide)

/-- The coordinate model is isomorphic to its actual Sylow image. -/
noncomputable def equivSylow : SylowModel ≃* sylow :=
  MonoidHom.ofInjective embedding_injective

/-- Every Sylow subgroup of the specified centralizer has this multiplication. -/
noncomputable def equiv (P : Sylow 2 Centralizer) : SylowModel ≃* P :=
  equivSylow.trans (Sylow.equiv sylow P)

def root (i : CoreRoot) : SylowModel := SemidirectProduct.inl (Core.root i)

def rootOne : SylowModel := SemidirectProduct.inr (FiveFour.generator 4)⁻¹

@[simp] theorem embedding_root (i : CoreRoot) :
    embedding (root i) = Centralizer.root i := by
  apply SemidirectProduct.ext
  · rfl
  · exact map_one complementEmbedding

@[simp] theorem embedding_rootOne : embedding rootOne = Centralizer.rootOne := by
  change SemidirectProduct.inr (complementEmbedding (FiveFour.generator 4)⁻¹) = _
  have h : complementEmbedding (FiveFour.generator 4) = Core.complementA :=
    Subtype.ext Core.complementAction_a
  rw [map_inv, h]
  rfl

/-- Reduction from the cyclic group of order four to that of order two. -/
def parity : FiveFour.Cyclic 4 →* FiveFour.Cyclic 2 :=
  FiveFour.cyclicHom (FiveFour.generator 2) (n := 4) (by decide +kernel)

/-- Parity of the cyclic-four coordinate. -/
def character : SylowModel →* FiveFour.Cyclic 2 :=
  parity.comp SemidirectProduct.rightHom

@[simp] theorem character_root (i : CoreRoot) : character (root i) = 1 := by
  simp [character, root]

theorem character_rootOne_ne_one : character rootOne ≠ 1 := by decide +kernel

/-- Every involution is killed by parity of the cyclic-four coordinate. -/
theorem character_eq_one_of_square_eq_one (g : SylowModel) (hg : g ^ 2 = 1) :
    character g = 1 := by
  have hright : g.right ^ 2 = 1 := by
    simpa only [map_pow, map_one, SemidirectProduct.rightHom_eq_right] using congrArg
      (SemidirectProduct.rightHom : SylowModel →* FiveFour.Cyclic 4) hg
  exact (by decide +kernel : ∀ t : FiveFour.Cyclic 4, t ^ 2 = 1 → parity t = 1)
    g.right hright

theorem rootOne_order : orderOf rootOne = 4 := by
  rw [← orderOf_injective embedding embedding_injective, embedding_rootOne]
  exact Centralizer.root_one_order

end SylowModel

namespace Centralizer

/-- The parity character extends over the specified five-by-four complement. -/
noncomputable def character : Centralizer →* FiveFour.Cyclic 2 :=
  SylowModel.parity.comp
    ((SemidirectProduct.rightHom : FiveFour.Group →* FiveFour.Cyclic 4).comp
      (Core.complementEquiv.symm.toMonoidHom.comp SemidirectProduct.rightHom))

@[simp] theorem character_embedding (g : SylowModel) :
    character (SylowModel.embedding g) = SylowModel.character g := by
  change SylowModel.parity
    ((Core.complementEquiv.symm (Core.complementEquiv (SemidirectProduct.inr g.right))).right) = _
  rw [Core.complementEquiv.symm_apply_apply]
  rfl

/-- The local centralizer already separates root 1 from the parity kernel.
Only conjugation outside this centralizer remains to be controlled. -/
theorem not_isConj_embedding_rootOne (g : SylowModel) (hg : SylowModel.character g = 1) :
    ¬ IsConj (SylowModel.embedding SylowModel.rootOne) (SylowModel.embedding g) := by
  intro h
  have heq := isConj_iff_eq.mp (character.map_isConj h)
  rw [character_embedding, character_embedding, hg] at heq
  exact SylowModel.character_rootOne_ne_one heq

end Centralizer
end ReeTwo
