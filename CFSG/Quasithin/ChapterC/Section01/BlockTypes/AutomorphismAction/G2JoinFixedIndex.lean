module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.G2JoinFullActor
public import Theory.Representation.G2NaturalOffenders
public import Theory.Representation.BinaryOffender.QuotientFixedIndex

/-!
# Sharp fixed indices for elementary actors on G₂ blocks

The full G₂(2) actor on the intrinsic natural quotient has kernel in
O₂(LT). Every elementary actor has rank at most its fixed codimension,
since the natural module has no strong offenders. Surjective coordinates
from U(L) retain its central kernel and bound the literal centralizer
index below by that fixed-codimension power of two.

Source: Aschbacher–Smith B.4.6(13) and 3.3.28, printed pp.88–90 and601.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.G2BlockAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- An elementary actor in LT satisfies the sharp literal fixed-index inequality. -/
theorem elementary_actor_sharp_fixed_index
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hb : IsG2TwoBlock L) (B : Subgroup G) [IsElementaryAbelian 2 B]
    (hBH : B ≤ L ⊔ (T : Subgroup G)) :
    ((L ⊔ (T : Subgroup G)).pCoreIn 2).relIndex B ≤
      (centralizer (B : Set G)).relIndex ((blockU L).map L.subtype) := by
  obtain ⟨m⟩ := hb.natural_model
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let U := (blockU L).map L.subtype
  let β := (joinFullActor hTL m).comp (inclusion hBH)
  let σ := Atlas.G2.NaturalOffenders.binaryNatural (F := ZMod 2)
  have hker : β.ker ≤ Q.subgroupOf B := by
    intro b hb
    exact mem_core_of_joinFullActor_eq_one hTL m (inclusion hBH b) hb
  have hi : Q.relIndex B ≤ Nat.card β.range := by
    exact (index_antitone hker).trans_eq (index_ker β)
  let : IsElementaryAbelian 2 β.range :=
    IsElementaryAbelian.of_surjective β.rangeRestrict β.rangeRestrict_surjective
  have hcard : Nat.card β.range ≤ 2 ^ fixedCodim σ β.range := by
    by_cases hbot : β.range = ⊥
    · rw [hbot]
      simp
      exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
    · have he : IsElementaryTwo β.range := ⟨hbot, inferInstance⟩
      have hr : rank β.range ≤ fixedCodim σ β.range := by
        apply Nat.le_of_not_gt
        intro hlt
        exact Atlas.G2.NaturalOffenders.natural_no_strong
          (F := ZMod 2) (n := 1) (by simp) (by decide) ⟨β.range, he, hlt⟩
      rw [he.card_eq_two_pow_rank]
      exact Nat.pow_le_pow_right (by decide) hr
  let e : blockU L ≃* U := (blockU L).equivMapOfInjective L.subtype L.subtype_injective
  let α : U →* Multiplicative (Atlas.G2.Natural.Space (ZMod 2)) :=
    m.moduleIso.toMonoidHom.comp ((QuotientGroup.mk' (blockFixed L)).comp e.symm.toMonoidHom)
  have hα : Function.Surjective α := m.moduleIso.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp e.symm.surjective)
  have hfixed : ∀ (x : U), (x : G) ∈ centralizer (B : Set G) →
      ∀ b : B, σ (β b) (α x).toAdd = (α x).toAdd := by
    intro x hx b
    let u := e.symm x
    have hu : ((u : L) : G) = (x : G) :=
      congrArg Subtype.val (e.apply_symm_apply x)
    have hc : MulAut.characteristic (blockU L)
        (L.normalizerMonoidHom
          (inclusion (sup_le L.le_normalizer hTL) (inclusion hBH b))) u = u := by
      apply Subtype.ext
      apply Subtype.ext
      change (b : G) * ((u : L) : G) * (b : G)⁻¹ = ((u : L) : G)
      rw [hu, hx b b.property, mul_inv_cancel_right]
    have hh := joinFullActor_modulePoint hTL m (inclusion hBH b) u
    rw [hc] at hh
    exact hh.symm
  exact hi.trans (hcard.trans (quotient_centralizer_index_le σ U B α hα β hfixed))

end CFSG.Quasithin.ChapterC.G2BlockAction
