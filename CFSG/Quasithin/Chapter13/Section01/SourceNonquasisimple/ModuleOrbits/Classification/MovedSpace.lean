module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification.ReducedAction
public import Theory.Representation.NormalElementaryQuotient.SubgroupSpace

/-!
# Literal coordinates on the moved module

The commutator of the internal reduced subgroup with the internal copy of L
maps to U=[R₂(N_G(L)),L]. The subgroup-space commutator theorem identifies its
binary vector space with the moved space of the original quotient action.
The resulting coordinates preserve ambient elements and intertwine the whole
normalizer action, and hence the original component map.

The fixed subspace is exactly C_U(L); the binary dimension is the source
rank of U. These identifications retain the quotient and centralizer
conventions needed when the three surviving B.5 rows are converted into
four moved-module markings. They make no classification assumption.
Source: Aschbacher--Smith 13.1.8--10, printed pp.869--872.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterB.SourceInduction
open NormalElementaryQuotient ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]

@[expose] def internalMoved (L : Subgroup G) : Subgroup (NormalizerReducedAction.Ambient L) :=
  ⁅NormalizerReducedAction.Core L, L.subgroupOf (NormalizerReducedAction.Ambient L)⁆

omit [Finite G] in
theorem internalMoved_map (L : Subgroup G) :
    (internalMoved L).map (NormalizerReducedAction.Ambient L).subtype = normalizerMoved L := by
  rw [internalMoved, map_commutator, map_subgroupOf_eq_of_le L.le_normalizer,
    normalizerMoved_eq]

omit [Finite G] in
theorem internalMoved_le_core (L : Subgroup G) :
    internalMoved L ≤ NormalizerReducedAction.Core L := commutator_le_left _ _

omit [Finite G] in
theorem internalMoved_space (L : Subgroup G) :
    subgroupSpace (NormalizerReducedAction.Core L) (internalMoved L) =
      moved (reducedRepresentation L) (NormalizerReducedAction.componentImage L) := by
  rw [internalMoved, subgroupSpace_commutator _ (NormalizerReducedAction.quotient L)
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) _ _ le_rfl]
  have ht : subgroupSpace (NormalizerReducedAction.Core L)
      (NormalizerReducedAction.Core L) = ⊤ := by
    ext v
    exact iff_of_true v.toMul.property Submodule.mem_top
  rw [ht, NormalizerReducedAction.componentImage_eq]
  rfl

/-- Coordinates identify the actual U with the moved space of the reduced action. -/
def movedCoordinates (L : Subgroup G) : normalizerMoved L ≃*
    Multiplicative (moved (reducedRepresentation L) (NormalizerReducedAction.componentImage L)) := by
  let ei := ((internalMoved L).equivMapOfInjective
    (NormalizerReducedAction.Ambient L).subtype
    (NormalizerReducedAction.Ambient L).subtype_injective).trans
      (MulEquiv.subgroupCongr (internalMoved_map L))
  let ec : internalMoved L ≃*
      Multiplicative (subgroupSpace (NormalizerReducedAction.Core L) (internalMoved L)) := {
    toFun x := Multiplicative.ofAdd ⟨Additive.ofMul ⟨x, internalMoved_le_core L x.property⟩,
      x.property⟩
    invFun x := ⟨x.toAdd.val.toMul, x.toAdd.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  exact ei.symm.trans (ec.trans (LinearEquiv.ofEq _ _ (internalMoved_space L)).toAddEquiv.toMultiplicative)

omit [Finite G] in
/-- The vector coordinates are the original ambient group elements. -/
theorem movedCoordinates_val (L : Subgroup G) (u : normalizerMoved L) :
    (((movedCoordinates L u).toAdd.val.toMul : NormalizerReducedAction.Ambient L) : G) = u := by
  let e := (internalMoved L).equivMapOfInjective
    (NormalizerReducedAction.Ambient L).subtype
    (NormalizerReducedAction.Ambient L).subtype_injective
  let v := (MulEquiv.subgroupCongr (internalMoved_map L)).symm u
  have he := congrArg Subtype.val (e.apply_symm_apply v)
  simp [movedCoordinates]
  change (((e.symm v : internalMoved L) : NormalizerReducedAction.Ambient L) : G) = u
  change (((e.symm v : internalMoved L) : NormalizerReducedAction.Ambient L) : G) = (v : G) at he
  exact he.trans (MulEquiv.subgroupCongr_symm_apply (internalMoved_map L) u)

omit [Finite G] in
/-- Equivariance holds for the whole original normalizer and quotient map. -/
theorem movedCoordinates_equivariant (L : Subgroup G)
    (m : NormalizerReducedAction.Ambient L) (u : normalizerMoved L) :
    (movedCoordinates L (action L m u)).toAdd.val =
      reducedRepresentation L (NormalizerReducedAction.quotient L m)
        (movedCoordinates L u).toAdd.val := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  have h := congrArg Subtype.val (reducedRepresentation_apply L m
    (movedCoordinates L u).toAdd.val)
  change _ = ((reducedRepresentation L (NormalizerReducedAction.quotient L m)
    (movedCoordinates L u).toAdd.val).toMul : G)
  rw [h, movedCoordinates_val]
  change (m : G) * (u : G) * (m : G)⁻¹ =
    (m : G) * (((movedCoordinates L u).toAdd.val.toMul : NormalizerReducedAction.Ambient L) : G) * (m : G)⁻¹
  rw [movedCoordinates_val]

omit [Finite G] in
/-- Component equivariance uses the original map from L, not a new marking. -/
theorem movedCoordinates_component (L : Subgroup G) (l : L) (u : normalizerMoved L) :
    (movedCoordinates L (componentAction L l u)).toAdd.val =
      reducedRepresentation L (NormalizerReducedAction.componentMap L l)
        (movedCoordinates L u).toAdd.val := by
  rw [NormalizerReducedAction.componentMap_eq]
  exact movedCoordinates_equivariant L (inclusion L.le_normalizer l) u

omit [Finite G] in
/-- The central subspace in B.5 is the literal C_U(L). -/
theorem movedCoordinates_fixed_iff (L : Subgroup G) (u : normalizerMoved L) :
    (movedCoordinates L u).toAdd.val ∈
      fixedSpace (reducedRepresentation L) (NormalizerReducedAction.componentImage L) ↔
      (u : G) ∈ centralizer (L : Set G) := by
  have hfix (l : L) :
      reducedRepresentation L (NormalizerReducedAction.componentMap L l)
          (movedCoordinates L u).toAdd.val = (movedCoordinates L u).toAdd.val ↔
        componentAction L l u = u := by
    rw [← movedCoordinates_component]
    constructor
    · intro he
      apply (movedCoordinates L).injective
      exact congrArg Multiplicative.ofAdd (Subtype.ext he)
    · intro he
      rw [he]
  constructor
  · intro hf l hl
    have he := (hfix ⟨l,hl⟩).mp (hf ⟨NormalizerReducedAction.componentMap L ⟨l,hl⟩,
      NormalizerReducedAction.componentMap_range L ▸ ⟨⟨l,hl⟩,rfl⟩⟩)
    have he' := congrArg Subtype.val he
    change l * (u : G) * l⁻¹ = (u : G) at he'
    exact mul_inv_eq_iff_eq_mul.mp he'
  · intro hc a
    have ha : (a : NormalizerReducedAction.Star L) ∈
        (NormalizerReducedAction.componentMap L).range :=
      (NormalizerReducedAction.componentMap_range L).symm ▸ a.property
    obtain ⟨l,hl⟩ := ha
    change reducedRepresentation L (a : NormalizerReducedAction.Star L)
      (movedCoordinates L u).toAdd.val = _
    rw [← hl]
    apply (hfix l).mpr
    apply Subtype.ext
    change (l : G) * (u : G) * (l : G)⁻¹ = (u : G)
    rw [hc l l.property, mul_inv_cancel_right]

/-- The source group rank is the dimension of this same moved space. -/
theorem movedCoordinates_rank (L : Subgroup G) :
    rank (normalizerMoved L) = Module.finrank (ZMod 2)
      (moved (reducedRepresentation L) (NormalizerReducedAction.componentImage L)) := by
  have hc := Nat.card_congr (movedCoordinates L).toEquiv
  change Nat.card (normalizerMoved L) =
    Nat.card (moved (reducedRepresentation L) (NormalizerReducedAction.componentImage L)) at hc
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := moved (reducedRepresentation L) (NormalizerReducedAction.componentImage L)),
    Nat.card_zmod] at hc
  unfold rank
  rw [hc, Nat.log_pow (by decide : 1 < 2)]

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
