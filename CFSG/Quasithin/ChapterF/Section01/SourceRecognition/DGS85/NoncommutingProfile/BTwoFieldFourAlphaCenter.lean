module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourAlphaQuotientSource
public import Theory.Representation.GeneralLinearNatural

/-!
# The full binary alpha-center action

The existing natural coordinates make the marked SL₂ representation faithful.
When the section denominator is trivial, the actual conjugation action on the
center therefore has the same kernel as the original quotient map. At field
order two both its image and the center automorphism group have order six,
so every center automorphism is induced by an actual alpha actor.

Source: DGS, *Groups and Graphs* (1985), proof of (10.9), pp.162–163.
This supplies the full-center-action premise for the order-1152 endpoint.
-/

public noncomputable section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
local instance alpha50Algebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2

private theorem center_representation_injective {v m w : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) : Function.Injective c.representation := by
  obtain ⟨d,hd⟩ := c.center_natural_coordinates E
  intro g h hgh
  apply specialLinearNatural_injective 2
  apply LinearMap.ext
  intro z
  have hh := congrArg (fun f : Module.End (ZMod 2) W => d (f (d.symm z))) hgh
  rw [hd,hd,d.apply_symm_apply] at hh
  simpa only [specialLinearNatural_apply] using hh

/-- The actual binary alpha actor induces every automorphism of its natural center. -/
theorem BTwoCenterActionData.binary_center_action_surjective
    (h : LocallyRankOneTriple P B) {v m w : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k))
    (hω : omegaCenterIn c.actor = ⊥) (hk : Nat.card k = 2) :
    Function.Surjective ((Z F v).normalizerMonoidHom.comp
      (inclusion c.coordinates.normalized)) := by
  let : ∀ i, Finite (F i) := finite_endpoints h
  let Z₀ := Z F v
  let f := Z₀.normalizerMonoidHom.comp (inclusion c.coordinates.normalized)
  have hi : Function.Injective c.coordinates.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [c.coordinates.kernel_eq,hω,bot_subgroupOf]
  have hker : f.ker = c.quotient.ker := by
    ext a
    change f a = 1 ↔ c.quotient a = 1
    constructor
    · intro ha
      apply center_representation_injective c E
      apply LinearMap.ext
      intro z
      obtain ⟨x,hx⟩ := c.coordinates.onto (Multiplicative.ofAdd z)
      have hz : (c.coordinates.coordinates x).toAdd = z := congrArg Multiplicative.toAdd hx
      have hax : f a x = x := by rw [ha]; rfl
      have he := c.coordinates.equivariant a x
      change (c.coordinates.coordinates (f a x)).toAdd = c.representation (c.quotient a)
        (c.coordinates.coordinates x).toAdd at he
      rw [hax,hz] at he
      simpa only [map_one,Module.End.one_apply] using he.symm
    · intro ha
      apply MulEquiv.ext
      intro x
      apply hi
      apply Multiplicative.toAdd.injective
      have he := c.coordinates.equivariant a x
      change (c.coordinates.coordinates (f a x)).toAdd = c.representation (c.quotient a)
        (c.coordinates.coordinates x).toAdd at he
      simpa only [ha,map_one,Module.End.one_apply,MulAut.one_apply] using he
  let d : f.range ≃* SL(2,k) :=
    (QuotientGroup.quotientKerEquivRange f).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective c.quotient c.onto))
  have hcZ : Nat.card Z₀ = 4 := by
    rw [c.central_center_card E hω,hk]
    decide
  let : Finite Z₀ := Nat.finite_of_card_ne_zero (hcZ ▸ by decide)
  let : Nontrivial Z₀ := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcZ]; decide)
  let : IsElementaryAbelian 2 Z₀ := IsElementaryAbelian.of_le (source_Z_Q_U h v).1
  let : IsKleinFour Z₀ := ⟨hcZ,IsElementaryAbelian.exponent_eq_prime⟩
  let : Fintype k := Fintype.ofFinite k
  let ek : k ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [Nat.card_eq_fintype_card,ZMod.card] using hk)
  let eSL := (Atlas.fieldEquivSL 2 ek).trans SLTwoPermThree.sl2Two_equiv_perm_three.some
  have hSL : Nat.card SL(2,k) = 6 := by
    rw [Nat.card_congr eSL.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
    decide
  apply MonoidHom.range_eq_top.mp
  apply eq_of_le_of_card_ge le_top
  rw [Nat.card_congr d.toEquiv,card_top,IsKleinFour.card_mulAut,hSL]

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
