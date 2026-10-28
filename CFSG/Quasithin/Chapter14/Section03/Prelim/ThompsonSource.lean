module

public import CFSG.Quasithin.Chapter14.Section03.Prelim.ThompsonSource.Marking
public import CFSG.Quasithin.Chapter14.Section03.Prelim.ThompsonSource.Replacement
public import Theory.Representation.PSL3Two.ThompsonEscape

/-!
# Source Thompson normality in the natural L₃(2) setup

The same coordinates identify fixed vectors of the literal centralizer-quotient
action with fixed vectors of the natural module. Equal-weight replacement and
the finite rank-one escape theorem therefore force J(T) into the two-group
action kernel. Thompson heredity gives its relative normality in the original
LT. All flags, subgroup embeddings and quotient maps are retained.

Only the genuine universal Structural1222 predecessor is explicit. No
Thompson, offender or local normality conclusion is an input. The source
consumer in `ThompsonSource.Consumer` instantiates the original universal
14.3.9(2) contract used by the Goldschmidt argument.

Source: Aschbacher–Smith, 14.3.9(1–2), printed pp.992–993; B.2.3(3), B.2.8.
-/

public section

open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section03.ThompsonSource
open Chapter12.Section08 Chapter12.Section02 Matrix.PSL3Two
open Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag

private theorem fixed_card_transport {X : Type*} [Group X] [Finite X]
    (E : Subgroup X) [E.Normal] [IsElementaryAbelian 2 E]
    (q : X →* SL) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (E : Set X)) (e : Model ≃* E)
    (he : ∀ g v, (e (slAut (q g) v) : X) = g * (e v : X) * g⁻¹)
    (B : Subgroup SL) :
    Nat.card (fixedSpace (NormalElementaryQuotient.representation E q hq hk) B) =
      Nat.card (BinaryLinearThree.ThompsonEscape.Fix B) := by
  let ρ := NormalElementaryQuotient.representation E q hq hk
  have ha (g : SL) (v : Model) :
      ρ g (Additive.ofMul (e v)) = Additive.ofMul (e (slAut g v)) := by
    obtain ⟨g, rfl⟩ := hq g
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [NormalElementaryQuotient.representation_apply]
    exact (he g v).symm
  let f : BinaryLinearThree.ThompsonEscape.Fix B ≃ fixedSpace ρ B := {
    toFun v := ⟨Additive.ofMul (e v), by
      intro b
      change ρ (b : SL) (Additive.ofMul (e v)) = _
      rw [ha]
      exact congrArg (fun x : Model => Additive.ofMul (e x))
        ((MonoidHom.mem_commonFixed slAut.toMonoidHom B v).mp v.property b b.property)⟩
    invFun v := ⟨e.symm v.val.toMul, by
      rw [BinaryLinearThree.ThompsonEscape.Fix, MonoidHom.mem_commonFixed]
      intro b hb
      apply e.injective
      apply Additive.ofMul.injective
      change Additive.ofMul (e (slAut b (e.symm v.val.toMul))) = _
      rw [← ha, e.apply_symm_apply]
      exact v.property ⟨b, hb⟩⟩
    left_inv v := by apply Subtype.ext; exact e.symm_apply_apply v
    right_inv v := by apply Subtype.ext; exact congrArg Additive.ofMul (e.apply_symm_apply v.val.toMul) }
  exact (Nat.card_congr f).symm

private theorem weight_transport {X : Type*} [Group X] [Finite X]
    (E : Subgroup X) [E.Normal] [IsElementaryAbelian 2 E]
    (q : X →* SL) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (E : Set X)) (e : Model ≃* E)
    (he : ∀ g v, (e (slAut (q g) v) : X) = g * (e v : X) * g⁻¹)
    (B : Subgroup SL) :
    weight (NormalElementaryQuotient.representation E q hq hk) B =
      weight BinaryLinearThree.W B := by
  have hc := (fixed_card_transport E q hq hk e he B).trans
    (BinaryLinearThree.ThompsonEscape.card_Fix_eq B)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := fixedSpace (NormalElementaryQuotient.representation E q hq hk) B),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace BinaryLinearThree.W B),
    Nat.card_zmod] at hc
  have hr := Nat.pow_right_injective (by decide : 1 < 2) hc
  exact congrArg (fun n => rank B + n) hr

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {K : GroupClass.{u}} (h : HigherRankHypothesis K T L V 3)
  (F : InvariantFlag T V 3) (structural : Structural1222 K)

include h structural in
theorem thompson_normal
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ F.Ri L 1) :
    ((elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf
      (L ⊔ (T : Subgroup G))).Normal := by
  obtain ⟨e, q, hq, hk2, ha, hk, hT, hR⟩ := exists_marking h F structural
  let H := L ⊔ (T : Subgroup G)
  let E := V.subgroupOf H
  have hVH : V ≤ H := h.chosen.le_sylow.trans le_sup_right
  let := h.chosen.elementary
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hVH
  let : E.Normal := (normal_subgroupOf_iff_le_normalizer hVH).mpr
    (sup_le h.chosen.normalizes (h.sylow_normalizes_seed structural))
  let a : E ≃* V := subgroupOfEquivOfLe hVH
  let e' : Model ≃* E := e.trans a.symm
  have ha' (g : H) (v : Model) :
      (e' (slAut (q g) v) : H) = g * (e' v : H) * g⁻¹ := by
    apply Subtype.ext
    exact ha g v
  have hk' : q.ker = centralizer (E : Set H) := by
    rw [hk]
    ext g
    constructor
    · intro hg v hv
      apply Subtype.ext
      exact hg v hv
    · intro hg v hv
      exact congrArg Subtype.val (hg ⟨v, hVH hv⟩ hv)
  let S : Sylow 2 H := T.subtype le_sup_right
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le fun _ hA => hA.1
  have hSmap : (S : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hJmap : (elementaryAbelianMaxJ (S : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective, hSmap]
  have hJsub : elementaryAbelianMaxJ (S : Subgroup H) =
      (elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hJmap, map_subgroupOf_eq_of_le (hJT.trans le_sup_right)]
  rw [← hJsub]
  apply thompson_normal_of_image_escape S E q hq hk' hk2
    (subgroupOf_mono _ h.chosen.le_sylow) MarkedAutomorphisms.pointV
  · rw [hJsub]
    exact hR ▸ map_mono (subgroupOf_mono _ hJ)
  · intro B hB hne _
    obtain ⟨C, _, hC, heq, _, g, hgS, hgD⟩ :=
      BinaryLinearThree.ThompsonEscape.exists_replacement_escape B hB hne
    refine ⟨C, hC, ⟨heq.1, ?_⟩, g, ?_, hgD⟩
    · rw [weight_transport E q hq hk' e' ha', weight_transport E q hq hk' e' ha']
      exact heq.2
    · exact hT ▸ hgS

end CFSG.Quasithin.Chapter14.Section03.ThompsonSource
