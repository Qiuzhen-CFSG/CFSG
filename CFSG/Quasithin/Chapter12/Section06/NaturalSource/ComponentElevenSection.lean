module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentRankOneEleven
public import Theory.Representation.BinaryPrimeDegree

/-!
# The original binary degree and point-span lower bound

The actual PSL2(11) component has an element of order eleven. Its faithful
restriction in the original H-star action therefore requires at least ten
binary dimensions. Apply this to the literal U_H/V1 action, then use the
original point order two to obtain |U_H| at least 2^11. No irreducibility
or changed quotient is assumed.

The upper bound through O2(L1), needed to contradict this lower bound, is
still an independent local step of this same original source argument.
Source: Aschbacher--Smith, proof of 12.6.26, printed p.833.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
  (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)



include hz hTV hTz hbound hH hn a in
/-- Every faithful binary action of the original H-star has degree at least ten. -/
theorem SourceHypothesis.original_selectedComponent_binary_degree
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (Nonabelian.Setup.Hstar H) W)
    (hσ : Function.Injective σ) : 10 ≤ Module.finrank (ZMod 2) W := by
  obtain ⟨F,hfield,hfinite,hF,⟨e⟩⟩ :=
    S.original_selectedComponent_linearTwoEleven D hZ z hz hTV hTz hbound hH hn c a hTI hns
  let := hfield
  let := hfinite
  let B := Nonabelian.Setup.star H c.K
  have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice
    (F := F) (hF ▸ (by decide : Odd 11))
  rw [←Nat.card_congr e.toEquiv,hF] at hc
  have hd : 11 ∣ Nat.card B := by
    have he : Nat.card B = 660 := by dsimp [B]; omega
    rw [he]
    decide
  have hlow := Representation.BinaryPrimeDegree.orderOf_le_finrank
    (σ.comp B.subtype) (hσ.comp B.subtype_injective) (by decide : Nat.Prime 11) (by decide) hd
  rwa [Representation.BinaryPrimeDegree.orderOf_two_mod_eleven] at hlow

include hz hTV hTz hbound hH hn a in
/-- Applying the degree bound to the literal faithful U_H/V1 quotient gives
its original point span order at least 2^11, as used in the final PSL2(11) contradiction. -/
theorem SourceHypothesis.original_selectedComponent_pointSpan_large
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    2^11 ≤ Nat.card ((D.fullSetup hZ T z).UH H) := by
  let E := D.fullSetup hZ T z
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  let : (E.V₁.subgroupOf (E.UH H)).Normal := h.point_normal_in_UH
  let : IsElementaryAbelian 2 (E.UH H ⧸ E.V₁.subgroupOf (E.UH H)) := h.point_quotient_elementary
  obtain ⟨σ,κ,hσ,_⟩ := h.faithful_point_quotient
  let W := Additive (E.UH H ⧸ E.V₁.subgroupOf (E.UH H))
  have hdim := S.original_selectedComponent_binary_degree D hZ z hz hTV hTz hbound hH hn c a hTI hns (W := W) σ hσ
  have hcard : Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  have hq : Nat.card (E.UH H ⧸ E.V₁.subgroupOf (E.UH H)) =
      2 ^ Module.finrank (ZMod 2) W := hcard
  have hle : E.V₁ ≤ E.UH H := E.V₁_le_V₅.trans (le_conjugateSpanBy E.V₅ H)
  have hpoint : Nat.card (E.V₁.subgroupOf (E.UH H)) = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
    exact E.point_card hz
  have hc := card_eq_card_quotient_mul_card_subgroup (E.V₁.subgroupOf (E.UH H))
  rw [hq,hpoint] at hc
  calc
    2^11 = 2^10 * 2 := by norm_num
    _ ≤ 2 ^ Module.finrank (ZMod 2) W * 2 :=
      Nat.mul_le_mul_right 2 (Nat.pow_le_pow_right (by decide) hdim)
    _ = Nat.card (E.UH H) := hc.symm

end CFSG.Quasithin.Chapter12.Section06
