module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner.ActorCalculation.Interface
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Tactic.FinCases

/-!
# Inner placement of the marked partner actors

The recognized element t exchanges the natural and dual summands, so its
actor is noninner. Since the actual inner subgroup has index two, every
noninner actor also exchanges the summands. Projection to the natural
coordinate is injective on its fixed vectors, giving at most eight of them.

In the separate marked coordinates, each point translation fixes at least
sixteen vectors. The small calculation uses four translation matrices and
64 pairs of binary three-vectors; the dot product supplies actual dual
vectors. Transporting both fixed sets through their literal coordinate maps
excludes every noninner marked actor, without identifying the two splittings.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.56(3–5), 15.3.58(1,3), and the proof of 15.3.59,
printed pp.1147–1150 (PDF pp.1164–1167).
-/

open Subgroup Matrix
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner
open CFSG.Quasithin.Chapter15.Section03.Nonabelian
open BinaryLinearThree Matrix.PSL3Two

private def inCoordinates {Q : Type*} [Group Q]
    (e : Q ≃* Multiplicative NaturalDualSpace) (a : MulAut Q) :
    NaturalDualSpace ≃+ NaturalDualSpace :=
  MulEquiv.toAdditive (e.symm.trans (a.trans e))

private lemma inCoordinates_mul {Q : Type*} [Group Q]
    (e : Q ≃* Multiplicative NaturalDualSpace) (a b : MulAut Q)
    (v : NaturalDualSpace) :
    inCoordinates e (a * b) v = inCoordinates e a (inCoordinates e b v) := by
  change e (a (b (e.symm _))) = e (a (e.symm (e (b (e.symm _)))))
  rw [MulEquiv.symm_apply_apply]

private lemma fixed_fst_injective (e : NaturalDualSpace ≃+ NaturalDualSpace)
    (he : ∀ f, (e (0, f)).2 = 0) :
    Function.Injective (fun v : {v : NaturalDualSpace // e v = v} => v.val.1) := by
  intro v w h
  apply Subtype.ext
  have hf : e (v.val - w.val) = v.val - w.val := by
    rw [map_sub, v.property, w.property]
  have hz : v.val - w.val = (0, v.val.2 - w.val.2) := by
    apply Prod.ext
    · exact sub_eq_zero.mpr h
    · rfl
  have hs := he (v.val.2 - w.val.2)
  rw [← hz, hf] at hs
  exact Prod.ext h (sub_eq_zero.mp hs)

private lemma fixed_card_le_eight (e : NaturalDualSpace ≃+ NaturalDualSpace)
    (he : ∀ f, (e (0, f)).2 = 0) :
    Nat.card {v : NaturalDualSpace // e v = v} ≤ 8 := by
  have h := Nat.card_le_card_of_injective _ (fixed_fst_injective e he)
  have hc : Nat.card Vector = 8 := by
    rw [Nat.card_eq_fintype_card]
    decide
  exact hc ▸ h

variable {G : Type*} [Group G]
variable {T Z ZS V : Subgroup G} {t : G}
variable [(Z.subgroupOf (closureU Z ZS)).Normal]

private lemma t_not_inner (d : RecognizedAction T Z ZS V t) :
    d.actorEquiv (actorProjection Z ⟨t, d.t_mem_H⟩) ∉ MulAut.innerSubgroup SL := by
  rintro ⟨g, hg⟩
  let v : Vector := ![1, 0, 0]
  have hs := d.swaps_natural v
  have he := congrArg Prod.fst (d.equivariant ⟨t, d.t_mem_H⟩ g hg.symm
    (d.coordinates.symm (Multiplicative.ofAdd (v, 0))))
  simp only [MulEquiv.apply_symm_apply] at he
  have hzero : W g v = 0 := he.symm.trans hs
  have hinj : Function.Injective (W g) :=
    (LinearMap.GeneralLinearGroup.toLinearEquiv (W.asGroupHom g)).injective
  have hv : v = 0 := hinj (hzero.trans (map_zero (W g)).symm)
  exact (by decide : v ≠ 0) hv

private lemma inner_action (d : RecognizedAction T Z ZS V t)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (a : ActorQuotient Z) (g : SL) (ha : d.actorEquiv a = MulAut.conj g)
    (v : NaturalDualSpace) :
    inCoordinates d.coordinates (faithfulActorAction hkernel a) v =
      (W g v.1, W.dual g v.2) := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (centralizerH Z)) a
  change (d.coordinates (quotientAction Z ZS h
    (d.coordinates.symm (Multiplicative.ofAdd v)))).toAdd = _
  simpa only [MulEquiv.apply_symm_apply, toAdd_ofAdd] using
    d.equivariant h g ha (d.coordinates.symm (Multiplicative.ofAdd v))

private lemma outer_swaps_dual (d : RecognizedAction T Z ZS V t)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (a : ActorQuotient Z) (ha : d.actorEquiv a ∉ MulAut.innerSubgroup SL) :
    ∀ f, (inCoordinates d.coordinates (faithfulActorAction hkernel a) (0, f)).2 = 0 := by
  let b := actorProjection Z ⟨t, d.t_mem_H⟩
  have hb : d.actorEquiv b ∉ MulAut.innerSubgroup SL := t_not_inner d
  have hm : d.actorEquiv (a * b⁻¹) ∈ MulAut.innerSubgroup SL := by
    rw [map_mul, map_inv]
    exact (Subgroup.mul_mem_iff_of_index_two
      Matrix.PSL3Two.Automorphisms.card_outer_sl).mpr
      (iff_of_false ha (fun hh => hb ((MulAut.innerSubgroup SL).inv_mem_iff.mp hh)))
  obtain ⟨g, hg⟩ := hm
  intro f
  have he : a = (a * b⁻¹) * b := by simp
  conv_lhs => rw [he, map_mul, inCoordinates_mul,
    inner_action d hkernel (a * b⁻¹) g hg.symm]
  change W.dual g (inCoordinates d.coordinates (faithfulActorAction hkernel b) (0, f)).2 = 0
  have hs : (inCoordinates d.coordinates (faithfulActorAction hkernel b) (0, f)).2 = 0 :=
    d.swaps_dual f
  rw [hs, map_zero]

private def translation (a b : ZMod 2) : SL :=
  ⟨!![1,a,b; 0,1,0; 0,0,1], by simp [Matrix.det_fin_three]⟩

private lemma translation_eq (x : SL) (hx : x ∈ MarkedAutomorphisms.pointV) :
    x = translation (x.val 0 1) (x.val 0 2) := by
  rcases hx with ⟨h00, h10, h20, h11, h12, h21, h22⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [translation, h00, h10, h20, h11, h12, h21, h22]

private lemma translation_inv : ∀ a b : ZMod 2,
    (translation a b)⁻¹ = translation a b := by
  intro a b
  apply inv_eq_of_mul_eq_one_right
  revert a b
  decide +kernel

private abbrev fixedParameters (a b : ZMod 2) :=
  {p : Vector × Vector // a * p.1 1 + b * p.1 2 = 0 ∧ p.2 0 = 0}

private lemma fixedParameters_card : ∀ a b : ZMod 2,
    16 ≤ Fintype.card (fixedParameters a b) := by
  decide +kernel

private lemma translation_fixes (a b : ZMod 2) (p : fixedParameters a b) :
    (W (translation a b) p.val.1,
      W.dual (translation a b) (dotProductEquiv (ZMod 2) (Fin 3) p.val.2)) =
      (p.val.1, dotProductEquiv (ZMod 2) (Fin 3) p.val.2) := by
  apply Prod.ext
  · change (translation a b).val *ᵥ p.val.1 = p.val.1
    ext i
    fin_cases i <;>
      simp [translation, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        add_assoc, p.property.1]
  · apply LinearMap.ext
    intro v
    change p.val.2 ⬝ᵥ ((translation a b)⁻¹.val *ᵥ v) = p.val.2 ⬝ᵥ v
    rw [translation_inv]
    simp [translation, Matrix.mulVec, dotProduct, Fin.sum_univ_three, p.property.2]

private lemma point_fixed_card (x : MarkedAutomorphisms.pointV) :
    16 ≤ Nat.card {v : NaturalDualSpace // (W x.val v.1, W.dual x.val v.2) = v} := by
  classical
  let : Finite (Module.Dual (ZMod 2) Vector) :=
    Finite.of_equiv Vector (dotProductEquiv (ZMod 2) (Fin 3)).toEquiv
  let a := x.val.val 0 1
  let b := x.val.val 0 2
  let f : fixedParameters a b →
      {v : NaturalDualSpace // (W x.val v.1, W.dual x.val v.2) = v} :=
    fun p => ⟨(p.val.1, dotProductEquiv (ZMod 2) (Fin 3) p.val.2), by
      rw [translation_eq x.val x.property]
      exact translation_fixes a b p⟩
  have hi : Function.Injective f := by
    intro p q h
    apply Subtype.ext
    exact Prod.ext (congrArg (fun v => v.val.1) h)
      ((dotProductEquiv (ZMod 2) (Fin 3)).injective (congrArg (fun v => v.val.2) h))
  have hc : 16 ≤ Nat.card (fixedParameters a b) := by
    rw [Nat.card_eq_fintype_card]
    exact fixedParameters_card a b
  exact hc.trans (Nat.card_le_card_of_injective f hi)

private lemma fixed_card_coordinates {Q : Type*} [Group Q]
    (e : Q ≃* Multiplicative NaturalDualSpace) (a : MulAut Q) :
    Nat.card {w : Q // a w = w} =
      Nat.card {v : NaturalDualSpace // inCoordinates e a v = v} := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (show Q ≃ NaturalDualSpace from e.toEquiv) ?_
  intro w
  change a w = w ↔ e (a (e.symm (e w))) = e w
  rw [MulEquiv.symm_apply_apply, e.injective.eq_iff]

private lemma marked_fixed_card
    {V₀ : Subgroup G} {y : G} {hXH : partnerX Z ZS y ≤ centralizerH Z}
    (m : MarkedAction Z ZS V₀ y t hXH) (x : partnerX Z ZS y) :
    16 ≤ Nat.card {w : VectorQuotient Z ZS //
      quotientAction Z ZS ⟨x, hXH x.property⟩ w = w} := by
  rw [fixed_card_coordinates m.coordinates]
  have he (v : NaturalDualSpace) :
      inCoordinates m.coordinates (quotientAction Z ZS ⟨x, hXH x.property⟩) v =
        (W (m.parameter x).val v.1, W.dual (m.parameter x).val v.2) := by
    change (m.coordinates (quotientAction Z ZS ⟨x, hXH x.property⟩
      (m.coordinates.symm (Multiplicative.ofAdd v)))).toAdd = _
    simpa only [MulEquiv.apply_symm_apply, toAdd_ofAdd] using
      m.equivariant x (m.coordinates.symm (Multiplicative.ofAdd v))
  simp only [he]
  exact point_fixed_card (m.parameter x)

/-- The marked partner four-group acts through the actual inner automorphisms.
The natural and marked coordinates need not agree. -/
public theorem marked_actorImage_le_inner [Finite G]
    (d : RecognizedAction T Z ZS V t)
    {V₀ : Subgroup G} {y : G} (hXH : partnerX Z ZS y ≤ centralizerH Z)
    (m : MarkedAction Z ZS V₀ y t hXH)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z)) :
    (actorImage Z (partnerX Z ZS y)).map d.actorEquiv.toMonoidHom ≤
      MulAut.innerSubgroup SL := by
  rintro _ ⟨a, ha, rfl⟩
  by_contra hn
  obtain ⟨x, hx, rfl⟩ := ha
  have hu := fixed_card_le_eight
    (inCoordinates d.coordinates (faithfulActorAction hkernel (actorProjection Z x)))
    (outer_swaps_dual d hkernel (actorProjection Z x) hn)
  rw [← fixed_card_coordinates] at hu
  rw [faithfulActorAction_projection] at hu
  have hl := marked_fixed_card m (⟨x, hx⟩ : partnerX Z ZS y)
  have he : (⟨(⟨x, hx⟩ : partnerX Z ZS y), hXH hx⟩ : centralizerH Z) = x :=
    Subtype.ext rfl
  rw [he] at hl
  omega

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner
