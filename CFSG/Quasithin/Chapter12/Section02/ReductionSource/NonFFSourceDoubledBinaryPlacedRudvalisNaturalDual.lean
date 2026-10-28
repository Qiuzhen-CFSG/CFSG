module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPlacedNative
public import Theory.Representation.PSL3Two.NaturalDualTransitiveObstruction

/-!
# Natural--dual exclusion for the placed Rudvalis local

The native Chapter 12 geometry supplies a quotient residual acting on the
complete order-64 orbit.  This module transports that action to the abstract
natural--dual representation and applies the axis obstruction.  The only
remaining model-specific premise is the concrete transitivity of each native
order-64 row normalizer; it is exposed as an explicit witness so the finite
Rudvalis certificate can discharge it independently.

Source: Aschbacher--Smith 4.4.3, printed pp.622--623, and the natural--dual
marking in Chapter 12.  The transport follows the literal quotient and
inclusion maps of `BinaryPlacedNativeGeometry`.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory ChapterB.QuasisimpleSource
open Chapter7.NormalizedSource Chapter4 Chapter4.Section04
open Representation Representation.BinaryOffender BinaryLinearThree
open scoped IsMulCommutative
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

omit [Finite G] in
/-- The placed natural--dual geometry is impossible once the native row
normalizer supplies transitivity on the order-64 orbit. -/
theorem native_geometry_false_of_transitivity
    (A : Subgroup G) (K : Subgroup (normalizer (A : Set G)))
    (hr : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (e : (K ⧸ center K) ≃* Rudvalis.Model)
    (hg : D.BinaryPlacedNativeGeometry A K hr e)
    (htrans : ∀ (m : K.map (normalizer (A : Set G)).subtype ≃* Rudvalis.Model)
      (hWK : D.sourceOrbit ≤ K.map (normalizer (A : Set G)).subtype),
      let w := m.toMonoidHom.comp (inclusion hWK)
      ∀ x y : w.range, x ≠ 1 → y ≠ 1 →
        ∃ p : normalizer (w.range : Set Rudvalis.Model),
          p.val * x.val * p.val⁻¹ = y.val) : False := by
  let K₀ := K.map (normalizer (A : Set G)).subtype
  let R := oddActorResidual L A
  let W := D.sourceOrbit
  obtain ⟨_,_,m,hm,huQ,hp,hWK,hcard,hwcore,hwcentral,hmove,hN_eq,hnormal,
    ⟨t,ht,hnt,eR,E,hE,hV,hVt⟩⟩ := hg
  let r := m.toMonoidHom.comp (inclusion hr)
  let w := m.toMonoidHom.comp (inclusion hWK)
  let eMul : Multiplicative NaturalDual.Space ≃* W :=
    E.symm.toAddEquiv.toMultiplicative.trans
      (MulEquiv.toMultiplicative_toAdditive :
        Multiplicative (Additive W) ≃* W)
  let u : Multiplicative NaturalDual.Space →* Rudvalis.Model :=
    w.comp eMul.toMonoidHom
  have hu : Function.Injective u := by
    exact m.injective.comp (inclusion_injective hWK) |>.comp eMul.injective
  have hu_range : u.range = w.range := by
    apply le_antisymm
    · rintro z ⟨v, rfl⟩
      exact ⟨eMul v, rfl⟩
    · rintro z ⟨v, rfl⟩
      obtain ⟨v', rfl⟩ := eMul.surjective v
      exact ⟨v', rfl⟩
  have hpW : IsPGroup 2 w.range := by
    exact (IsElementaryAbelian.isPGroup 2 W).of_surjective
      w.rangeRestrict w.rangeRestrict_surjective
  have hWne : w.range ≠ ⊥ := by
    intro hzero
    rw [hzero, card_bot] at hcard
    omega
  have hNWlocal : IsTwoLocal (normalizer (w.range : Set Rudvalis.Model)) :=
    ⟨w.range,hWne,hpW,rfl⟩
  have hNRW : normalizer (r.range : Set Rudvalis.Model) ≤
      normalizer (w.range : Set Rudvalis.Model) := by
    exact (normal_subgroupOf_iff_le_normalizer
      (hnormal (normalizer (r.range : Set Rudvalis.Model)) huQ.1.1
        r.range.le_normalizer).2.1).mp
      (hnormal (normalizer (r.range : Set Rudvalis.Model)) huQ.1.1
        r.range.le_normalizer).2.2
  have hRW : r.range ≤ normalizer (w.range : Set Rudvalis.Model) :=
    r.range.le_normalizer.trans hNRW
  have hNWR : (r.range.subgroupOf (normalizer (w.range : Set Rudvalis.Model))).Normal :=
    (hnormal (normalizer (w.range : Set Rudvalis.Model)) hNWlocal hRW).1
  let q : R →* BinaryLinearThree.Group :=
    eR.toMonoidHom.comp (QuotientGroup.mk' _)
  have hq : Function.Surjective q := eR.surjective.comp (QuotientGroup.mk'_surjective _)
  have hEP : u.range ≤ normalizer (w.range : Set Rudvalis.Model) := by
    rw [hu_range]
    exact le_normalizer
  have hUN : (u.range.subgroupOf (normalizer (w.range : Set Rudvalis.Model))).Normal := by
    rw [hu_range]
    exact (hnormal (normalizer (w.range : Set Rudvalis.Model)) hNWlocal hRW).2.2
  have ha (x : R) (v : NaturalDual.Space) :
      r x * u (Multiplicative.ofAdd v) * (r x)⁻¹ =
        u (Multiplicative.ofAdd (NaturalDual.action (q x) v)) := by
    change r x * w (eMul (Multiplicative.ofAdd v)) * (r x)⁻¹ =
      w (eMul (Multiplicative.ofAdd (NaturalDual.action (q x) v)))
    change r x * w (E.symm v).toMul * (r x)⁻¹ =
      w (E.symm (NaturalDual.action (eR (QuotientGroup.mk' _ x)) v)).toMul
    exact hE x v
  have htr : ∀ x y : u.range, x ≠ 1 → y ≠ 1 →
      ∃ p : normalizer (w.range : Set Rudvalis.Model),
        p.val * x.val * p.val⁻¹ = y.val := by
    rw [hu_range]
    intro x y hx hy
    simpa only [hu_range] using htrans m hWK x y hx hy
  exact BinaryLinearThree.NaturalDual.no_transitive_mapped_conjugation
    r q hq u hu ha (normalizer (w.range : Set Rudvalis.Model)) hRW hEP hNWR hUN htr

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
