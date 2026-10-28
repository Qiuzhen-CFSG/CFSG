module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.RankOne
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Reciprocal transvections survive the actual quotient

Conjugation by the inverse endpoint identifies Uγ with U_H and A₁ with V₁.
Compose this isomorphism with U_H → U_H/V₁. Its equivariance transports
rank-at-most-one displacement. Strictness of D_H supplies u and v whose
commutator lies outside A₁, so the transported displacement survives V₁.
Consequently the actor survives O₂(H) and has fixed codimension exactly one.

This algebraic lemma is used by `CriticalReciprocity` after its derivation
of the transvection action from 13.8.18(3); it does not assume a reciprocal
transvection on U_H/V₁.

Source: Aschbacher–Smith, 13.8.24, printed pp.958–959, using 13.8.18(3)
and the denominators of F.9.12 (1 March 2004 manuscript).
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.CriticalReciprocity
open CriticalGeometry

private theorem quotient_fixedCodim_le
    {J X Y : Type*} [Group J] [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    [FiniteDimensional (ZMod 2) X] [FiniteDimensional (ZMod 2) Y]
    (ρ : Representation (ZMod 2) J Y) (a : J)
    (t : X ≃ₗ[ZMod 2] X) (f : X →ₗ[ZMod 2] Y) (hf : Function.Surjective f)
    (he : ∀ x, f (t x) = ρ a (f x))
    (ht : t ∈ LinearEquiv.transvections (ZMod 2) X) :
    fixedCodim ρ (zpowers a) ≤ 1 := by
  have hh : (ρ a - LinearMap.id).comp f = f.comp (t.toLinearMap - LinearMap.id) := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      map_sub, LinearEquiv.coe_coe, he]
  rw [fixedCodim_zpowers_eq_displacement_rank]
  have hr : LinearMap.range (ρ a - LinearMap.id) =
      (LinearMap.range (t.toLinearMap - LinearMap.id)).map f := by
    rw [← LinearMap.range_comp, ← hh, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr hf, Submodule.map_top]
  rw [hr]
  exact (Submodule.finrank_map_le _ _).trans
    (LinearEquiv.mem_dilatransvections_iff_finrank.mp
      (LinearEquiv.transvections_subset_dilatransvections ht))

variable {G : Type*} [Group G]

/-- Literal conjugation on the section U/Z through H/O₂(H). -/
def Compatible (H U Z : Subgroup G) [(Z.subgroupOf U).Normal]
    [IsElementaryAbelian 2 U]
    (hn : H ≤ normalizer (U : Set G))
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (U ⧸ Z.subgroupOf U))) : Prop :=
  ∀ (h : H) (u : U),
    ρ (QuotientGroup.mk' (pCore 2 H) h)
      (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) u)) =
    Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U)
      ⟨(h : G) * (u : G) * (h : G)⁻¹,
        (mem_normalizer_iff.mp (hn h.property) u).mp u.property⟩)

/-- Transport a transvection through the actual endpoint and quotient. -/
theorem reciprocal_of_axis [Finite G]
    (H U Z : Subgroup G) (g : G) [IsElementaryAbelian 2 U]
    [(Z.subgroupOf U).Normal]
    (hUH : U.conjBy g⁻¹ ≤ H)
    (hnH : H ≤ normalizer (U : Set G))
    (hn : U ≤ normalizer (U.conjBy g : Set G))
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (U ⧸ Z.subgroupOf U)))
    (hρ : Compatible H U Z hnH ρ)
    (hproper : Source.DH U (U.conjBy g) (Z.conjBy g) < U)
    (ht : let _ : IsElementaryAbelian 2 (U.conjBy g) := IsElementaryAbelian.map _
      ∀ u : U, binaryLinear (conjugationAction U (U.conjBy g) hn u) ∈
        LinearEquiv.transvections (ZMod 2) (Additive (U.conjBy g))) :
    ∃ a ∈ Source.starImage H (U.conjBy g⁻¹),
      a ≠ 1 ∧ fixedCodim ρ (zpowers a) = 1 := by
  let _ : IsElementaryAbelian 2 (U.conjBy g) := IsElementaryAbelian.map _
  obtain ⟨u, hu, v, hv, hcomm⟩ :
      ∃ u ∈ U, ∃ v ∈ U.conjBy g, ⁅u, v⁆ ∉ Z.conjBy g := by
    by_contra! hc
    exact hproper.not_ge (le_commutatorPreimage le_rfl (commutator_le.mpr hc))
  let b : H := ⟨g⁻¹ * u * g, hUH ⟨u, hu, by simp⟩⟩
  let a := QuotientGroup.mk' (pCore 2 H) b
  let e : U.conjBy g ≃* U := ((MulAut.conj g).subgroupMap U).symm
  let q := QuotientGroup.mk' (Z.subgroupOf U)
  let m : U.conjBy g →* (U ⧸ Z.subgroupOf U) := q.comp e.toMonoidHom
  let f : Additive (U.conjBy g) →ₗ[ZMod 2] Additive (U ⧸ Z.subgroupOf U) :=
    { m.toAdditive with map_smul' := ZMod.map_smul m.toAdditive }
  have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp e.surjective
  let t := binaryLinear (conjugationAction U (U.conjBy g) hn ⟨u, hu⟩)
  have he (x : Additive (U.conjBy g)) : f (t x) = ρ a (f x) := by
    change Additive.ofMul (q (e (conjugationAction U (U.conjBy g) hn ⟨u, hu⟩ x.toMul))) =
      ρ a (Additive.ofMul (q (e x.toMul)))
    rw [hρ b (e x.toMul)]
    congr 2
    apply Subtype.ext
    change g⁻¹ * (u * (x.toMul : G) * u⁻¹) * g =
      (g⁻¹ * u * g) * (g⁻¹ * (x.toMul : G) * g) * (g⁻¹ * u * g)⁻¹
    group
  let x : Additive (U.conjBy g) := Additive.ofMul ⟨v, hv⟩
  have hmoves : ρ a (f x) ≠ f x := by
    intro hh
    rw [← he] at hh
    have hh' : q (e (conjugationAction U (U.conjBy g) hn ⟨u, hu⟩ ⟨v, hv⟩)) =
        q (e ⟨v, hv⟩) := hh
    have hz := QuotientGroup.eq_iff_div_mem.mp hh'
    have hz' := mem_map_of_mem (MulAut.conj g).toMonoidHom hz
    apply hcomm
    change g * ((g⁻¹ * (u * v * u⁻¹) * g) / (g⁻¹ * v * g)) * g⁻¹ ∈ Z.conjBy g at hz'
    convert hz' using 1
    change u * v * u⁻¹ * v⁻¹ =
      g * ((g⁻¹ * (u * v * u⁻¹) * g) / (g⁻¹ * v * g)) * g⁻¹
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    group
  have ha : a ≠ 1 := by
    intro hh
    exact hmoves (by rw [hh, map_one]; rfl)
  have hle := quotient_fixedCodim_le ρ a t f hf he (ht ⟨u, hu⟩)
  have hpos : fixedCodim ρ (zpowers a) ≠ 0 := by
    rw [fixedCodim_zpowers_eq_displacement_rank]
    intro hz
    have hz' := Submodule.finrank_eq_zero.mp hz
    have hx : ((ρ a - LinearMap.id : Module.End (ZMod 2)
        (Additive (U ⧸ Z.subgroupOf U))) (f x)) ∈ LinearMap.range (ρ a - LinearMap.id) :=
      LinearMap.mem_range_self _ _
    rw [hz'] at hx
    exact hmoves (sub_eq_zero.mp hx)
  refine ⟨a, ⟨b, ?_, rfl⟩, ha, by omega⟩
  exact ⟨u, hu, by simp [b]⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.CriticalReciprocity

end
