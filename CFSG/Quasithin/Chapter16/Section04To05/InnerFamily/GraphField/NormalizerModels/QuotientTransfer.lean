module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.ModelData
public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.ResidualFixer

/-!
# Faithful transport of the quaternion placement calculation

The relative quotient H/K, where H = N_G(L) and K = C_G(L), embeds
faithfully in Aut(PSL₃(4)) through a perfect central covering of L. This
map carries the actual image of L onto the inner automorphisms and sends
an involution outside KL to an outer involution of order two.

Consequently the intrinsic quaternion-centralizer containment transports
to precisely `QuaternionPlacement L`, retaining the original quotient
and marked actor. The automorphism-group containment is an explicit input
here; this transfer does not supply the missing model calculation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
the first paragraph of printed p.1192 in the proof of 16.4.9(2).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.Intersections.GraphField.NormalizerModels
open Matrix.PSL3Four
variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)
variable (c : PerfectCentralCovering.Cover L PSL) (hk : c.toMonoidHom.ker = center L)

/-- The faithful quotient action on the specified projective model. -/
noncomputable def quotientModelAction : actionQuotient L →* MulAut PSL :=
  (c.autMap hk).comp ((QuotientGroup.kerLift L.normalizerMonoidHom).comp
    (QuotientGroup.quotientMulEquivOfEq L.normalizerMonoidHom_ker.symm).toMonoidHom)

omit [Finite G] in
theorem quotientModelAction_injective : Function.Injective (quotientModelAction L c hk) :=
  (c.autMap_injective hk).comp ((QuotientGroup.kerLift_injective L.normalizerMonoidHom).comp
    (QuotientGroup.quotientMulEquivOfEq L.normalizerMonoidHom_ker.symm).injective)

omit [Finite G] in
theorem quotientModelAction_mk (n : normalizer (L : Set G)) :
    quotientModelAction L c hk (actionProjection L n) =
      c.autMap hk (L.normalizerMonoidHom n) := rfl

omit [Finite G] in
theorem quotientModelAction_inner (x : L) :
    quotientModelAction L c hk (actionProjection L ⟨x, L.le_normalizer x.property⟩) =
      MulAut.conj (c.toMonoidHom x) := by
  rw [quotientModelAction_mk]
  ext y
  obtain ⟨d, rfl⟩ := c.surjective y
  rw [c.autMap_apply]
  change c.toMonoidHom (x * d * x⁻¹) =
    c.toMonoidHom x * c.toMonoidHom d * (c.toMonoidHom x)⁻¹
  rw [map_mul, map_mul, map_inv]

omit [Finite G] in
/-- The image of L is exactly the inner automorphisms, through the original covering map. -/
theorem innerImage_map_quotientModelAction :
    (innerImage L).map (quotientModelAction L c hk) =
      (MulAut.conj : PSL →* MulAut PSL).range := by
  ext a
  constructor
  · rintro ⟨q, ⟨n, hn, rfl⟩, rfl⟩
    refine ⟨c.toMonoidHom ⟨n, hn⟩, ?_⟩
    exact (quotientModelAction_inner L c hk ⟨n, hn⟩).symm
  · rintro ⟨x, rfl⟩
    obtain ⟨d, rfl⟩ := c.surjective x
    exact ⟨actionProjection L ⟨d, L.le_normalizer d.property⟩,
      ⟨⟨d, L.le_normalizer d.property⟩, d.property, rfl⟩,
      quotientModelAction_inner L c hk d⟩

omit [Finite G] in
/-- Being outside C_G(L)L is retained by the faithful projective action. -/
theorem quotientModelAction_outer (s : normalizer (L : Set G))
    (hout : (s : G) ∉ centralizer (L : Set G) ⊔ L) :
    quotientModelAction L c hk (actionProjection L s) ∉
      (MulAut.conj : PSL →* MulAut PSL).range := by
  rintro ⟨x, hx⟩
  obtain ⟨d, rfl⟩ := c.surjective x
  let dN : normalizer (L : Set G) := ⟨d, L.le_normalizer d.property⟩
  have he : actionProjection L s = actionProjection L dN := by
    apply quotientModelAction_injective L c hk
    exact hx.symm.trans (quotientModelAction_inner L c hk d).symm
  have hker : s * dN⁻¹ ∈ (centralizer (L : Set G)).subgroupOf (normalizer (L : Set G)) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change actionProjection L (s * dN⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  have hm := (centralizer (L : Set G) ⊔ L).mul_mem
    (mem_sup_left (show (s : G) * (d : G)⁻¹ ∈ centralizer (L : Set G) from hker))
    (mem_sup_right d.property)
  exact hout (by simpa only [inv_mul_cancel_right] using hm)

omit [Finite G] in
/-- An outer involution remains an involution in the faithful model action. -/
theorem quotientModelAction_order (s : normalizer (L : Set G))
    (hs : orderOf (s : G) = 2) (hout : (s : G) ∉ centralizer (L : Set G) ⊔ L) :
    orderOf (quotientModelAction L c hk (actionProjection L s)) = 2 := by
  apply orderOf_eq_prime
  · rw [← map_pow, ← map_pow,
      show s ^ 2 = 1 from Subtype.ext (hs ▸ pow_orderOf_eq_one (s : G)), map_one, map_one]
  · intro he
    apply quotientModelAction_outer L c hk s hout
    rw [he]
    exact (MulAut.conj : PSL →* MulAut PSL).range.one_mem

omit [Finite G] in
include c hk in
/-- Transport the actual automorphism-group quaternion calculation to H/K.
Relative normality and both the inner subgroup and marked involution are preserved. -/
theorem quaternionPlacement_of_model
    (hmodel : ∀ a : MulAut PSL, orderOf a = 2 →
      a ∉ (MulAut.conj : PSL →* MulAut PSL).range →
      ∀ P : Subgroup (MulAut PSL), Nonempty (P ≃* QuaternionGroup 2) →
        P ≤ centralizer ({a} : Set (MulAut PSL)) →
        P ≤ (MulAut.conj : PSL →* MulAut PSL).range ⊔ zpowers a) :
    QuaternionPlacement L := by
  intro s hs hout P hP hcentral
  let f := quotientModelAction L c hk
  have hf := quotientModelAction_injective L c hk
  have hi : Nonempty (P.map f ≃* QuaternionGroup 2) := by
    obtain ⟨e⟩ := hP
    exact ⟨(P.equivMapOfInjective f hf).symm.trans e⟩
  have hc : P.map f ≤ centralizer ({f (actionProjection L s)} : Set (MulAut PSL)) := by
    rintro a ⟨x, hx, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp (hcentral hx))
  have hb := hmodel (f (actionProjection L s)) (quotientModelAction_order L c hk s hs hout)
    (quotientModelAction_outer L c hk s hout) (P.map f) hi hc
  apply (map_le_map_iff_of_injective hf).mp
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, innerImage_map_quotientModelAction]
  exact hb

end CFSG.Quasithin.Chapter16.Intersections.GraphField.NormalizerModels
