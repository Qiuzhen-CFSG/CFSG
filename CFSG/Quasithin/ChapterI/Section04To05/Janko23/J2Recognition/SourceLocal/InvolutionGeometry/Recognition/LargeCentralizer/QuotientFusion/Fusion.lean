module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.QuotientFusion.Images

/-!
# Fusion and the marked centralizer in C_G(t)/⟨t⟩

A quotient conjugation lifts to an ambient conjugation with two possible
values, differing by t. Both lifts lie in EU. Ambient involution fusion
forces the conjugate of an element of E# back into E; injectivity on E
then removes the ambiguity for the distinguished element z.

Consequently the E-image is closed under involution fusion in the Sylow
image, and the full quotient centralizer of z* is precisely (EU)*.

Source: Aschbacher, *Sporadic Groups* (1994), 47.1(1), printed p.260.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer
variable {G : Type*} [Group G] [Finite G] {D : Seed G} {t : G}
namespace LocalFrame
variable (F : LocalFrame D t)

theorem quotient_conjugate_mem_E (L : LocalCensus D) (ht : orderOf t = 2)
    {e a : involutionCentralizer t} (he : (e : G) ∈ F.E) (hne : e ≠ 1)
    (ha : (a : G) ∈ F.E ⊔ F.U)
    (hconj : IsConj (quotientMap t e) (quotientMap t a)) :
    quotientMap t a ∈ quotientImage F.E := by
  let : IsElementaryAbelian 2 (F.E ⊔ F.U : Subgroup G) := F.elementary
  obtain ⟨gq, hgq⟩ := isConj_iff.mp hconj
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (quotientKernel t) gq
  have hq : quotientMap t (g * e * g⁻¹) = quotientMap t a := by
    simpa only [quotientMap, map_mul, map_inv] using hgq
  have hb : ((g * e * g⁻¹ : involutionCentralizer t) : G) ∈ F.E ⊔ F.U := by
    rcases (quotient_eq_iff ht _ _).mp hq with h | h
    · simpa only [h] using ha
    · rw [h]
      exact mul_mem ha (mem_sup_right F.t_mem)
  have heo : orderOf (e : G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (A := F.E ⊔ F.U) _ (mem_sup_left he))
    (fun h => hne (Subtype.ext h))
  have hec : IsConj D.z (e : G) := (F.involution_fusion L (mem_sup_left he) heo).mpr he
  have he_b : IsConj (e : G) ((g : G) * e * (g : G)⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  have hbo : orderOf ((g : G) * e * (g : G)⁻¹) = 2 :=
    ((MulAut.conj (g : G)).orderOf_eq e).trans heo
  have hbE := (F.involution_fusion L hb hbo).mp (hec.trans he_b)
  exact mem_map.mpr ⟨g * e * g⁻¹, hbE, hq⟩

theorem quotient_fusion_closed (L : LocalCensus D) (ht : orderOf t = 2)
    (x y : F.quotientSylow) (hx : orderOf x = 2)
    (hconj : IsConj (x : CentralQuotient t) (y : CentralQuotient t)) :
    x ∈ F.quotientClosed ↔ y ∈ F.quotientClosed := by
  have hxne : (x : CentralQuotient t) ≠ 1 := by
    intro h
    exact (orderOf_eq_prime_iff.mp hx).2 (Subtype.ext h)
  have hyne : (y : CentralQuotient t) ≠ 1 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    intro h
    apply hxne
    have hh : (MulAut.conj g) (x : CentralQuotient t) = (MulAut.conj g) 1 := by
      simpa only [MulAut.conj_apply, map_one] using hg.trans h
    exact (MulAut.conj g).injective hh
  have step (a b : F.quotientSylow) (hne : (a : CentralQuotient t) ≠ 1)
      (hc : IsConj (a : CentralQuotient t) (b : CentralQuotient t))
      (ha : a ∈ F.quotientClosed) : b ∈ F.quotientClosed := by
    obtain ⟨e, he, heq⟩ := mem_map.mp ha
    have hbs : (b : CentralQuotient t) ∈ quotientImage (F.E ⊔ F.U) := by
      rw [← F.quotientSylow_eq]
      exact b.property
    obtain ⟨v, hv, hvq⟩ := mem_map.mp hbs
    have hene : e ≠ 1 := by
      intro h
      exact hne (heq.symm.trans (h ▸ (quotientMap t).map_one))
    change (b : CentralQuotient t) ∈ quotientImage F.E
    rw [← hvq]
    exact F.quotient_conjugate_mem_E L ht he hene hv (heq ▸ hvq ▸ hc)
  exact ⟨step x y hxne hconj, step y x hyne hconj.symm⟩

def quotientTransfer (L : LocalCensus D) (ht : orderOf t = 2) : TransferData t where
  S := F.quotientSylow
  elementary := F.quotientSylow_elementary
  E := F.quotientClosed
  index := F.quotientClosed_index ht
  closed := F.quotient_fusion_closed L ht

def quotientSourceLift : involutionCentralizer t :=
  ⟨D.z, F.join_le_centralizer (mem_sup_left F.z_mem)⟩

def quotientSource : CentralQuotient t := quotientMap t F.quotientSourceLift

theorem quotientSource_mem : F.quotientSource ∈ quotientImage F.E :=
  mem_map.mpr ⟨F.quotientSourceLift, F.z_mem, rfl⟩

theorem quotientSource_ne_one (ht : orderOf t = 2) : F.quotientSource ≠ 1 := by
  intro h
  have hh : quotientMap t F.quotientSourceLift = quotientMap t 1 := by
    simpa only [quotientSource, map_one] using h
  have he := F.quotient_E_injective ht F.z_mem F.E.one_mem hh
  exact (orderOf_eq_prime_iff.mp D.localType.involution).2 (congrArg Subtype.val he)

theorem quotientSource_order (ht : orderOf t = 2) : orderOf F.quotientSource = 2 := by
  apply orderOf_eq_prime _ (F.quotientSource_ne_one ht)
  change quotientMap t F.quotientSourceLift ^ 2 = 1
  rw [← map_pow]
  have h : F.quotientSourceLift ^ 2 = 1 :=
    Subtype.ext (orderOf_eq_prime_iff.mp D.localType.involution).1
  rw [h, map_one]

theorem quotientSource_centralizer (L : LocalCensus D) (ht : orderOf t = 2) :
    centralizer ({F.quotientSource} : Set (CentralQuotient t)) =
      (F.quotientSylow : Subgroup (CentralQuotient t)) := by
  let : IsElementaryAbelian 2 (F.E ⊔ F.U : Subgroup G) := F.elementary
  apply le_antisymm
  · intro gq hgq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (quotientKernel t) gq
    have hc : quotientMap t g * F.quotientSource = F.quotientSource * quotientMap t g :=
      mem_centralizer_singleton_iff.mp hgq
    have hq : quotientMap t (g * F.quotientSourceLift * g⁻¹) =
        quotientMap t F.quotientSourceLift := by
      change quotientMap t (g * F.quotientSourceLift * g⁻¹) = F.quotientSource
      rw [map_mul, map_mul, map_inv]
      change quotientMap t g * F.quotientSource * (quotientMap t g)⁻¹ = F.quotientSource
      rw [hc, mul_inv_cancel_right]
    have hb : ((g * F.quotientSourceLift * g⁻¹ : involutionCentralizer t) : G) ∈ F.E ⊔ F.U := by
      rcases (quotient_eq_iff ht _ _).mp hq with h | h
      · rw [h]
        exact mem_sup_left F.z_mem
      · rw [h]
        exact mul_mem (mem_sup_left F.z_mem) (mem_sup_right F.t_mem)
    have hbo : orderOf ((g : G) * D.z * (g : G)⁻¹) = 2 :=
      ((MulAut.conj (g : G)).orderOf_eq D.z).trans D.localType.involution
    have hbE := (F.involution_fusion L hb hbo).mp (isConj_iff.mpr ⟨(g : G), rfl⟩)
    have he := F.quotient_E_injective ht hbE F.z_mem hq
    have hgz : (g : G) ∈ involutionCentralizer D.z := by
      apply mem_centralizer_singleton_iff.mpr
      have hh := congrArg (fun x : involutionCentralizer t => (x : G) * (g : G)) he
      simpa only [coe_mul, coe_inv, quotientSourceLift, mul_assoc, inv_mul_cancel, mul_one] using hh
    have hgA : (g : G) ∈ F.E ⊔ F.U := F.double_centralizer ▸ ⟨g.property, hgz⟩
    rw [F.quotientSylow_eq]
    exact mem_map.mpr ⟨g, hgA, rfl⟩
  · intro g hg
    let : IsElementaryAbelian 2 F.quotientSylow := F.quotientSylow_elementary
    have hz : F.quotientSource ∈ (F.quotientSylow : Subgroup (CentralQuotient t)) :=
      F.quotient_E_le F.quotientSource_mem
    exact mem_centralizer_singleton_iff.mpr
      (setLike_mul_comm hg hz)
end LocalFrame
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer
