module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.BinaryLinear
public import Theory.GroupTheory.GeneralizedFitting.ComponentMaximalIntersection
public import Theory.GroupTheory.InnerInvolutionSylowCenter

/-!
# The Borel of the original ordinary component

Minimality of the escaping overgroup makes the literal Mc ∩ I maximal
inside I. Suppose a Sylow of the selected component is normal in its
marked fixed subgroup. Its image is exactly O₂(L ∩ Mc). An inner
conjugator lies in that Sylow; faithfulness shows the local core cannot
centralize L. The component-core orbit theorem therefore puts the full
component Sylow normalizer in Mc, so the marked automorphism fixes it.
All subgroup embeddings and central two-covers are retained.

Source: Aschbacher--Smith 15.2.24, printed p.1117, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
open Section01 Section03 Candidates.ComponentStructure ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
variable {P : Sylow 2 I} {z : G}
variable (c : ComponentData (T := T) (Mc := Mc) I P z)
include d

/-- The actual intersection Mc ∩ I is maximal inside the minimal escape. -/
theorem minimal_intrinsic_intersection (hI : MinimalPlaneEscape Mc ZS I) :
    IsCoatom (Mc.comap I.subtype) := by
  apply isCoatom_iff_ge_of_le.mpr
  constructor
  · intro he
    apply hI.1.2.2
    intro x hx
    have hh : (⟨x,hx⟩ : I) ∈ Mc.comap I.subtype := he ▸ mem_top _
    exact hh
  · intro J hJ hCJ
    have hCM : (Mc.comap I.subtype).map I.subtype = Mc ⊓ I := by
      rw [map_comap_eq,range_subtype,inf_comm]
    have hle : Mc ⊓ I ≤ J.map I.subtype := hCM ▸ map_mono hCJ
    rcases d.minimal_intermediate hI hle (map_subtype_le J) with he | he
    · have hh : J = Mc.comap I.subtype := map_injective I.subtype_injective (he.trans hCM.symm)
      exact hh.le
    · exfalso
      apply hJ
      apply map_injective I.subtype_injective
      simpa only [← MonoidHom.range_eq_map,range_subtype] using he

/-- The marked action fixes the full Borel when its fixed subgroup normalizes the Sylow. -/
theorem marked_component_borel_fixed
    (hI : MinimalPlaneEscape Mc ZS I)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (hai : TwoCentralInner a)
    (Q : Sylow 2 c.component)
    (hQ : (Q : Subgroup c.component) ≤ a.fixedSubgroup)
    (hn : a.fixedSubgroup ≤ normalizer (Q : Set c.component)) :
    ∀ x ∈ normalizer (Q : Set c.component), a x = x := by
  let C := Mc.comap I.subtype
  let L := c.component
  have hD : a.fixedSubgroup.map L.subtype = L ⊓ C := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      refine ⟨y.property,?_⟩
      change (y : G) ∈ Mc
      rw [← (marked_centralizer d hI.1 hz hzne).2]
      apply mem_centralizer_singleton_iff.mpr
      have hh := ha y
      rw [(MulAut.mem_fixedSubgroup _ _).mp hy] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
    · rintro ⟨hxL,hxC⟩
      refine ⟨⟨x,hxL⟩,?_,rfl⟩
      apply (MulAut.mem_fixedSubgroup _ _).mpr
      apply Subtype.ext
      apply Subtype.ext
      rw [ha]
      have hc : (x : G) * z = z * x := mem_centralizer_singleton_iff.mp
        ((marked_centralizer d hI.1 hz hzne).2.ge hxC)
      rw [←hc,mul_inv_cancel_right]
  have hcore : (L ⊓ C).pCoreIn 2 = (Q : Subgroup L).map L.subtype := by
    rw [← hD,← map_pCoreIn_of_injective 2 _ _ L.subtype_injective]
    congr 1
    apply le_antisymm
    · have hh := pCoreIn_le_sylow a.fixedSubgroup (Q.subtype hQ)
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hQ] using hh
    · exact le_pCoreIn_of_normalizes Q.isPGroup' hQ hn
  have hnon : ¬ (L ⊓ C).pCoreIn 2 ≤ centralizer (L : Set I) := by
    intro hc
    have ht := hai.1
    obtain ⟨t,_,he⟩ := MulAut.exists_center_sylow_conjugator_of_inner_involution Q a
      (hai.2.1 ▸ pow_orderOf_eq_one a) ht
      (fun x hx => (MulAut.mem_fixedSubgroup _ _).mp (hQ hx)) c.center_two
    have hacent : MulAut.conj (t : L) = 1 := by
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      change (t : I) * (x : I) * (t : I)⁻¹ = x
      have htc := hc (hcore ▸ mem_map_of_mem L.subtype t.property) (x : I) x.property
      exact mul_inv_eq_iff_eq_mul.mpr htc.symm
    have hh : orderOf a = 1 := by rw [←he,hacent,orderOf_one]
    have ho := hai.2.1
    omega
  have hle := c.isComponent.normalizer_intersection_core_le
    (minimal_intrinsic_intersection d hI) hnon
  intro x hx
  have hxI : (x : I) ∈ normalizer ((L ⊓ C).pCoreIn 2 : Set I) := by
    rw [hcore]
    exact (Q : Subgroup L).le_normalizer_map L.subtype (mem_map_of_mem L.subtype hx)
  have hc := hle ⟨x.property,hxI⟩
  have hxD : (x : I) ∈ a.fixedSubgroup.map L.subtype := hD ▸ ⟨x.property,hc⟩
  exact (MulAut.mem_fixedSubgroup _ _).mp ((mem_map_iff_mem L.subtype_injective).mp hxD)
end CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
