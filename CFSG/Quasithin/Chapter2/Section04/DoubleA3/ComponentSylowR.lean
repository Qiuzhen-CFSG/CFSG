module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentActionSource
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.PairFrattini
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
/-!
# Intrinsic component Sylows in the original Thompson subgroup

The second centralizer's Sylow is R⟨x⟩ with R of index two. If an element
of a normal component lies outside R, it induces the same conjugate on the
second cubic four-group as x. Normality puts their commutator in the component;
the source commutator is its fixed involution line. That involution also
centralizes the component, contradicting its trivial center.

Source: Aschbacher–Smith, the inspection before 2.4.32, printed p.547.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.DoubleA3
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}

private theorem commutator_inner_conjugate_le
    {H : Type*} [Group H] (K A : Subgroup H) [K.Normal]
    (ha : IsMulCommutative A) (y : H) (hy : y ∈ K) :
    ⁅A,A.map (MulAut.conj y).toMonoidHom⁆ ≤ K := by
  let q := QuotientGroup.mk' K
  have he : q.comp (MulAut.conj y).toMonoidHom = q := by
    ext a
    have hyq : q y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
    change q (y*a*y⁻¹) = q a
    simp only [map_mul,map_inv,hyq,one_mul,mul_one,inv_one]
  have hc : ⁅A.map q,A.map q⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    rintro a ⟨a,haA,rfl⟩ b ⟨b,hbA,rfl⟩
    let := ha
    exact congrArg q (show b*a=a*b from (le_centralizer A haA) b hbA)
  have hh : (⁅A,A.map (MulAut.conj y).toMonoidHom⁆).map q = ⊥ := by
    rw [map_commutator,map_map,he,hc]
  simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hh

/-- The actual Sylow intersection of a centerless normal component lies in R. -/
theorem SourceCentralizerGeometry.component_sylow_le_sourceR
    (g : SourceCentralizerGeometry c)
    (K : Subgroup (involutionCentralizer g.z₂)) [K.Normal]
    (hzK : center K = ⊥) :
    K.map (involutionCentralizer g.z₂).subtype ⊓
      (g.P₂ : Subgroup (involutionCentralizer g.z₂)).map (involutionCentralizer g.z₂).subtype ≤ sourceR d := by
  let H := involutionCentralizer g.z₂
  let P := (g.P₂ : Subgroup H).map H.subtype
  let A := c.U₂.subgroupOf H
  have hAH : c.U₂ ≤ H := by
    let : IsElementaryAbelian 2 c.U₂ := c.second.elementary
    intro a ha
    exact mem_centralizer_singleton_iff.mpr ((le_centralizer c.U₂ g.second_mem) a ha)
  have hmapA : A.map H.subtype = c.U₂ := map_subgroupOf_eq_of_le hAH
  have hAN : sourceR d ≤ normalizer (c.U₂ : Set G) := by
    intro r hr
    exact (normalizer_le_normalizer_characteristic_image c.L (blockU c.L))
      (c.second.normalizes (by change r ∈ ChapterB.baumann _; rw [c.baumann]; exact hr))
  have hxP : c.x ∈ P := by
    change c.x ∈ (g.P₂ : Subgroup H).map H.subtype
    rw [g.second_span]
    exact mem_sup_right (mem_zpowers c.x)
  have hxR : c.x ∉ sourceR d := by
    intro hx
    have hn := hAN hx
    have he : c.V₂ = c.U₂ := mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (c.U₂ : Set G)).inv_mem hn)
    apply RankOne.second_noncommuting c.orbit
    change c.V₂ ≤ centralizer (c.U₂ : Set G)
    rw [he]
    let : IsElementaryAbelian 2 c.U₂ := c.second.elementary
    exact le_centralizer c.U₂
  intro y hy
  by_contra hyR
  obtain ⟨yk,hyK,heyk⟩ := hy.1
  have hyP : y ∈ P := hy.2
  have hr : y*c.x⁻¹ ∈ sourceR d := by
    have hi : ((sourceR d).subgroupOf P).index = 2 := g.second_index
    have hh := (Subgroup.mul_mem_iff_of_index_two hi
      (a := (⟨y,hyP⟩ : P)) (b := (⟨c.x⁻¹,P.inv_mem hxP⟩ : P)))
    apply hh.mpr
    change y ∈ sourceR d ↔ c.x⁻¹ ∈ sourceR d
    simp only [hyR,(sourceR d).inv_mem_iff,hxR]
  have hm : c.U₂.map (MulAut.conj y⁻¹).toMonoidHom = c.V₂ := by
    have he : (MulAut.conj y⁻¹).toMonoidHom =
        (MulAut.conj c.x⁻¹).toMonoidHom.comp
          (MulAut.conj (y*c.x⁻¹)⁻¹).toMonoidHom := by
      ext u
      simp only [MonoidHom.comp_apply,MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,MulAut.conj_apply]
      group
    have hh := mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (c.U₂ : Set G)).inv_mem (hAN hr))
    change c.U₂.map (MulAut.conj (y*c.x⁻¹)⁻¹).toMonoidHom = c.U₂ at hh
    rw [he,←map_map,hh]
  let yH : H := yk
  have hyHG : (yH:G) = y := heyk
  let : IsElementaryAbelian 2 c.U₂ := c.second.elementary
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hAH
  have hc := commutator_inner_conjugate_le K A inferInstance yH⁻¹ (K.inv_mem hyK)
  have hcG : ⁅c.U₂,c.V₂⁆ ≤ K.map H.subtype := by
    have hh := map_mono (f := H.subtype) hc
    rw [map_commutator] at hh
    have hhmap : (A.map (MulAut.conj yH⁻¹).toMonoidHom).map H.subtype = c.V₂ := by
      calc
        _ = (A.map H.subtype).map (MulAut.conj y⁻¹).toMonoidHom := by
          rw [map_map,map_map]
          congr 1
          ext a
          simp only [MonoidHom.comp_apply,MulEquiv.toMonoidHom_eq_coe,
            MonoidHom.coe_coe,map_inv]
          change ((yH:H):G)⁻¹*(a:G)*((yH:H):G) = y⁻¹*(a:G)*y
          rw [hyHG]
        _ = c.V₂ := by rw [hmapA,hm]
    rw [hhmap,hmapA] at hh
    exact hh
  have hzKmem : g.z₂ ∈ K.map H.subtype := hcG (by
    rw [c.second_commutator]
    exact ⟨g.second_mem,g.second_fixed⟩)
  obtain ⟨z,hz,hez⟩ := hzKmem
  have hzc : (⟨z,hz⟩ : K) ∈ center K := by
    rw [mem_center_iff]
    intro k
    apply Subtype.ext
    apply Subtype.ext
    change (k:G)*(z:G) = (z:G)*(k:G)
    have hez' : (z:G) = g.z₂ := hez
    rw [hez']
    exact mem_centralizer_singleton_iff.mp (k:H).property
  have hzone : (⟨z,hz⟩ : K) = 1 := by simpa only [hzK,mem_bot] using hzc
  have hzG : g.z₂ = 1 := hez.symm.trans (congrArg (fun t : K => ((t:H):G)) hzone)
  have ho := g.order_second
  rw [hzG,orderOf_one] at ho
  omega
end CFSG.Quasithin.Chapter2.DoubleA3
