module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.MSBlock
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.Movement

/-!
# Reconstructing the component core from the literal natural module

Once the component commutator core is identified with the original natural
subgroup, its elementary and central properties follow from the specified
natural action and its exact two-core kernel. Transitivity of A6 on nonzero
vectors gives the full normal-subgroup interval required by
`BlockModuleIrreducible`; its fixed subspace is zero.

The critical-distance argument supplies the core equality. This extension
performs its intrinsic pullback without replacing the original module or
assuming an abstract MS classification. Source: MS93 Sections 3 and 5,
and Aschbacher--Smith C.1.37, printed pp.141--143.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SourceData
variable {K : Type*} [Group K] [Finite K]
  {L V : Subgroup K} [L.Normal] [V.Normal] {T : Sylow 2 K}
  (d : SourceData L V T)
include d

omit [Finite K] in
/-- No element of the specified natural module is fixed by the component. -/
theorem module_inf_component_centralizer_eq_bot :
    V ⊓ centralizer (L : Set K) = ⊥ := by
  apply le_bot_iff.mp
  rintro x ⟨hx,hc⟩
  have hf : (d.eV ⟨x,hx⟩).toAdd ∈ Representation.BinaryOffender.fixedSpace
      Model.rho (alternatingGroup (Fin 6)) := by
    intro a
    obtain ⟨l,hl,he⟩ := d.image_component.ge a.property
    have hconj : MulAut.conjNormal l (⟨x,hx⟩ : V) = ⟨x,hx⟩ := by
      apply Subtype.ext
      change l*x*l⁻¹=x
      rw [hc l hl,mul_inv_cancel_right]
    have hh := d.action l ⟨x,hx⟩
    rw [hconj,he] at hh
    exact hh.symm
  rw [Model.fixedSpace_alternating_eq_bot] at hf
  have hx1 : (⟨x,hx⟩ : V) = 1 := d.eV.injective (by
    apply Multiplicative.toAdd.injective
    rw [map_one]
    exact hf)
  exact congrArg Subtype.val hx1

omit [Finite K] in
/-- Transitivity on nonzero vectors recognizes each component-invariant
subgroup of the literal natural module. -/
theorem module_invariant_dichotomy (N : Subgroup K) (hNV : N ≤ V)
    (hn : L ≤ normalizer (N : Set K)) : N = ⊥ ∨ N = V := by
  by_cases hb : N = ⊥
  · exact Or.inl hb
  right
  apply le_antisymm hNV
  obtain ⟨u,hu⟩ := ne_bot_iff_exists_ne_one.mp hb
  let uV : V := ⟨u,hNV u.property⟩
  have hu0 : (d.eV uV).toAdd ≠ 0 := by
    intro he
    apply hu
    have hh : uV = 1 := d.eV.injective (by
      apply Multiplicative.toAdd.injective
      rw [map_one]
      exact he)
    exact Subtype.ext (congrArg (fun v : V => (v:K)) hh)
  intro x hx
  by_cases hx1 : x=1
  · rw [hx1];exact one_mem N
  let xV : V := ⟨x,hx⟩
  have hx0 : (d.eV xV).toAdd ≠ 0 := by
    intro he
    apply hx1
    have hh : xV=1 := d.eV.injective (by
      apply Multiplicative.toAdd.injective
      rw [map_one]
      exact he)
    exact congrArg Subtype.val hh
  obtain ⟨a,ha⟩ := Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport.transitive_nonzero
    (d.eV uV).toAdd (d.eV xV).toAdd hu0 hx0
  obtain ⟨l,hl,he⟩ := d.image_component.ge a.property
  have hconj : MulAut.conjNormal l uV=xV := by
    apply d.eV.injective
    apply Multiplicative.toAdd.injective
    rw [d.action,he]
    exact ha
  have hh : l*(u:K)*l⁻¹=x := congrArg Subtype.val hconj
  rw [← hh]
  exact le_normalizer_iff.mp hn l hl u u.property

omit [Finite K] in
/-- Equality with the entire specified natural module reconstructs every
intrinsic core clause, including its normal-subgroup interval. -/
theorem coreReconstruction_of_core_image_eq
    (he : (blockU L).map L.subtype = V) : CoreReconstruction L := by
  have huc : blockU L ≤ centralizer (pCore 2 L : Set L) := by
    intro u hu q hq
    have hqK : (q:K) ∈ pCore 2 K := by
      apply (show (pCore 2 L).map L.subtype ≤ pCore 2 K from
        le_sSup ⟨inferInstance,pCore_isPGroup.map L.subtype⟩)
      exact mem_map_of_mem L.subtype hq
    have huV : (u:K) ∈ V := he ▸ mem_map_of_mem L.subtype hu
    rw [← d.centralizer_eq_core] at hqK
    apply L.subtype_injective
    exact (hqK u huV).symm
  have hfixed : blockU L ⊓ center L = ⊥ := by
    apply le_bot_iff.mp
    rintro u ⟨hu,hz⟩
    have huV : (u:K) ∈ V := he ▸ mem_map_of_mem L.subtype hu
    have hc : (u:K) ∈ centralizer (L : Set K) := by
      intro l hl
      exact congrArg L.subtype (mem_center_iff.mp hz ⟨l,hl⟩)
    have hu1 := (show (u:K) ∈ (⊥:Subgroup K) from
      d.module_inf_component_centralizer_eq_bot ▸ ⟨huV,hc⟩)
    exact L.subtype_injective hu1
  have hune : blockU L ≠ ⊥ := by
    intro hb
    have hvbot : V=⊥ := by rw [← he,hb,Subgroup.map_bot]
    have hv1 : d.v=1 := Subtype.ext (hvbot ▸ d.v.property)
    exact d.v_ne hv1
  refine ⟨?_,huc,?_,?_⟩
  · let := d.elementary
    let e := ((blockU L).equivMapOfInjective L.subtype L.subtype_injective).trans
      (MulEquiv.subgroupCongr he)
    exact IsElementaryAbelian.of_injective e.toMonoidHom e.injective
  · rw [hfixed]
    exact bot_lt_iff_ne_bot.mpr hune
  · intro N hn hlow hhigh
    let := hn
    have hN : N.map L.subtype ≤ V := by
      rw [← he]
      exact map_mono hhigh
    have hnorm : L ≤ normalizer (N.map L.subtype : Set K) := by
      simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,L.range_subtype] using
        N.le_normalizer_map L.subtype
    rcases d.module_invariant_dichotomy (N.map L.subtype) hN hnorm with hb|hfull
    · left
      rw [hfixed]
      exact (N.map_eq_bot_iff_of_injective L.subtype_injective).mp hb
    · right
      exact Subgroup.map_injective L.subtype_injective (hfull.trans he.symm)

end CFSG.Quasithin.ChapterC.NaturalSixControl.SourceData
