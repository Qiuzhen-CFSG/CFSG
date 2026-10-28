module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.SourceMarker.Definitions
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.OriginalComparison

/-!
# Orbit generation by the identical temporary Thompson actor

The original product G_E = I M_E and the section-kernel Frattini correction
give V_E = ⟨V^I₀⟩. First projection is equivariant under the actual centralizer.
The checked original/temporary action-image comparison replaces each I₀ action
by an action from the identical q(J(C_H(E))). Thus its orbit of the literal
marker spans the first summand, without identifying the groups themselves.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 15.3.67, printed pp.1153–1154 (PDF pp.1170–1171).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceMarker
open Replacement Replacement.Transvections BestReduction.FullCoreTransfer BestReduction.SourceAssembly
open Representation.NormalElementaryQuotient OriginalComparison
universe u
variable {G L : Type u} [Group G] [Finite G] [Group L]
  {Y T V M E Pc : Subgroup G} [IsMulCommutative V]
  (o : Geometry.OriginalData Y T V M E Pc)
  (hNM : normalizer (V : Set G) ≤ M)
  (hprod : (lineNormalizer E : Set G) = (lineI E : Set G) * (lineM M E : Set G))
local notation "H" => temporaryLineNormalizer T V E
local notation "U" => Replacement.Transvections.localSpan T V E

include o hNM hprod in
/-- Original I₀ generates the full original conjugate span of V. -/
theorem span_eq_originalActor_span : lineV V E = conjugateSpanBy V (lineI0 T V E) := by
  have hr : (lineNormalizer E : Set G) = (lineM M E : Set G) * (lineI E : Set G) := by
    simpa only [mul_inv_rev, inv_coe_set] using congrArg Inv.inv hprod
  have hp := Descent.original_product M T V E o.line_le o.sylow o.sylow_image hNM hr
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro _ ⟨g,hg,v,hv,rfl⟩
    have hgi : g⁻¹ ∈ (lineM M E : Set G) * (lineI0 T V E : Set G) := by
      rw [← hp]
      exact (lineNormalizer E).inv_mem hg
    obtain ⟨m,hm,i,hi,hmi⟩ := hgi
    have he : g = i⁻¹ * m⁻¹ := by
      simpa only [mul_inv_rev, inv_inv] using (congrArg Inv.inv hmi).symm
    have hv' : m⁻¹ * v * m ∈ V := by
      simpa only [inv_inv, SetLike.mem_coe] using (o.action.normalizes (M.inv_mem hm.1) v).mp hv
    have hmemb : i⁻¹ * (m⁻¹ * v * m) * (i⁻¹)⁻¹ ∈ conjugateSpanBy V (lineI0 T V E) :=
      subset_closure ⟨i⁻¹,(lineI0 T V E).inv_mem hi,_,hv',rfl⟩
    rw [he]
    convert hmemb using 1
    simp only [SetLike.mem_coe]
    group
  · apply (closure_le _).mpr
    rintro _ ⟨i,hi,v,hv,rfl⟩
    exact subset_closure ⟨i,lineI_le_lineNormalizer E hi.1,v,hv,rfl⟩

variable (f : temporaryLineNormalizer T V E →* L) (hf : Function.Surjective f)
  (hker : f.ker = centralizer
    (Replacement.Transvections.localSpan T V E : Set (temporaryLineNormalizer T V E)))
local notation "P" => o.pairedSection f hf hker
local notation "σ" => o.pairedRepresentation f hf hker
local notation "q" => QuotientGroup.mk' (localCore T V E)
local notation "I" => thompsonImage T V E

include hNM hprod in
/-- The orbit of V# under the same q(J(C_H(E))) spans the entire first summand. -/
theorem projected_orbit_span : let := o.module_normal
    let := o.module_elementary
    Submodule.span (ZMod 2)
      {w | ∃ (g : I) (v : _), v ∈ projected o f hf hker ∧ σ g v = w} = ⊤ := by
  let := o.module_normal
  let := o.module_elementary
  dsimp only
  let F := (LinearMap.fst (ZMod 2) _ _).comp (P).projection
  let K := Submodule.span (ZMod 2)
    {w | ∃ (g : I) (v : _), v ∈ projected o f hf hker ∧ σ g v = w}
  let B₀ : Subgroup U := (K.comap F).toAddSubgroup.toSubgroup'
  let e : U →* G := (H).subtype.comp (U).subtype
  let B : Subgroup G := B₀.map e
  let s := (σ).asGroupHom.comp q
  have hs : (Descent.sectionKernel V E).subgroupOf H ⊓ localCentralizer T V E ≤ s.ker := by
    intro x hx
    have hx' : (⟨x, hx.2⟩ : localCentralizer T V E) ∈
        ((σ).comp ((q).comp (localCentralizer T V E).subtype)).ker :=
      (o.pairedRepresentation_centralizer_ker f hf hker).symm ▸ hx.1
    exact Units.ext hx'
  have heq := original_image_eq o s hs
  have hUB : lineV V E ≤ B := by
    rw [span_eq_originalActor_span o hNM hprod]
    apply (closure_le _).mpr
    rintro _ ⟨i,hi,v,hv,rfl⟩
    let iH : H := ⟨i, (lineI0_le_temporaryCentralizer T V E hi).1⟩
    let vU : Additive U := Additive.ofMul
      ⟨⟨v, o.span_le_temporary (le_conjugateSpanBy V _ hv)⟩,le_conjugateSpanBy V _ hv⟩
    let w := representation U f hf hker (f iH) vU
    have hiC : iH ∈ localCentralizer T V E := originalActor_le_centralizer hi
    have him : s iH ∈ (elementaryAbelianMaxJ (localCentralizer T V E)).map s := by
      rw [heq]
      exact mem_map_of_mem s hi
    obtain ⟨j,hj,hji⟩ := him
    have hji' : σ (q j) = σ (q iH) := congrArg Units.val hji
    have hw : F w ∈ K := by
      change ((P).projection (representation U f hf hker (f iH) vU)).1 ∈ K
      rw [(P).equivariant iH hiC]
      apply Submodule.subset_span
      refine ⟨⟨q j,mem_map_of_mem q hj⟩,F vU,?_,?_⟩
      · exact Submodule.mem_map.mpr ⟨vU,hv,rfl⟩
      · exact LinearMap.congr_fun hji' _
    refine mem_map.mpr ⟨w.toMul,hw,?_⟩
    change ((w.toMul : H) : G) = i * v * i⁻¹
    rw [representation_apply]
    rfl
  have hFK (u : Additive U) : F u ∈ K := by
    obtain ⟨w,hw,he⟩ := hUB u.toMul.property
    have hwu : w = u.toMul := by
      apply Subtype.ext
      apply Subtype.ext
      exact he
    subst w
    exact hw
  apply top_unique
  intro w _
  obtain ⟨v,hv⟩ := (P).surjective (w,0)
  have hh := hFK v
  change ((P).projection v).1 ∈ K at hh
  rwa [hv] at hh

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceMarker
