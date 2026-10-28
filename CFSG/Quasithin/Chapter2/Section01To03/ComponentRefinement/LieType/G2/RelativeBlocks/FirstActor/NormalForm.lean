module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
The standard-plane reduction adapts the coordinate argument in
Theory/AtlasPort/LinearGroups/G2/EvenLocal/NormalizerCover/OctonionHexagon/
CosetIdentification/Stabilizer.lean, based on Atlas/LinearGroups/G2/Parabolic.lean,
revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917;
see LICENSES/ATLAS-CITATION.cff.
Changes: retain the two explicit short-root cells, separate the radical, and
prove radical normality in the full first parabolic.
-/

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.RelativeBlocks.FirstActor.SquareTests
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification.Stabilizer
public import Theory.GroupTheory.LocalNormalizerUniqueness


/-!
# The full first parabolic has the two required root cells

Its action on the standard zero-product plane reduces an element either to
the flag stabilizer (the Borel) or to F(a)S times the Borel. The six-root
chart then separates the five-root radical from its last simple-root
parameter. Normality of the local two-core moves that radical to the left,
giving the normal forms used by the four square tests.

The entire split torus is retained. Its root-character formulas also show
that it normalizes the five-root radical, so the radical is normal in the
full parabolic. The only conditional input is the permitted identification
of the short local two-core with that radical.

Source: Aschbacher–Smith 2.3.9(7), printed p.526. The standard-plane reduction
adapts the licensed ATLAS coordinate argument in the imported stabilizer
module; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

open Atlas.G2 Atlas.G2.Explicit Atlas.G2.LieParabolicSetup Atlas.SplitOctonion Subgroup
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2.RelativeBlocks.FirstActor
variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
private theorem local_normalizes_radical
    (hc : (local₁ (F := F)).pCoreIn 2 = radical₁) :
    local₁ (F := F) ≤ normalizer (radical₁ (F := F) : Set (Model F)) := by
  rw [← hc]
  exact local₁.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image local₁ (pCore 2 local₁))

omit [CharP F 2] in
theorem parabolic_normalizes_radical
    (hc : (local₁ (F := F)).pCoreIn 2 = radical₁) :
    parabolic₁ (F := F) ≤ normalizer (radical₁ (F := F) : Set (Model F)) := by
  have ht (g : Model F) (hg : g ∈ splitTorus) (r : Model F) (hr : r ∈ radical₁) :
      g * r * g⁻¹ ∈ radical₁ := by
    obtain ⟨⟨l,m⟩,rfl⟩ := hg
    obtain ⟨t,ht,rfl⟩ := hr
    exact ⟨torusUnipotentParameters l m t,
      by simp [torusUnipotentParameters,ht], (torus_unipotentProduct l m t).symm⟩
  have htor : splitTorus (K := F) ≤ normalizer (radical₁ (F := F) : Set (Model F)) := by
    intro g hg
    apply mem_normalizer_iff.mpr
    intro r
    constructor
    · exact ht g hg r
    · intro hr
      have := ht g⁻¹ (splitTorus.inv_mem hg) _ hr
      simpa [mul_assoc] using this
  change (unipotent ⊔ splitTorus) ⊔ closure {weylS} ≤ _
  exact sup_le (sup_le (unipotent_le_local₁.trans (local_normalizes_radical hc)) htor)
    (le_sup_right.trans (local_normalizes_radical hc))

omit [CharP F 2] in
private theorem borel_normalForm {g : Model F} (hg : g ∈ borel) :
    ∃ r ∈ radical₁, ∃ a : F, ∃ l m : Fˣ, g = r * smallLevi a l m := by
  obtain ⟨⟨u,t⟩,he⟩ := (borelProductEquiv (K := F)).surjective ⟨g,hg⟩
  have he' : u.val * t.val = g := congrArg Subtype.val he
  obtain ⟨v,hv⟩ := (unipotent_eq_range (K := F)).le u.property
  obtain ⟨⟨l,m⟩,hm⟩ := t.property
  refine ⟨unipotentProduct ![v 0,v 1,v 2,v 3,v 4,0],⟨_,rfl,rfl⟩,v 5,l,m,?_⟩
  rw [← he',← hv,← hm]
  simp [smallLevi, unipotentProduct,torusHom,mul_assoc]

private theorem two_cells {g : Model F} (hg : g ∈ parabolic₁) :
    g ∈ borel ∨ ∃ a : F, ∃ b ∈ borel, g = rootF a * weylS * b := by
  have hl := shortParabolic_le_lineStabilizer hg
  let x := g.val (basisVector 0)
  have hx : x ∈ standardPlane := by
    have ht := (mem_line_smul g standardLine (basisVector 0)).mpr
      (Submodule.subset_span (by simp))
    rwa [show g • standardLine = standardLine from hl] at ht
  have hn : x ≠ 0 := by
    intro h
    exact first_basis_ne_zero (g.val.injective (h.trans (g.val.map_zero).symm))
  obtain ⟨h2,h3,h4,h5,h6,h7⟩ := (mem_standardPlane_iff_coordinates x).mp hx
  by_cases h1 : x 1 = 0
  · left
    have he : x = x 0 • basisVector 0 := by
      funext i
      fin_cases i <;> simp [basisVector,h1,h2,h3,h4,h5,h6,h7]
    have h0 : x 0 ≠ 0 := by
      intro hz
      apply hn
      rw [he,hz,zero_smul]
    apply pointStabilizer_lineStabilizer_le_borel ⟨g,?_⟩ hl
    exact (mem_pointStabilizer_iff g).mpr ⟨Units.mk0 (x 0) h0,he⟩
  · right
    let k : Model F := weylS * rootF (x 0 / x 1)
    have hk : k ∈ parabolic₁ := parabolic₁.mul_mem weylS_mem_shortParabolic
      (rootF_mem_shortParabolic _)
    have he : k.val x = (-x 1) • basisVector 0 := by
      funext i
      fin_cases i <;> simp [k,weylS,weylSEquiv,weylSLinear,weylSApply,
        rootF,rootFEquiv,rootFLinear,rootFApply,basisVector,h2,h3,h4,h5,h6,h7]
      field_simp
      ring
    have hp : k*g ∈ pointStabilizer := by
      apply (mem_pointStabilizer_iff _).mpr
      exact ⟨Units.mk0 (-x 1) (neg_ne_zero.mpr h1),he⟩
    have hb : k*g ∈ borel := pointStabilizer_lineStabilizer_le_borel
      ⟨k*g,hp⟩ (shortParabolic_le_lineStabilizer (parabolic₁.mul_mem hk hg))
    refine ⟨x 0 / x 1,k*g,hb,?_⟩
    have hi : k⁻¹ = rootF (x 0 / x 1) * weylS := by
      change (weylS * rootF (x 0 / x 1))⁻¹ = _
      rw [mul_inv_rev,weylS_inverse,← rootF_neg,CharTwo.neg_eq]
    rw [← hi,inv_mul_cancel_left]

theorem parabolic_normalForm
    (hc : (local₁ (F := F)).pCoreIn 2 = radical₁)
    {g : Model F} (hg : g ∈ parabolic₁) : HasNormalForm g := by
  rcases two_cells hg with hb | ⟨a,b,hb,rfl⟩
  · exact Or.inl (borel_normalForm hb)
  · obtain ⟨r,hr,c,l,m,he⟩ := borel_normalForm hb
    right
    let k : Model F := rootF a * weylS
    have hk : k ∈ local₁ := local₁.mul_mem
      (unipotent_le_local₁ (subset_closure (by simp)))
      (mem_sup_right (subset_closure (by simp)))
    have hr' : k*r*k⁻¹ ∈ radical₁ :=
      (mem_normalizer_iff.mp (local_normalizes_radical hc hk) r).mp hr
    refine ⟨k*r*k⁻¹,hr',a,c,l,m,?_⟩
    rw [he]
    dsimp only [bigLevi,smallLevi,k]
    group

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2.RelativeBlocks.FirstActor

end
