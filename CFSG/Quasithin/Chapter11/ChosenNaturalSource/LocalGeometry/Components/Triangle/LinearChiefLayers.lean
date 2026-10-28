module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.LinearSourceFrame
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.LinearMarkedSylow
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure.RecognitionApplications
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.RecognizedModels

/-!
# Natural and dual layers for the original centralizer span

In the branch [O₂(L_X₁),L_X₁]=1, the original extraspecial cubic action makes
U escape O₂(LT). The proved point-normalizer equality identifies this U with
the closure in G.2.5. Apply the marked frame construction and the genuine
G.2.5 structure and recognition theorems: [V,U]=V₁, J=LU lies in LT, and its two-core has
the series V≤S₂≤S₃≤O₂(J), S₂/V is central, and the two upper factors have
actual homogeneous dual and natural coordinates. The same original star map
identifies the kernel on U with U intersect O₂(J).

The natural and dual models retain the exact original L/O₂(L) marking and
literal quotient projections. They may have zero multiplicity. These are
ambient layer models, not recognition of the selected KX-chief section or
selection of its projective adjoint extension. That comparison, the
centralizer exclusions, common-normal existence and both triangle
orientations remain required for the source theorem.

The private point-radical and kernel transports adapt the already proved
calculations in Closure/Linear/Generation/Layers/UpperPreparation and
Closure/Linear/Block/Special/Order. Their later closure consumers import this
local-geometry boundary, so importing those modules here would form a cycle.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed pp.763--764, using G.2.5, printed pp.335--336.
-/

open Subgroup Theory.GroupTheory Representation Matrix
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

open ChapterG.Section02.LinearThree

private theorem source_point_radical {B : ChapterG.Section02.Setup G}
    {F : Type*} [Field F] [Finite F] {n : ℕ} {g h : G}
    (d : Hypothesis B F n g h) (hUT : B.U ≤ B.T)
    (hf : (frattini B.U).map B.U.subtype ≤ B.V₁) :
    Recognition.Hypothesis.UpperRadicalIdentification d (d.sourceStarComparison hUT hf) := by
  let e := d.sourceStarComparison hUT hf
  have himage : (B.U.subgroupOf (I B g h)).map e.projection =
      (B.star B.U).subgroupOf (B.star B.L) := by
    ext z
    constructor
    · rintro ⟨i,hi,rfl⟩
      change (e.projection i : B.Star) ∈ B.star B.U
      rw [d.sourceStarComparison_projection_apply hUT hf]
      exact ⟨inclusion (d.I_le_LT hUT) i,hi,rfl⟩
    · intro hz
      obtain ⟨u,hu,he⟩ := hz
      let i : I B g h := ⟨u,(le_sup_left.trans le_sup_left : B.U ≤ I B g h) hu⟩
      refine ⟨i,hu,?_⟩
      rw [d.sourceStarComparison_projection_apply hUT hf]
      exact Subtype.ext he
  change (B.U.subgroupOf (I B g h)).map e.projection = _
  rw [himage]
  apply Subgroup.map_injective (f := d.model.toMonoidHom) d.model.injective
  change d.pointRadicalImage = _
  rw [d.pointRadicalImage_eq_radical hUT hf (d.star_U_le_star_L hUT hf)]
  ext z
  rw [mem_map_equiv]
  change ((∀ v ∈ d.point,z.val *ᵥ v = v) ∧ (∀ v,z.val *ᵥ v-v ∈ d.point)) ↔
    (∀ v,(d.model (d.model.symm z)).val *ᵥ v-v ∈ d.point) ∧
      (∀ v ∈ d.point,(d.model (d.model.symm z)).val *ᵥ v = v)
  rw [d.model.apply_symm_apply]
  exact and_comm


private theorem source_span_kernel {B : ChapterG.Section02.Setup G}
    {F : Type*} [Field F] [Finite F] {n : ℕ} {g h : G}
    (d : Hypothesis B F n g h) (hUT : B.U ≤ B.T)
    (hf : (frattini B.U).map B.U.subtype ≤ B.V₁) :
    (Hypothesis.UStarProjection B hUT).ker =
      (ChapterG.Section02.LinearThree.S B g h).subgroupOf B.U := by
  have hUI : B.U ≤ I B g h := le_sup_left.trans le_sup_left
  have hs := d.S_eq_star_kernel hUT hf
  ext u
  change Hypothesis.UStarProjection B hUT u = 1 ↔
    (u : G) ∈ ChapterG.Section02.LinearThree.S B g h
  rw [Subtype.ext_iff]
  change QuotientGroup.mk' (pCore 2 B.LT)
    (inclusion (hUT.trans le_sup_right) u) = 1 ↔ _
  rw [QuotientGroup.mk'_apply,QuotientGroup.eq_one_iff]
  constructor
  · intro hu
    exact hs.ge ⟨hUI u.property,mem_map_of_mem _ hu⟩
  · intro hu
    obtain ⟨v,hv,he⟩ := (hs.le hu).2
    exact (Subtype.ext he : v = inclusion (hUT.trans le_sup_right) u) ▸ hv

/-- Natural and dual coordinates on the literal layers of the original U-span.
All source inputs, including escape, are obtained from the projective quotient
in the branch where the cubic-normalizer residual centralizes its two-core. -/
theorem linear_point_original_layers
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 ≤ K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 0) ≤ centralizer (f.Vi 0 : Set G))
    (hzero : let H := localResidual L (X ⊓ Closure.coreQuotientCentralizer (f.Li 0))
      ⁅H.pCoreIn 2,H⁆ = ⊥) :
    let B := linearPointSetup D S m f
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    ∃ g h : G, ∃ d : Hypothesis B S.field.Carrier S.field.degree g h,
      ∃ hUT : B.U ≤ B.T, ∃ hf : (frattini B.U).map B.U.subtype ≤ B.V₁,
      d.model = linearPointStarModel D S m f ∧
      d.coordinates = SL3.naturalEquiv D S m ∧ d.point = f.space 0 ∧
      B.U = U ∧ ⁅V,U⁆ = f.Vi 0 ∧ I B g h = L ⊔ U ∧ L ⊔ U ≤ L ⊔ (T : Subgroup G) ∧
      ChapterG.Section02.LinearThree.S B g h = (L ⊔ U).pCoreIn 2 ∧
      V ≤ S₂ B g h ∧ S₂ B g h ≤ S₃ B g h ∧
      S₃ B g h ≤ ChapterG.Section02.LinearThree.S B g h ∧
      ⁅S₂ B g h,L ⊔ U⁆ ≤ V ∧
      L ⊔ U ≤ normalizer (S₃ B g h : Set G) ∧
      (let p := (d.starUEquiv hUT hf).toMonoidHom.comp (Hypothesis.UStarProjection B hUT)
       Function.Surjective p ∧ p.ker =
         (ChapterG.Section02.LinearThree.S B g h).subgroupOf B.U) ∧
      (letI := Recognition.Hypothesis.lower_normal d hUT hf (d.L_le_I hUT hf)
       letI := d.S₃_normal_in_S hUT hf
       ∃ r s : ℕ, Nonempty (ChiefFactors.MarkedLayers d (d.L_le_I hUT hf) r s)) := by
  intro B U
  have hUeq : B.U = U := linear_four_point_spans_eq D S m f hd hX hcard hmove
  obtain ⟨_,hUT,hf,_⟩ := linear_point_centralizer_span D S m f
  obtain ⟨_,hY⟩ := linear_cubic_displacement_of_projective D S m f hd hfix hX hK hLK hk hp hcard hmove
  have hescape := linear_four_span_escapes_of_central_cubic_core D S m f hd hX hcard hUT hY hzero
  have hUT' : B.U ≤ B.T := hUeq ▸ hUT
  have hf' : (frattini B.U).map B.U.subtype ≤ B.V₁ := by
    change (frattini B.U).map B.U.subtype ≤ f.Vi 0
    rw [hUeq]
    exact hf
  obtain ⟨g,h,d,hmodel,hcoords,hpoint⟩ := linear_point_source_frame D S m f (hUeq ▸ hescape) hUT'
  have hI : I B g h = L ⊔ U := (d.I_eq_LU hUT' hf').trans (congrArg (L ⊔ ·) hUeq)
  have hVU : ⁅V,U⁆ = f.Vi 0 := by
    change ⁅B.V,U⁆ = B.V₁
    rw [←hUeq]
    exact d.commutator_V_U_eq_point hUT' hf'
  have hh := Recognition.Hypothesis.recognized_layers_from_projective d hUT' hf'
    (d.L_le_I hUT' hf') (d.S_normalizes_U hUT' hf')
    (d.S_normalizes_marked hUT' hf' g d.g_mem) (d.S_normalizes_marked hUT' hf' h d.h_mem)
    (d.S_eq_product hUT' hf') (d.sourceStarComparison hUT' hf')
    (source_point_radical d hUT' hf')
  obtain ⟨hN,r,s,_,_,_,_,hlayers⟩ := hh
  have hseries := d.series_inclusions hUT' hf' (d.L_le_I hUT' hf')
  refine ⟨g,h,d,hUT',hf',hmodel,hcoords,hpoint,hUeq,hVU,hI,sup_le_sup_left hUT L,?_,
    hseries.1,hseries.2.1,hseries.2.2,?_,hI ▸ hN,?_,r,s,hlayers⟩
  · change (I B g h).pCoreIn 2 = _
    rw [hI]
  · rw [←hI]
    exact (d.intersection hUT' hf').2.2.2.1
  · refine ⟨(d.starUEquiv hUT' hf').surjective.comp
      (Hypothesis.UStarProjection_surjective hUT'),?_⟩
    rw [MonoidHom.ker_comp_of_injective _ _ (d.starUEquiv hUT' hf').injective]
    exact source_span_kernel d hUT' hf'

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
