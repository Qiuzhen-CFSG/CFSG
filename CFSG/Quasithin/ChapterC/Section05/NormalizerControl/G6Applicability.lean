module
public import CFSG.Quasithin.ChapterG.Section06.Source
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DisplacementGeneration

/-!
# G.6 applicability for the actual A₃ source action

C.5.10 supplies the elementary full span and C.5.11 its Sylow subgroup.
The canonical centralizer quotient is two-reduced and faithful. A moving
member of the original conjugate four-group acts as a transvection, and
its conjugate displacement spaces generate the entire source span.
The SQTK cover is the original X, with its literal quotient map.

Source: Aschbacher–Smith C.5.12, printed p.163, applying G.6.1 and G.6.4.
-/
public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource.RankOne Representation.BinaryOffender
universe u
variable {G : Type u} [Group G] [Finite G]
private theorem g6_hypotheses_of_transvection
    {D W C : Type u} [Group D] [Group C] [Finite D] [Finite C]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) D W) (q : C →* D)
    {𝒦 : GroupClass.{u}} (hC : IsSQTK 𝒦 C) (hq : Function.Surjective q)
    (hcore : pCore 2 D = ⊥) (hi : Function.Injective ρ.asGroupHom)
    (a : D) (ha : a^2=1) (hne : a ≠ 1)
    (ht : LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom a) ∈
      LinearEquiv.transvections (ZMod 2) W)
    (hgen : conjugateDisplacementSpan ρ a ⊤ = ⊤) :
    ChapterG.Section06.Hypotheses 𝒦 ρ a q := by
  have hfaith : Function.Injective ρ := by
    intro a b hab
    apply hi
    apply Units.ext
    exact hab
  have hrank := (LinearEquiv.mem_dilatransvections_iff_finrank
    (e := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom a))).mp
      (LinearEquiv.transvections_subset_dilatransvections ht)
  have hrank' : Module.finrank (ZMod 2) (LinearMap.range (ρ a-LinearMap.id)) ≤ 1 := by
    convert! hrank using 1
  exact {
    finite_group := inferInstance
    finite_cover := inferInstance
    finite_displacement := inferInstance
    cover_sqtk := hC
    quotient_surjective := hq
    twoCore := hcore
    faithful := hfaith
    involution := ha
    nonidentity := hne
    displacement_rank := hrank'.trans (by decide)
    generated := hgen }

/-- The actual A₃ source span satisfies every G.6.1 hypothesis, with
the original SQTK cover retained and no action or reduction certificate. -/
theorem alternating_three_g6_hypotheses
    {T K : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) (ha : ChapterC.IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (X : Subgroup G) (hKX : K ≤ X) (hTX : T ≤ X)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    {𝒦 : GroupClass.{u}} (hX : IsSQTK 𝒦 X)
    (V : Subgroup G) (hV : V = conjugateSpanBy (U K) X)
    (hVC : V ≤ centralizer (U K : Set G)) (hVT : V ≤ T)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    ∃ hp : Theory.GroupTheory.IsPReduced 2 (V.subgroupOf X),
    let : (V.subgroupOf X).Normal := hp.normal
    let : IsElementaryAbelian 2 (V.subgroupOf X) := hp.elementary
    ∃ b : X, (b : G) ∈ (U K).map (MulAut.conj x⁻¹).toMonoidHom ∧
      (b : G) ∉ centralizer (U K : Set G) ∧
      ChapterG.Section06.Hypotheses 𝒦 (Representation.centralizerQuotient (V.subgroupOf X))
        (QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X)) b)
        (QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X))) ∧
      LinearMap.GeneralLinearGroup.toLinearEquiv
        ((Representation.centralizerQuotient (V.subgroupOf X)).asGroupHom
          (QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X)) b)) ∈
        LinearEquiv.transvections (ZMod 2) (Additive (V.subgroupOf X)) := by
  subst V
  let V := conjugateSpanBy (U K) X
  have hUV : U K ≤ V := le_conjugateSpanBy _ _
  have hVX : V ≤ X := conjugateSpanBy_le_self ((map_subtype_le _).trans hKX)
  have hXV : X ≤ normalizer (V : Set G) := le_normalizer_conjugateSpanBy _ _
  have hred := alternating_three_full_span_reduced h ha hT hTK X hKX S hS hVC
  let : (V.subgroupOf X).Normal := hred.normal
  let : IsElementaryAbelian 2 (V.subgroupOf X) := hred.elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_surjective
    (subgroupOfEquivOfLe hVX).toMonoidHom (subgroupOfEquivOfLe hVX).surjective
  let q := QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X))
  let ρ := Representation.centralizerQuotient (V.subgroupOf X)
  obtain ⟨b,hb,hbC⟩ := Set.not_subset.mp hnc
  have hbT : b ∈ T := (h.conjugate_le hx).trans inf_le_left hb
  let b₀ : X := ⟨b,hTX hbT⟩
  have hB : (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ X :=
    (h.conjugate_le hx).trans (inf_le_left.trans hTX)
  have hTB : T ≤ normalizer ((U K).map (MulAut.conj x⁻¹).toMonoidHom : Set G) := by
    have hs := mem_normalizer_iff_map_conj_eq.mp ((normalizer (T : Set G)).inv_mem hx)
    have hTU := hTK.trans (normalizer_le_normalizer_characteristic_image K (blockU K))
    rw [← map_equiv_normalizer_eq,← hs]
    exact map_mono hTU
  have ht := alternating_three_relative_transvections h ha hx hnc X V hVX hXV hUV (hVT.trans hTB) hB b hb
  have hb2 : (q b₀)^2=1 := by
    have hb2 : b^2=1 := by
      let := h.elementary
      let : IsElementaryAbelian 2 ((U K).map (MulAut.conj x⁻¹).toMonoidHom) :=
        IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
      exact elemPow_eq_one_of_isElementaryAbelian b hb
    rw [← map_pow,show b₀^2=1 from Subtype.ext hb2,map_one]
  have hbne : q b₀ ≠ 1 := by
    intro he
    have hc : b₀ ∈ centralizer (V.subgroupOf X : Set X) := (QuotientGroup.eq_one_iff _).mp he
    apply hbC
    intro u hu
    exact congrArg X.subtype (hc ⟨u,hVX (hUV hu)⟩ (hUV hu))
  have hgen := alternating_three_displacement_generates h ha hTK X V hKX hVX hXV rfl b₀ hbT hbC
  refine ⟨hred,b₀,hb,hbC,?_,ht⟩
  exact g6_hypotheses_of_transvection ρ q hX (QuotientGroup.mk'_surjective _)
    hred.quotient_pCore_eq_bot (Representation.centralizerQuotient_faithful _)
    (q b₀) hb2 hbne ht hgen
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
