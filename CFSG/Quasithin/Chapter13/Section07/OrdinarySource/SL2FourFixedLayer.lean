module

public import Theory.Representation.SL2OrthogonalCover.OffenderGeometry
public import CFSG.Quasithin.Chapter13.Section07.TildeOffenders
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.PairFixedIntersection
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.SeedGeneration
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.CoverProjection
public import Theory.Representation.SL2FourNaturalOrbits.Model
public import Theory.Representation.BinaryConjugationSection.DisplacementPreimage

/-!
# The fixed layer in the original natural SL₂(4) branch

The literal tilde action is faithful and the selected pair actor is an
actual offender. Containment of L₁ makes the component generate U_H, so
its natural section supplies a full cover. Cover offender geometry places
every component-fixed vector in the pair actor's moved space. The original
pair intersection then gives U₀=V₁.

This removes the fixed-layer premise in the selected SL₂(4) contradiction.
The earlier containment L₁≤K and natural-section marking remain explicit.
Source: Aschbacher–Smith 13.7.21, printed p.945.
-/

public section
open Subgroup Representation Representation.BinaryOffender

namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion Section08.TransvectionRecognition ChapterF.Section09.Setup
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionRecognition.Component
open Representation.SL2OrthogonalCover
open scoped IsMulCommutative commutatorElement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
  [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
include d

/-- In the original contained natural SL₂(4) case, the fixed layer is exactly V₁. -/
theorem source_sl2Four_fixed_layer_eq_point
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hsquare : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1)
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    (hKH : K ≤ H) (hKC : (K.subgroupOf H).IsCComponent)
    (hKn : H ≤ normalizer (K : Set G))
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* Representation.SL2FourNatural.SL)
    (hs : HasSectionModel H V₃ V₁ ρ K hKH
      (binaryNatural (F := Representation.SL2FourNatural.F)) eK)
    (hcentral : K ≤ centralizer (PlusAction.fixedLayer
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) : Set G)) :
    PlusAction.fixedLayer (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) = V₁ := by
  let U := Section08.Source.UH H V₃
  let U₀ := PlusAction.fixedLayer (ConjugateIntersections.sourceSetup T L V V₃ V₁ H)
  let A := conjugate (Section08.Source.VH H V) (g : G) ⊓
    (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2
  let π := QuotientGroup.mk' (pCore 2 H)
  let Astar := (A.subgroupOf H).map π
  obtain ⟨hE,τ,c,hτ,hcoord,hA,_⟩ := source_tilde_offenders d h hU hV g hsquare hout
  have heq : τ = ρ := by
    apply MonoidHom.ext
    intro a
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) a
    apply LinearMap.ext
    intro v
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf U) v.toMul
    have he := c.equivariant a u
    rw [hcoord,hcoord] at he
    exact he.symm.trans (hρ a u).symm
  subst τ
  let : (K.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
  let : (Section08.Source.starImage H K).Normal :=
    (inferInstance : (K.subgroupOf H).Normal).map π (QuotientGroup.mk'_surjective _)
  let e := (Section08.Components.componentStarEquiv H K hKH hKC).symm.trans eK
  have hgen := ModelExclusions.span_commutator_of_containing_normal_component d hKH hKn hL₁K
  have hem : modelActor hKH hKC eK =
      (Section08.Source.starImage H K).subtype.comp e.symm.toMonoidHom := by
    ext x
    rfl
  have hcover := exists_cover_of_section hKH hKC ρ hρ hgen.symm
    (binaryNatural (F := Representation.SL2FourNatural.F)) eK hs
  rw [hem] at hcover
  obtain ⟨p,hp⟩ := hcover
  let : IsElementaryAbelian 2 Astar := hA.1.2
  obtain ⟨S,hAS⟩ := (IsElementaryAbelian.isPGroup 2 Astar).exists_le_sylow
  have hfixed := Representation.SL2NaturalOffenders.fixed_le_moved_of_cover_offender
    ρ hτ (Section08.Source.starImage H K) e
    (by simpa only [Nat.card_eq_fintype_card] using Representation.SL2FourNatural.card_field)
    p hp S hAS hA
  have hAH : A ≤ H := (pair_actor_elementary_nontrivial d h hU hV g hsquare hout).1
  have hcU : ⁅U,A⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp
    (hAH.trans (le_normalizer_conjugateSpanBy V₃ H))
  have hbound : U₀ ≤ ⁅U,A⁆ ⊔ V₃ := by
    intro u hu
    let u' : U := ⟨u,hu.1⟩
    have hf : vector H V₃ V₁ u' ∈ fixedSpace ρ (Section08.Source.starImage H K) := by
      rintro ⟨a,ha⟩
      obtain ⟨a,ha,rfl⟩ := ha
      change ρ (QuotientGroup.mk' (pCore 2 H) a) (vector H V₃ V₁ u') =
        vector H V₃ V₁ u'
      rw [hρ]
      have hc : Commute a.val u := (show Commute u a.val from (hcentral ha) u hu).symm
      have he : a.val*u*a.val⁻¹ = u := by rw [hc.eq,mul_inv_cancel_right]
      congr 1
      exact Subtype.ext he
    have hv := hfixed hf
    change vector H V₃ V₁ u' ∈
      subspaceCommutator ρ ⊤ (Section08.Source.starImage H A) at hv
    rw [← commutatorImage_eq_subspaceCommutator A hAH ρ hρ] at hv
    obtain ⟨w,hw,hwe⟩ := hv
    have hi : (c.coordinates u').toAdd ∈ c.imageSpace ⁅U,A⁆ := by
      apply (c.mem_imageSpace_iff _ _).mpr
      refine ⟨w,hw,?_⟩
      rw [hcoord,hcoord]
      exact congrArg Additive.ofMul hwe
    have huC := (c.coordinates_mem_imageSpace_iff ⁅U,A⁆ hcU u').mp hi
    exact (sup_le_sup_left (d.line_le_plane.trans d.plane_le_seed) _) huC
  have hpairs := OrdinarySource.pair_fixed_intersection_of_normal_component d
    h1221 h hU hV hne (K.subgroupOf H) hKC inferInstance
    (by rw [map_subgroupOf_eq_of_le hKH]; exact hcentral) g hsquare hout
  exact hpairs.2.2 hbound

end CFSG.Quasithin.Chapter13.Section07
