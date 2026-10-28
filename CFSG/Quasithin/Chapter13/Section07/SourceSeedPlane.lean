module

public import CFSG.Quasithin.Chapter13.Section07.SeedDisplacement

/-!
# The original seed plane for every actual plus offender

For any specified coordinates on U_H/U₀, the original centralizer index
makes the V₃ image two-dimensional. Original13.7.12 places the entire
commutator span of every subgroup of A* in that same plane. Thus later
model exclusions receive a bound on the whole moved space.
Source: Aschbacher–Smith13.7.12(2) and13.7.15, pp.942–944.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- Dimension and whole-span displacement on the original plus-section coordinates. -/
theorem source_plus_seed_plane
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1)
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W)
    (s : Representation.BinaryConjugationSection H (Section08.Source.UH H V₃)
      ((Section08.Source.UH H V₃) ⊓ centralizer (H.pCoreIn 2 : Set G))
      (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (B : Subgroup (H ⧸ pCore 2 H))
    (hBA : B ≤ ((conjugate (Section08.Source.VH H V) (g : G) ⊓
      (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2).subgroupOf H).map
        (QuotientGroup.mk' (pCore 2 H))) :
    Module.finrank (ZMod 2) (s.imageSpace V₃) = 2 ∧
      subspaceCommutator σ ⊤ B ≤ s.imageSpace V₃ := by
  let U := Section08.Source.UH H V₃
  let U₀ := U ⊓ centralizer (H.pCoreIn 2 : Set G)
  let Q := (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2
  let A := conjugate (Section08.Source.VH H V) (g : G) ⊓ Q
  let π := QuotientGroup.mk' (pCore 2 H)
  have hHG : H ≤ G₁ := by
    rw [d.first_normalizer]
    exact h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  have hseedU : V₃ ≤ U := le_conjugateSpanBy V₃ H
  have hinter : U₀ ⊓ V₃ = V₁ := by
    have he := seed_centralizer_eq_line d h (seed_noncentral_on_local_core h hHG hne)
    change V₃ ⊓ centralizer (H.pCoreIn 2 : Set G) = V₁ at he
    rw [← he]
    ext z
    exact ⟨fun hz => ⟨hz.2,hz.1.2⟩,fun hz => ⟨⟨hseedU hz.1,hz.2⟩,hz.1⟩⟩
  constructor
  · apply s.imageSpace_finrank_of_index V₃ hseedU 2
    rw [← inf_relIndex_right,hinter]
    have he := relIndex_mul_relIndex (⊥ : Subgroup G) V₁ V₃ bot_le h.point_lt.le
    rw [relIndex_bot_left,relIndex_bot_left,d.line_card,d.seed_card] at he
    norm_num
    omega
  · have hc := source_seed_displacement_bound d h hU hV hHG hne g hs hout
    change ⁅U,A⁆ ≤ V₃ ⊔ U₀ at hc
    apply Submodule.span_le.mpr
    rintro _ ⟨b,hb,w,_,rfl⟩
    obtain ⟨a,ha,rfl⟩ := hBA hb
    obtain ⟨z,hz⟩ := s.onto (Multiplicative.ofAdd w)
    have hw : (s.coordinates z).toAdd = w := congrArg Multiplicative.toAdd hz
    rw [← hw]
    apply (s.displacement_mem_imageSpace_iff V₃ hseedU a z).mpr
    rw [commutator_comm] at hc
    exact hc (commutator_mem_commutator ha z.property)

end CFSG.Quasithin.Chapter13.Section07
