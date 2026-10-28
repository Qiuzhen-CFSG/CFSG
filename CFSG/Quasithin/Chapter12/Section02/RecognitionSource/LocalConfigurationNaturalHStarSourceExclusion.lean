module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceRank
public import Theory.Representation.BinaryConjugationSection.AlternatingSevenGeneration

/-!
# The final A₇ centralizer-generation exclusion in 12.2.19

A marked faithful binary four-dimensional section for an overgroup Y of the
original residual has generating point centralizers at two distinct nonzero
vectors. If the corresponding original elements belong to V, no escape puts
both centralizers in N_G(L). Hence Y lies there, contradicting residual escape.

The section, its surjective actor and its two original points are explicit
inputs here. Constructing them from the nonsolvable source alternatives and
the natural TI-pair analysis remains an upstream obligation; this conditional
exclusion alone does not assert H is solvable.

Source: Aschbacher--Smith, final paragraph of 12.2.19, printed p.802.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open Representation.BinaryAlternatingSevenControl
universe u v
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H : Subgroup G}
variable {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

theorem chosen_hstar_false_of_seven_section_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (Y J : Subgroup G) (hKY : (pResidual 2 H).map H.subtype ≤ Y)
    (ρ : Representation (ZMod 2) A7 W) (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) W = 4)
    (f : Y →* A7) (hs : Function.Surjective f)
    (C : Representation.BinaryConjugationSection Y J ⊥ (ρ.comp f))
    (v w : J) (hvV : (v : G) ∈ V) (hwV : (w : G) ∈ V)
    (hv : v ≠ 1) (hw : w ≠ 1) (hvw : v ≠ w) : False := by
  have hgen := Representation.BinaryConjugationSection.point_centralizers_generate_of_alternatingSeven
    ρ hf hd f hs C v w hv hw hvw
  have hv1 : (v : G) ≠ 1 := fun he => hv (Subtype.ext he)
  have hw1 : (w : G) ≠ 1 := fun he => hw (Subtype.ext he)
  have hY : Y ≤ normalizer (L : Set G) := by
    intro y hy
    have ht : (⊤ : Subgroup Y) ≤ (normalizer (L : Set G)).subgroupOf Y := by
      rw [← hgen]
      exact sup_le (comap_mono (hnone v hvV hv1)) (comap_mono (hnone w hwV hw1))
    exact ht (mem_top (⟨y,hy⟩ : Y))
  exact chosen_hstar_residual_escape_at h structural hH (hKY.trans hY)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
