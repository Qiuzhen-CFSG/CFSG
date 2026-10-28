module
public import CFSG.Quasithin.Chapter13.Section07.FixedLineEndgame
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.NaturalFlag.FixedSpaceTransport

/-!
# The natural L₃(2) fixed-layer contradiction in 13.7.16

For W=[U₀,K], a normal component makes W H-invariant. The natural line
residual has no fixed vector, while the Borel fixed line is displaced by
the line radical. Since W lies in O₂(LT), it normalizes the opposite span;
that displacement therefore belongs to the opposite span. The proved pair
generation contradiction now applies to the literal source groups.

The inputs are the actual natural conjugation marking and the three actor
images from the preceding doubled-natural-module analysis. These encode
original13.5.2(3) and the line-parabolic placement in13.7.16, not fixed-space
or centralization conclusions. Source: Aschbacher–Smith13.7.16, p.944.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.NaturalFixedLine
open Section08.SourceCompletion ChapterF.Section09.Setup
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

omit [Finite G] in
/-- The original normal component has an H-invariant fixed-layer commutator. -/
theorem component_layer_normalized (K : Subgroup G)
    (hKn : H ≤ normalizer (K : Set G)) :
    H ≤ normalizer ((⁅PlusAction.fixedLayer
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ H),K⁆ : Subgroup G) : Set G) := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  have hHU₀ := PlusAction.fixedLayer_normalized (D := F)
  intro t ht
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hHU₀ ht),
    mem_normalizer_iff_map_conj_eq.mp (hKn ht)]

private theorem core_normalizes_opposite
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G)) :
    (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2 ≤
      normalizer (conjugate (Section08.Source.UH H V₃) (g : G) : Set G) := by
  let X := L ⊔ (T : Subgroup G)
  let Q := X.pCoreIn 2
  let U := Section08.Source.UH H V₃
  have hQH : Q ≤ H := (h.sylow_centralizer.symm.le.trans inf_le_left).trans h.T_le_H
  have hnQ : X ≤ normalizer (Q : Set G) := X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hq : Q.map (MulAut.conj (g : G)⁻¹).toMonoidHom = Q :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (Q : Set G)).inv_mem (hnQ g.property))
  have hh := map_mono (f := (MulAut.conj (g : G)⁻¹).toMonoidHom)
    (hQH.trans (le_normalizer_conjugateSpanBy V₃ H))
  change Q.map (MulAut.conj (g : G)⁻¹).toMonoidHom ≤
    (normalizer (U : Set G)).map (MulAut.conj (g : G)⁻¹).toMonoidHom at hh
  rw [hq, map_normalizer_eq_of_bijective U (MulAut.conj (g : G)⁻¹).bijective] at hh
  exact hh

/-- The actual natural-module flag on a nonzero fixed-layer component is
impossible. All fixed-space and displacement conclusions are derived from
literal matrix actor images. -/
theorem source_no_natural_fixed_layer_flag
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,H.pCoreIn 2⁆ ≠ ⊥)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    (K : Subgroup G) (hKH : K ≤ H) (hKn : H ≤ normalizer (K : Set G))
    (e : (⁅PlusAction.fixedLayer (ConjugateIntersections.sourceSetup T L V V₃ V₁ H),K⁆ : Subgroup G) ≃* Model)
    (hL : lineA ≤ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁.subgroupOf H).map
      (linearAction H _ (component_layer_normalized K hKn) e))
    (hT : borelSL ≤ ((T : Subgroup G).subgroupOf H).map
      (linearAction H _ (component_layer_normalized K hKn) e))
    (hR : lineV ≤ ((conjugate (Section08.Source.UH H V₃) (g : G)).subgroupOf H).map
      (linearAction H _ (component_layer_normalized K hKn) e)) : False := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let U₀ := PlusAction.fixedLayer F
  let W := ⁅U₀,K⁆
  let Ug := conjugate F.UH (g : G)
  have hWU : W ≤ U₀ := le_normalizer_iff_commutator_le_left.mp
    (hKH.trans (PlusAction.fixedLayer_normalized (D := F)))
  have hWQ : W ≤ (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2 :=
    (hWU.trans inf_le_left).trans
      ((le_conjugateSpanBy F.UH L).trans (span_UH_L_le_core d h hU))
  have hWUg : W ≤ normalizer (Ug : Set G) :=
    hWQ.trans (core_normalizes_opposite h g)
  have hfixed : W ⊓ centralizer (F.L₁ : Set G) = ⊥ :=
    fixed_eq_bot_of_line_residual H W (component_layer_normalized K hKn) e F.L₁ hL
  have hopp : W ⊓ centralizer (T : Set G) ≤ Ug :=
    (fixed_le_commutator_of_line_radical H W (component_layer_normalized K hKn) e
      (T : Subgroup G) Ug hT hR).trans
        (le_normalizer_iff_commutator_le_right.mp hWUg)
  have hb : W = ⊥ := pair_normal_fixed_layer_eq_bot d h hU hV hne g hout W hWU
    (h.T_le_H.trans (component_layer_normalized K hKn)) hfixed hopp
  have hw : (e.symm (Multiplicative.ofAdd (![1,0,0] : Fano.Vector)) : G) = 1 := by
    have hm := (e.symm (Multiplicative.ofAdd (![1,0,0] : Fano.Vector))).property
    change (e.symm (Multiplicative.ofAdd (![1,0,0] : Fano.Vector)) : G) ∈ W at hm
    rwa [hb, mem_bot] at hm
  have hw' : e.symm (Multiplicative.ofAdd (![1,0,0] : Fano.Vector)) = 1 := Subtype.ext hw
  have hz := congrArg e hw'
  simp only [MulEquiv.apply_symm_apply, map_one] at hz
  have : (1 : ZMod 2) = 0 := congrFun hz 0
  exact one_ne_zero this

end CFSG.Quasithin.Chapter13.Section07.NaturalFixedLine
