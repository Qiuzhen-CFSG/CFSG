module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalBlockLine

/-!
# The source-preferred block and ambient Sylow exclusion

Retain the weight-two preference through the actual Sylow selection and
12.6.11 residual-strictness argument. With C_V(L) nontrivial, the existing
quasisimple exclusions give actual nonquasisimplicity of K_v. The aligned
conjugator and common commutator line now prove the nonblock assertion
of 12.6.16(2) when the selected S is an ambient Sylow.

At this same preferred point, normalizer escape constructs the original
A8-block L. Applying the nonblock result excludes an ambient Sylow
centralizing that point and containing its original T_v. No additional
choice, block or module premise is left in this application.

HS/J4 exclusions in the remaining original branch, canonical-module and
local-block arguments, splitting and fixed-space elimination remain;
neither 12.6.2 nor 12.6.23 is asserted. Earlier invariance/TI retain
producer qt-d-1222-source and final discharge owner qt-d-12634-source.
Source: Aschbacher--Smith 12.6.11, 12.6.16(2) and 12.6.18, printed
pp.825--827, combined manuscript of 1 March 2004.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher Representation BinaryPermutation BinaryPermutation.EightNonsingular
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The 12.6.11 argument at a fixed selected point, so additional source
choice properties are retained through the residual-strictness reduction. -/
theorem SourceHypothesis.nonsingular_residual_strict_of_normalizer_control
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (w : V) (hw : D.Nonsingular w) (he : ¬ Gv (w : G) ≤ M L)
    (hs : Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)))
    (hctrl : Gv (w : G) ≤ normalizer (Lv L (w : G) : Set G) →
      Gv (w : G) ⊓ normalizer (Vv L V (w : G) : Set G) ≤ M L) :
    Lv L (w : G) < Kv (w : G) := by
  apply lt_of_le_of_ne (Lv_le_Kv_of_A6 L (w : G)
    (Classical.choice (D.nonsingular_local_quotient H.chosen H.source.quasisimple w hw)))
  intro heq
  have hn : Gv (w : G) ≤ normalizer (Lv L (w : G) : Set G) := by
    rw [heq]
    exact (normal_subgroupOf_iff_le_normalizer (Kv_le_Gv _)).mp (Kv_normalIn_Gv _)
  have hc : Gv (w : G) ⊓ centralizer (Vv L V (w : G) : Set G) ≤ M L :=
    (inf_le_inf le_rfl (Subgroup.centralizer_le_normalizer _)).trans (hctrl hn)
  have hJ : ¬ Stellmacher.elementaryAbelianMaxJ (Tv T (w : G)) ≤ Q T L := by
    intro hJ
    exact H.small_thompson_moves_normal_overmodule D w hw hs hJ he hc
      (componentOrbit (Vv L V (w : G)) (Gv (w : G)))
      (le_componentOrbit _ _) (le_normalizer_componentOrbit _ _)
      (H.small_thompson_closure_centralized D w hw hTV hs hJ heq)
  have hg := (H.nonsingular_thompson_generation D w hw hTV hs hJ).2.1
  have heW := H.reduced_point_commutator_eq D w hw hTV hs hn hc hg
  let A := Gv (w : G)
  let U := reducedTwoSubgroup A
  let B := (Lv L (w : G)).subgroupOf A
  let : B.Normal := normal_subgroupOf_of_le_normalizer hn
  have hW : (⁅U,B⁆ : Subgroup A).map A.subtype = Vv L V (w : G) := by
    rw [map_commutator,map_subgroupOf_eq_of_le (Lv_le_Gv L (w : G))]
    exact heW
  have hnW : A ≤ normalizer (Vv L V (w : G) : Set G) := by
    rw [←hW]
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      (⁅U,B⁆ : Subgroup A).le_normalizer_map A.subtype
  exact he ((le_inf le_rfl hnW).trans (hctrl hn))

/-- Source 12.6.16(2), with the original preferred choice and ambient Sylow.
The nonquasisimplicity premise is discharged by the nontrivial original fixed space. -/
theorem SourceHypothesis.nonsingular_not_short_of_preferred_ambient_sylow
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hz : ZV L V ≠ ⊥)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (hproj : ∀ w, coreToNatural (Fin 8) (E w) = D.coordinates (Submodule.Quotient.mk w))
    (v : V) (hv : D.Nonsingular v) (he : ¬ Kv (v : G) ≤ M L)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (hpref : ∀ u : V, wordWeight (E (Additive.ofMul u)).val = 2 →
      ¬ Gv (u : G) ≤ M L → wordWeight (E (Additive.ofMul v)).val = 2)
    (P : Sylow 2 G) (hPG : (P : Subgroup G) ≤ Gv (v : G))
    (hTP : Tv T (v : G) ≤ (P : Subgroup G)) : ¬ ChapterC.IsShort L := by
  have hnq : ¬ IsQuasisimple (Kv (v : G)) := fun h =>
    hz (H.nonsingular_quasisimple_fixed_eq_bot D v hv h hTV hi he)
  have hn := H.nonsingular_normalizer_escape_of_not_quasisimple D v hv hTV hnq hs hi he
  have hlt : Q T L < Rv T L (v : G) := lt_of_le_of_ne (Q_le_Rv H.chosen v)
    (fun h => hn (h ▸ H.core_normalizer_le))
  obtain ⟨g,hgK,_,_,hgR,_,hgM⟩ :=
    H.nonsingular_full_alignment_of_ambient_sylow D v hv hTV hz hnq hs hi he P hPG hTP
  intro hshort
  exact H.nonsingular_aligned_block_contradiction_of_preferred D hTV hshort
    E hE hproj v hv he hpref hlt g hgM hgK hgR

/-- At the actual source-preferred point, the constructed A8-block excludes
an ambient Sylow in its centralizer. Every preference and block premise is discharged. -/
theorem SourceHypothesis.exists_preferred_nonsingular_no_ambient_sylow_of_fixed
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hz : ZV L V ≠ ⊥)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      Lv L (w : G) < Kv (w : G) ∧ ¬ Kv (w : G) ≤ M L ∧
      ChapterC.IsAlternatingBlock L 8 ∧
      ∀ P : Sylow 2 G, (P : Subgroup G) ≤ Gv (w : G) →
        ¬ Tv T (w : G) ≤ (P : Subgroup G) := by
  obtain ⟨E,hE,hproj⟩ := D.core_marking_of_fixed_ne_bot H.chosen hz
  obtain ⟨w,hw,hew,hs,hi,hpref,hctrl⟩ :=
    H.exists_preferred_nonsingular_core_control D hTV hTI E hE hproj v hv he
  have hlt := H.nonsingular_residual_strict_of_normalizer_control D hTV w hw hew hs hctrl
  have hnot : ¬ Kv (w : G) ≤ M L := fun h => hlt.ne (H.Kv_eq_Lv_of_le_normalizer D w hw h).symm
  have hnq : ¬ IsQuasisimple (Kv (w : G)) := fun h =>
    hz (H.nonsingular_quasisimple_fixed_eq_bot D w hw h hTV hi hnot)
  have hn := H.nonsingular_normalizer_escape_of_not_quasisimple D w hw hTV hnq hs hi hnot
  have hb := (H.nonsingular_original_alternating_block D hTV w hw hn).1
  refine ⟨w,hw,hew,hs,hi,hlt,hnot,hb,fun P hPG hTP => ?_⟩
  exact H.nonsingular_not_short_of_preferred_ambient_sylow D hTV hz E hE hproj
    w hw hnot hs hi hpref P hPG hTP hb.2.1

end CFSG.Quasithin.Chapter12.Section06
