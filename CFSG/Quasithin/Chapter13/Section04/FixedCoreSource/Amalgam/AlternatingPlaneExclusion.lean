module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.AlternatingBlockExclusion
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.AlternatingNearMaximum
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearPlaneSource

/-!
# Excluding the selected A₆ amalgam over the original ordinary plane

In the A₆ branch the proved near-maximum theorem puts J₁(T) in O₂(X),
hence in the second plane radical. The ordinary Thompson theorem makes
Baum(T) normal in X and forces J(T) outside the original LT two-core.
The already constructed plane MS pair therefore gives shortness from the
natural A₆ exhaustion theorem. The four-chief-factor lower bound then
contradicts the original short plane's three-factor bound.

The first theorem supplies the literal K₂=L₂ marking by aligning the
original invariant plane; the second discharges shortness itself. The
original ordinary A₆ marking and independent Natural.Exhaustion.LargeDistanceInput
remain explicit. This excludes the selected ordinary component in this
restricted plane application, not in every general S₃ pair. Both universal
13.4.7 interfaces and the remaining model selection are still required.
Source: Aschbacher–Smith 13.4.7(4), printed pp.902–903.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
open Section03.Noncentrality.SupercriticalSource NoncentralChiefRefinement
open Representation.BinaryOffender
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}
variable (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Theory.SpecificGroups.SymmetricSix.A6)
include h₀ D m h1332 hTA hTB eA eB hne hindexA hindexB hK hres eK

/-- Aligning the actual second plane supplies the literal residual equality
and excludes the selected A₆ component when the original L is short. -/
theorem original_pair_alternating_short_plane_impossible
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hb : ChapterC.IsShort L)
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)) : False := by
  let J := L ⊓ normalizer (m.naturalPreimage W : Set G)
  have hTJ := m.sylow_normalizes_inner_plane W hTW
  obtain ⟨g,hg⟩ := m.natural_plane_alignment W hW hTW
  have hi := m.aligned_inner_plane_image W g hg
  have hBJ : B = J ⊔ (T : Subgroup G) :=
    hB.trans (Solvable.second_flag_normalizer_eq D _ hTW)
  have hK₂ : (pResidual 2 B).map B.subtype = (pResidual 2 J).map J.subtype := by
    rw [hBJ]
    exact Solvable.second_parabolic_full_residual J hTJ
  exact original_pair_alternating_short_block_impossible h₀ D (m.relabel g) h1332
    hTA hTB eA eB hne hindexA hindexB K hK hres eK h structural hout hindexL
    hb J inf_le_left hTJ hi hK₂

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion

/-- The selected A₆ case is impossible over the original ordinary plane.
Near-maximum containment and shortness are constructed from the actual pair. -/
theorem original_pair_alternating_plane_impossible_of_largeDistance
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)) : False := by
  let X := A ⊔ B
  have hn := original_pair_alternating_thompson_normal h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK eK
  obtain ⟨_,hBN⟩ := original_pair_baumann_of_thompson_normal h₀ D m
    hTA hTB eA eB hne hindexA hindexB hn
  have hJne := thompson_not_le_original_core_of_outside_normalizer h D hout hn
  have hescape : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      normalizer (L : Set G) := fun hb => hout (hBN.trans hb)
  have hJQ := (original_pair_alternating_near_thompson_core h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK eK).1
  have hTX : (T : Subgroup G) ≤ X := hTB.trans le_sup_right
  have hQT : X.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow X (T.subtype hTX)
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTX] at hh
  have hQB : X.pCoreIn 2 ≤ B.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 X) (hQT.trans hTB)
    (le_sup_right.trans (X.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X))))
  have hb := original_plane_short_of_largeDistance hl h structural D m eL W hW hTW hB
    eB (hJQ.trans hQB) hJne hescape
  exact original_pair_alternating_short_plane_impossible h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK hres eK h structural hout hindexL hb W hW hTW hB

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
