module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearPlaneShort
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.PlaneMaximumAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearBlockSourceAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.PlaneShortAt

/-!
# Residual movement in the actual guarded linear plane

Align the original invariant plane to obtain the literal K2=L2.
The short-block exclusion then forces its entire two-residual to be
moved by J1(T). The natural MS theorem discharges shortness in the
second theorem; only independent large-distance exhaustion remains.
Source: Aschbacher--Smith 13.4.7(4), printed pp.902--903.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
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
      Matrix.PSL3Two.PSL)
include h₀ D m h1332 hTA hTB eA eB hne hindexA hindexB hK hres eK

/-- Full movement of the original second two-residual in the short branch,
with action, Sylow, plane marking and maximum-family premises discharged. -/
theorem original_pair_linear_short_movement_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hb : ChapterC.IsShort L)
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)) :
    ⁅(pResidual 2 B).map B.subtype,ChapterB.thompsonJ (T : Subgroup G) 1⁆ =
      (pResidual 2 B).map B.subtype := by
  have hc : ⁅(pResidual 2 B).map B.subtype,ChapterB.thompsonJ (T : Subgroup G) 1⁆ =
      (pResidual 2 B).map B.subtype := by
    apply (original_residual_thompson_one_iff hTB eB).mpr
    intro hn
    obtain ⟨eL⟩ := Solvable.ordinary_of_short_core_marking D m hb
    have hf := original_plane_maximum_family_of_thompson_one_bound_at
      h structural D m eL W hW hTW hB hn
    let J := L ⊓ normalizer (m.naturalPreimage W : Set G)
    have hTJ := m.sylow_normalizes_inner_plane W hTW
    obtain ⟨g,hg⟩ := m.natural_plane_alignment W hW hTW
    have hi := m.aligned_inner_plane_image W g hg
    have hBJ : B = J ⊔ (T : Subgroup G) :=
      hB.trans (Solvable.second_flag_normalizer_eq D _ hTW)
    have hK₂ : (pResidual 2 B).map B.subtype = (pResidual 2 J).map J.subtype := by
      rw [hBJ]
      exact Solvable.second_parabolic_full_residual J hTJ
    exact original_pair_linear_short_block_impossible_at h₀ D (m.relabel g) h1332
      hTA hTB eA eB hne hindexA hindexB K hK hres eK h structural hout hindexL
      hb hf J inf_le_left hTJ hi hK₂
  exact hc

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion

/-- In the selected ordinary linear plane case, the MS pair is constructed
and shortness is discharged. J₁(T) moves the entire second two-residual
and is not normalized by the join. Natural large-distance exhaustion
remains the independent earlier source input. -/
theorem original_pair_linear_plane_movement_of_largeDistance_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)) :
    ⁅(pResidual 2 B).map B.subtype,ChapterB.thompsonJ (T : Subgroup G) 1⁆ =
        (pResidual 2 B).map B.subtype ∧
      ¬ A ⊔ B ≤ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) := by
  have hc : ⁅(pResidual 2 B).map B.subtype,ChapterB.thompsonJ (T : Subgroup G) 1⁆ =
      (pResidual 2 B).map B.subtype := by
    apply (original_residual_thompson_one_iff hTB eB).mpr
    intro hJ
    have hn := original_pair_linear_thompson_normal_at h₀ h structural D m
      hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK eK
    obtain ⟨_,hbN⟩ := original_pair_baumann_of_thompson_normal h₀ D m
      hTA hTB eA eB hne hindexA hindexB hn
    have hJne := thompson_not_le_original_core_of_outside_normalizer h D hout hn
    have hescape : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
        normalizer (L : Set G) := fun hb => hout (hbN.trans hb)
    have hb := original_plane_short_of_largeDistance_at hl h structural D m eL W hW hTW hB
      eB hJ hJne hescape
    have hshort := original_pair_linear_short_movement_at h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK hres eK h structural hout hindexL hb W hW hTW hB
    exact ((original_residual_thompson_one_iff hTB eB).mp hshort) hJ
  exact ⟨hc,not_thompson_one_normalizer_of_residual_movement hTB eB le_sup_right hc⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
