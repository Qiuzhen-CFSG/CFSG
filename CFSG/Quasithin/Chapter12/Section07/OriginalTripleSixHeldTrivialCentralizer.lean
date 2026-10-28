module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldCentralizers
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPushingUpAt
import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.OddCore
import Theory.GroupTheory.TwoPerfectNormalizerControl

/-!
# The original component has trivial ambient centralizer in the Held branch

The original C.2.8 configuration excludes its ordinary component B from
M=N_G(K). If C=C_G(K) were nontrivial, C lies in M and is normal there.
Characteristic two therefore gives O2(C) nontrivial. The full residual fixer
proved in OriginalTripleSixHeldCentralizers shows that B centralizes C.
But original uniqueness over KT puts N_G(O2(C)) in M, a contradiction.

This proves the first and fourth centralizer conclusions of12.7.7, printed
p.841, without needing the later scalar X and Frattini calculations, or an
assumed two-group structure on the entire centralizer of the chosen U.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The actual ordinary point component escapes N_G(K), directly from
the original pushing-up source and its characteristic-two local subgroup. -/
theorem original_tripleSix_held_component_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hB : let H := centralizer ({(t : G)} : Set G)
      let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
      IsComponent H ((conjugateSpanBy Lt H).subgroupOf H)) :
    let H := centralizer ({(t : G)} : Set G)
    let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
    ¬ conjugateSpanBy Lt H ≤ normalizer (K : Set G) := by
  let H := centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  let B := conjugateSpanBy Lt H
  have h28 := original_tripleSix_pushingUp_at h structural D a t ht heven
  change ¬ B ≤ normalizer (K : Set G)
  intro hBM
  apply h28.component_not_le (B.subgroupOf H) hB
  intro b hb
  exact ⟨hBM hb,b.property⟩

/-- Both the full ambient centralizer of K and its original Sylow
intersection are trivial, on the literal ordinary Held configuration. -/
theorem original_tripleSix_held_component_centralizer_eq_bot
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hB : let H := centralizer ({(t : G)} : Set G)
      let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
      IsComponent H ((conjugateSpanBy Lt H).subgroupOf H))
    (hcenter :
      let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(t : G)} : Set G)).subtype
      centerIn (conjugateSpanBy Lt (centralizer ({(t : G)} : Set G))) = tripleSixPoint D a t)
    (e :
      let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(t : G)} : Set G)).subtype
      let B := conjugateSpanBy Lt (centralizer ({(t : G)} : Set G))
      B ⧸ center B ≃* Matrix.PSL3Four.PSL) :
    centralizer (K : Set G) = ⊥ ∧ (T : Subgroup G) ⊓ centralizer (K : Set G) = ⊥ := by
  let H := centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  let B := conjugateSpanBy Lt H
  let M := normalizer (K : Set G)
  let C := centralizer (K : Set G)
  have hmax := h.source_normalizer_maximal_unique_at structural
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hNM := h.source_chosen_normalizer_le_at structural
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)) D
  have hCM : C ≤ M := (centralizer_le D.le_component).trans
    ((centralizer_le_normalizer U).trans hNM)
  have hMC : M ≤ normalizer (C : Set G) := normalizer_le_normalizer_centralizer K
  have hchar : centralizer (pCore 2 M : Set M) ≤ pCore 2 M :=
    Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le T
      (h.simpleQTKE.evenCharacteristic T) hmax.1.1 D.sylow_normalizes_component)
  have hBC : B ≤ centralizer (C : Set G) := by
    apply le_centralizer_iff.mp
    have hCL : C ≤ centralizer (Lt : Set G) :=
      centralizer_le ((map_subtype_le _).trans inf_le_left)
    exact hCL.trans ((original_tripleSix_held_seed_centralizer D a t ht heven hcenter e).le.trans
      inf_le_right)
  have hzero : C = ⊥ := by
    by_contra hne
    have hcore : pCore 2 C ≠ ⊥ := pCore_ne_bot_of_core_normalizes M C hCM hchar
      ((pCoreIn_le 2 M).trans hMC) hne
    have hcoreG : C.pCoreIn 2 ≠ ⊥ := by
      intro he
      apply hcore
      exact ((pCore 2 C).map_eq_bot_iff_of_injective C.subtype_injective).mp he
    have hn := normalizer_le_normalizer_characteristic_image C (pCore 2 C)
    have hbound : normalizer (C.pCoreIn 2 : Set G) ≤ M :=
      normalizer_le_of_unique_maximalTwoLocal hmax.2 (isPGroup_pCoreIn 2 C) hcoreG
        ((sup_le K.le_normalizer D.sylow_normalizes_component).trans (hMC.trans hn))
    apply original_tripleSix_held_component_escape h structural D a t ht heven hB
    exact hBC.trans ((centralizer_le (pCoreIn_le 2 C)).trans
      ((Subgroup.centralizer_le_normalizer _).trans hbound))
  exact ⟨hzero,by rw [show centralizer (K : Set G) = ⊥ from hzero,inf_bot_eq]⟩

end CFSG.Quasithin.Chapter12.Section07
