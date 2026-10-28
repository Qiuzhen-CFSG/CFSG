module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixOrdinaryBlock
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldTrivialCentralizer
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AhatSixCoreSplit
public import CFSG.Quasithin.Chapter3.Section02

/-!
# The original whole two-core and module centralizer in the Held branch

The actual exceptional block has its original commutator module U. Its
cohomology split and the proved trivial ambient component centralizer force
O2(KT)=U. The original maximal two-local uniqueness and characteristic two
then apply3.2.11 to give O2(K)=O2(N_G(K))=C_G(U)=U and N_G(U)=N_G(K).
No block, core equality or cohomological displacement is retained as an input.

Source: Aschbacher--Smith12.7.6 and12.7.7, printed pp.840--841.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- Full core recovery from the literal ordinary point configuration. -/
theorem original_tripleSix_held_core_recovery
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
    K.pCoreIn 2 = U ∧ (K ⊔ (T : Subgroup G)).pCoreIn 2 = U ∧
      (normalizer (K : Set G)).pCoreIn 2 = U ∧
      normalizer (U : Set G) = normalizer (K : Set G) ∧
      centralizer (U : Set G) = U := by
  obtain ⟨hblock,hmodule⟩ := original_tripleSix_ordinary_exceptional_block
    h.toHypothesis1221 D a t ht heven hcenter e
  have hc := (original_tripleSix_held_component_centralizer_eq_bot
    h structural D a t ht heven hB hcenter e).1
  let H := K ⊔ (T : Subgroup G)
  let M := normalizer (K : Set G)
  have hHN : H ≤ M := sup_le K.le_normalizer D.sylow_normalizes_component
  have hQ : H.pCoreIn 2 = U := by
    have hs := hblock.normalizer_twoCore_eq_module_sup_centralizer
      (show K ≤ H from le_sup_left) hHN
    simpa only [hmodule,hc,inf_bot_eq,sup_bot_eq] using hs
  have hK : K.pCoreIn 2 = U := le_antisymm
    ((pCoreIn_mono_of_normalizes (show K ≤ H from le_sup_left) hHN).trans_eq hQ)
    D.le_componentCore
  have hmax := h.source_normalizer_maximal_unique_at structural
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hchar : centralizer (pCore 2 M : Set M) ≤ pCore 2 M :=
    Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le T
      (h.simpleQTKE.evenCharacteristic T) hmax.1.1 D.sylow_normalizes_component)
  let := D.elementary
  obtain ⟨hM,hN,hC,_⟩ := Chapter3.Section02.lemma_3_2_11_of_core_containment T K H M U
    le_sup_right hHN K.le_normalizer rfl hmax.1 hchar hQ.symm D.le_componentCore D.ne_bot
  exact ⟨hK,hQ,hM,hN,hC⟩

end CFSG.Quasithin.Chapter12.Section07
