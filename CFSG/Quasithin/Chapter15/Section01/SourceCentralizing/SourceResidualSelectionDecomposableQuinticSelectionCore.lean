module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartner
public import Theory.GroupTheory.PCoreImage

/-!
# The actual partner kernel and its two-core

For U=V(Mc), the full kernel C=C_G(U) lies in Mc and has the same
embedded two-core Q as Mc. The core lies in T and therefore normalizes
the original Thompson fixed subgroup E. The source partner containment
U≤E gives E≤C, and the actual elementary local module lies in Q.
Thus [Q,E]≤E∩Q. The stronger bound [Q,E]≤U, needed for the proposed
relative Baer--Suzuki argument, remains a separate source obligation.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

theorem PreparedChosenModule.decomposable_five_partner_kernel_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      let Uc := localModule T Mc
      let E := thompsonFixed T V
      let C := centralizer (Uc : Set G)
      let Q := C.pCoreIn 2
      C ≤ Mc ∧ Q = Mc.pCoreIn 2 ∧ Q ≤ (T : Subgroup G) ∧
        Q ≤ normalizer (E : Set G) ∧ C ⊓ centralizer (Q : Set G) ≤ Q ∧
        E ≤ C ∧ Uc ≤ E ⊓ Q ∧ ⁅Q,E⁆ ≤ E ⊓ Q := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive
  let Uc := localModule T Mc
  let E := thompsonFixed T V
  let C := centralizer (Uc : Set G)
  let Q := C.pCoreIn 2
  obtain ⟨hEN,_,hUE⟩ := h.decomposable_five_partner_control
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  have hMcC : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMcC.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hMcH : Mc ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hMcC.1.1,hTMc⟩
  let : IsElementaryAbelian 2 Uc := localModule_elementary_from_source hG T hMcH
  have hUN : Mc ≤ normalizer (Uc : Set G) := le_normalizer_conjugateSpanBy _ _
  have hCN : Mc ≤ normalizer (C : Set G) :=
    hUN.trans (normalizer_le_normalizer_centralizer _)
  have hCMc : C ≤ Mc := localModule_centralizer_le_partner T Mc hu
  have hQC : Mc.pCoreIn 2 ≤ C := by
    have hred := localModule_reduced_from_source hG T hMcH
    rintro x ⟨q,hq,rfl⟩ u hu
    exact congrArg Mc.subtype ((le_centralizer_iff.mp hred.le_centralizer_pCore)
      hq ⟨u,localModule_le T hTMc hu⟩ hu)
  have he : Q = Mc.pCoreIn 2 := le_antisymm
    (pCoreIn_mono_of_normalizes hCMc hCN)
    (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 Mc) hQC
      (hCMc.trans (Mc.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc)))))
  have hQT : Q ≤ (T : Subgroup G) := by
    rw [he]
    have hh := pCoreIn_le_sylow Mc (T.subtype hTMc)
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc] at hh
  have hTE : (T : Subgroup G) ≤ normalizer (E : Set G) :=
    (le_inf (hM.1.2.trans h.normalized)
      ((ChapterB.le_normalizer_thompsonJ _ _).trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hself : C ⊓ centralizer (Q : Set G) ≤ Q := by
    rw [he]
    exact (inf_le_inf_right _ hCMc).trans
      (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hMcH)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
  have hEC : E ≤ C :=
    (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le hUE)
  have hUQ : Uc ≤ Q := by
    rw [he]
    exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 Uc)
      (localModule_le T hTMc) hUN
  have hEQ : E ≤ normalizer (Q : Set G) := hEC.trans
    (C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pCore 2 C)))
  exact ⟨hCMc,he,hQT,hQT.trans hTE,hself,hEC,le_inf hUE hUQ,
    le_inf (le_normalizer_iff_commutator_le_right.mp (hQT.trans hTE))
      (le_normalizer_iff_commutator_le_left.mp hEQ)⟩

end CFSG.Quasithin.Chapter15.Section01
