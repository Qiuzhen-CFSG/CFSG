module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableCubicSeedGeometry
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableStarCore
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableSixSource
public import Theory.GroupTheory.SylowFixedConjugateSpanSplitting
public import Theory.GroupTheory.Commutator.SylowFixedSeed

/-!
# A noncentral intersection with the original decomposable fixed group

The actual A₆ central quotient makes S normalize L. The L-orbit of
E = Ω₁Z(S) lies in the elementary star module and in Q₁ ≤ S. Sylow
averaging supplies, for each element of E, an LS-fixed representative
modulo the moved orbit. That representative lies back in Ω₁Z(S)=E, so
the correction lies in E ∩ L. If E ∩ L centralized L, all of E would
centralize L, contrary to the same component's escape from M_Z=C_G(E).

The original source wrapper retains the selected component and actual
pre-exclusion and exchanged witnesses. It asserts no equality with
blockU(L) and uses no whole-core reconstruction or global residual premise.

Source: Aschbacher--Smith B.2.14 and 15.1.19--20, printed pp.78,1093--1095.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The actual A₆ marking and the original full omega-center force a
noncentral intersection with the same selected component. -/
theorem CaseIComponentData.PreExclusionSource.fixed_intersection_noncentral_of_six
    {T : Sylow 2 G} {M Mc V : Subgroup G} {d : CaseIComponentData T M Mc V}
    {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hMZ : d.MZ = centralizer (thompsonFixed T V : Set G))
    (hOmega : omegaOneCenterAmbient d.S = thompsonFixed T V)
    (a : (d.L ⧸ centralPreimage (pCore 2 d.L)) ≃* alternatingGroup (Fin 6)) :
    ¬ thompsonFixed T V ⊓ d.L ≤ centralizer (d.L : Set G) := by
  let := h.elementary
  let E := thompsonFixed T V
  let H := d.L ⊔ d.S
  let J := d.L ⊔ d.Q1
  let W := conjugateSpanBy E H
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
  have hSN : d.S ≤ normalizer (d.L : Set G) :=
    d.localFamily_alternating_central_normalizes hG h
      ⟨d.L_component.1,s.local_component⟩ s.quasisimple (by decide) a
  have hES : E ≤ d.S := fun e he =>
    ((mem_omegaOneCenterAmbient_iff _ _).mp (hOmega.symm ▸ he)).1
  have hEC : E ≤ centralizer (d.S : Set G) := fun e he =>
    ((mem_omegaOneCenterAmbient_iff _ _).mp (hOmega.symm ▸ he)).2.2
  have hspan : W = conjugateSpanBy E d.L :=
    conjugateSpanBy_sup_of_normalizes_seed E d.L d.S
      ((le_centralizer_iff.mp hEC).trans (Subgroup.centralizer_le_normalizer _)) hSN
  have hstar := (d.marked_core_star_geometry hi E hMZ).2.1
  have hWstar : W ≤ (starV d.L d.Q1).map J.subtype := hspan.le.trans hstar
  let : IsElementaryAbelian 2 ((starV d.L d.Q1).map J.subtype) :=
    IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWstar
  let : (d.L.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le d.L.le_normalizer hi.normalizes)
  have hWS : W ≤ d.S := hWstar.trans
    ((map_mono (show starV d.L d.Q1 ≤ pCore 2 J from map_subtype_le _)).trans
      ((source_joinCore_le_radical (source_join_input hi)).trans
        (d.catalogue_radical_le_sylow s.centralizer_sylow hu)))
  have hWH : W ≤ H := hWS.trans le_sup_right
  have hHN : H ≤ normalizer (d.L : Set G) := sup_le d.L.le_normalizer hSN
  have hmove : ⁅W,H⁆ = ⁅W,d.L⁆ :=
    commutator_conjugateSpan_eq_of_fixed_supplement E H H d.L d.S
      (hES.trans le_sup_right) le_sup_left le_sup_right H.le_normalizer hHN
      le_sup_left le_rfl hEC
  have hWL : ⁅W,H⁆ ≤ d.L := hmove.le.trans
    (le_normalizer_iff_commutator_le_right.mp (hWH.trans hHN))
  obtain ⟨P,hP⟩ := s.centralizer_sylow.restrict (show d.S ≤ H from le_sup_right)
    (sup_le d.L_component.1 d.S_le_G1)
  intro hfix
  apply d.L_not_le_MZ
  apply (le_centralizer_iff.mp ?_).trans_eq hMZ.symm
  intro e he
  obtain ⟨u,huW,hy⟩ := conjugateSpan_fixed_coset_of_sylow P (hP.symm ▸ hEC) he
  have hyE : u*e ∈ E := by
    apply hOmega.le
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hWS hy.1,elemPow_eq_one_of_isElementaryAbelian _ hy.1,
        centralizer_le (show d.S ≤ H from le_sup_right) hy.2⟩
  have huE : u ∈ E := by
    simpa only [mul_inv_cancel_right] using E.mul_mem hyE (E.inv_mem he)
  have huC := hfix ⟨huE,hWL huW⟩
  have hyC := centralizer_le (show d.L ≤ H from le_sup_left) hy.2
  simpa only [inv_mul_cancel_left] using
    (centralizer (d.L : Set G)).mul_mem ((centralizer (d.L : Set G)).inv_mem huC) hyC

/-- The original cubic decomposable action produces a component whose
intersection with the original sixteen-element E acts noncentrally on it. -/
theorem PreparedChosenModule.decomposable_three_component_fixed_intersection_noncentral
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
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
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 3 →
      ∃ e : CaseIComponentData T M Mc V,
        e.Z1 = DecomposableMarker.thompsonPlane T V (c.ambientFactor d s.first).space ∧
        e.row = .six ∧ Nat.card e.Z1 = 4 ∧
        e.PreExclusionSource h.normalized 3 ∧ e.ExchangedSource ∧
        omegaOneCenterAmbient e.S = thompsonFixed T V ∧
        thompsonFixed T V ⊓ centralizer (e.L : Set G) = e.Z1 ∧
        ¬ thompsonFixed T V ⊓ e.L ≤ centralizer (e.L : Set G) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hthree
  obtain ⟨e,heZ,hr,hc,es,_,x,_,_,hi,_,_,_,a,_⟩ :=
    h.decomposable_three_six_ms_source_without_residual hG T hempty hM hmany hJ hu hne
      hfull c d hd s π hp hs hdec hq hthree
  have hMZ := (h.decomposable_three_marked_core_geometry hG T hempty hM hJ hu hne
    hfull c d hd s π hp hs hdec hthree e heZ es).1
  obtain ⟨hOmega,hfixed⟩ := h.decomposable_marked_omegaCenter_and_component_fixed
    T hM hu hfull c d s e heZ x
  exact ⟨e,heZ,hr,hc,es,x,hOmega,hfixed,
    es.fixed_intersection_noncentral_of_six (h := h) hG hu hi hMZ hOmega a⟩

end CFSG.Quasithin.Chapter15.Section01
