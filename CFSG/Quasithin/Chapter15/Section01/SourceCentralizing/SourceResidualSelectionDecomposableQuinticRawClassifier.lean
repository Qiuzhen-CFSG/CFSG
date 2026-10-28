module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawStar
public import CFSG.Quasithin.Chapter1.SourceInputs.KnownSimple
public import CFSG.Quasithin.Chapter1.Section01.ModelActions115.Transport
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawCubic
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawOrdinary

/-!
# One literal quintic component with both initial classification branches

Select the actual outside component once. Its original source facts, cubic
centralizer obstruction, complete ordinary marked actions and constrained
rank-one-or-star alternative all refer to that same L. Whole-M generation
and the final normalization conclusion remain unasserted.

The two internal imports deliberately reuse this proof package's private
cubic and ordinary transport proofs on the selected L. No private helper
appears in the public theorem type; no frozen module is widened.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]

/-- Both genuine initial classifiers and the cubic-centralizer obstruction
are available on one actual original quintic component, without M-generation. -/
theorem PreparedChosenModule.decomposable_five_partner_four_raw_classifier
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
    ∀ (s : ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 4 →
      let Z1 := thompsonPlane T V (c.ambientFactor d s.first).space
      let G1 := centralizer (Z1 : Set G)
      let MZ := G1 ⊓ Mc
      let Q1 := MZ.pCoreIn 2
      let S := (T : Subgroup G) ⊓ G1
      let C := M ⊓ G1
      let R := (pResidual 2 C).map C.subtype
      let W := ⁅V,R⁆
      let Y := (pResidual 2 MZ).map MZ.subtype
      letI := caseI_module_centralizer_normal (Z1 := Z1) h.normalized
      ∃ L : Subgroup G,
        Z1 ≤ thompsonFixed T V ∧ Nat.card Z1 = 4 ∧
        Nat.card (pResidual 2 (C ⧸ (M ⊓ centralizer (V : Set G)).subgroupOf C)) = 5 ∧
        MZ = centralizer (thompsonFixed T V : Set G) ∧
        pPrimeCore 2 G1 = ⊥ ∧ Chapter1.IsSylowIn 2 S G1 ∧
        (S.subgroupOf (T : Subgroup G)).Normal ∧
        (pResidual 2 (M ⊓ Mc ⊓ G1 : Subgroup G)).map (M ⊓ Mc ⊓ G1).subtype =
          (pResidual 2 (M ⊓ centralizer (V : Set G) : Subgroup G)).map
            (M ⊓ centralizer (V : Set G)).subtype ∧
        centralInvolutions T ⊓ V ≤ Z1 ⊔ W ∧
        Q1 ≠ ⊥ ∧ Q1.characteristicNormalizerClosure ≤ Mc ∧
        G1 ⊓ normalizer (Q1 : Set G) = MZ ∧
        (T : Subgroup G) ≤ normalizer (MZ : Set G) ∧
        (T : Subgroup G) ≤ normalizer (Q1 : Set G) ∧
        normalizer (Y : Set G) ≤ Mc ∧ Y ≤ centralizer (centralInvolutions T : Set G) ∧
        (∃ P : Sylow 2 G1, (P : Subgroup G1).map G1.subtype = S ∧
          ∀ z ∈ centralInvolutions T, z ≠ 1 → Chapter1.Lemma115Hypotheses G1 P Mc z) ∧
        L ∈ Chapter1.cComponentsIn G1 ∧ ¬ L ≤ MZ ∧
        IsQuasisimple (L ⧸ pCore 2 L) ∧ L ∈ Chapter1.L G S ∧
        Chapter1.IsSylowIn 2 (S ⊓ L) L ∧ ¬ L ≤ M ∧
        R ⊔ W ≤ normalizer (L : Set G) ∧ ⁅L,W⁆ ≠ ⊥ ∧
        (primeToResidual 3 (M ⊓ L : Subgroup G)).map (M ⊓ L).subtype ≤
          centralizer (V : Set G) ∧
        S ⊓ centralizer (((primeToResidual 3 (M ⊓ L : Subgroup G)).map
          (M ⊓ L).subtype) : Set G) ≠ S ⊓ centralizer (L : Set G) ∧
        ((IsComponent G1 (L.subgroupOf G1) ∧
          center L = pCore 2 L ∧ IsPGroup 2 (center L) ∧
          centralInvolutions T ≤ normalizer (L : Set G) ∧
          centralInvolutions T ⊓ centralizer (L : Set G) = ⊥ ∧
          ∀ z ∈ centralInvolutions T, z ≠ 1 →
            ⁅L,zpowers z⁆ = L ∧ ∃ α : MulAut L,
              (∀ x : L, (α x : G) = z*x*z⁻¹) ∧ ModelAction115 L α) ∨
          (generalizedFitting L = pCore 2 L ∧
            (((∃ n : ℕ, IsL2EvenBlock L n) ∨ IsAlternatingBlock L 5) ∨
              ∃ hi : Input KnownSimple.IsKnownSimple G1 Q1 MZ L,
                StarModels.Model (starImage L Q1 L) ∧
                  (coreToStar hi.normalizes).ker ≤ center (L ⧸ pCore 2 L) ∧
                  (Nat.card (center (L ⧸ pCore 2 L)) = 1 ∨
                    Nat.card (center (L ⧸ pCore 2 L)) = 3)))) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let Z1 := thompsonPlane T V (c.ambientFactor d s.first).space
  let G1 := centralizer (Z1 : Set G)
  let S := (T : Subgroup G) ⊓ G1
  let C := M ⊓ G1
  let R := (pResidual 2 C).map C.subtype
  let W := ⁅V,R⁆
  obtain ⟨L,hZ,hZcard,hcard,hMZ,ho,hSylG,hSn,hI,hseed,hQne,hcontrol,hn,
    hTn,hTQ,hresN,hYseed,h115,hLc,hout,hquasi,hloc,hSyl,houtM,hnL,hmove,hcases⟩ :=
    h.decomposable_five_partner_four_raw_star
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  have hres := quintic_quotient_cubic_residual h.normalized hLc.1 hcard
  have hneq : S ⊓ centralizer (((primeToResidual 3 (M ⊓ L : Subgroup G)).map
      (M ⊓ L).subtype) : Set G) ≠ S ⊓ centralizer (L : Set G) := by
    intro he
    have hVT : V ≤ (T : Subgroup G) := by
      let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer h.normalized
      let := IsElementaryAbelian.subgroupOf h.le_selected (p := 2)
      have hh := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf M)).le_sylow_of_normal
        (T.subtype hM.1.2)
      simpa only [map_subgroupOf_eq_of_le h.le_selected,Sylow.coe_subtype,
        map_subgroupOf_eq_of_le hM.1.2] using map_mono (f := M.subtype) hh
    have hWV : W ≤ V := le_normalizer_iff_commutator_le_left.mp
      (((map_subtype_le _).trans inf_le_left).trans h.normalized)
    have hWS : W ≤ S := hWV.trans (le_inf hVT
      (V.le_centralizer.trans (centralizer_le (hZ.trans inf_le_left))))
    have hWC := hWV.trans (le_centralizer_iff.mp hres)
    have hWL : W ≤ centralizer (L : Set G) := ((le_inf hWS hWC).trans he.le).trans inf_le_right
    apply hmove
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hWL
  refine ⟨L,hZ,hZcard,hcard,hMZ,ho,hSylG,hSn,hI,hseed,hQne,hcontrol,hn,
    hTn,hTQ,hresN,hYseed,h115,hLc,hout,hquasi,hloc,hSyl,houtM,hnL,hmove,hres,hneq,?_⟩
  rcases hcases with hordinary | hconstrained
  · obtain ⟨hc,hc2⟩ := raw_ordinary_center hLc.1 hordinary ho
    obtain ⟨P,_,hi⟩ := h115
    obtain ⟨hcn,hfaith,ha⟩ := raw_ordinary_marked_actions hG T hLc.1 hout P hi hordinary
    exact Or.inl ⟨hordinary,hc,hc2,hcn,hfaith,ha⟩
  · exact Or.inr hconstrained

end CFSG.Quasithin.Chapter15.Section01
