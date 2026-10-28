module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterComparedAction
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.PairedFiveThreeFree

/-!
# The original positive-center action has two binary planes

The original H-star quotient is minimal parabolic, and its prescribed maximal
subgroup has order prime to three. The literal wreath recognition excludes
the paired natural-five alternative. The same original commutator module,
centralizer quotient and selected transvection therefore have the paired
binary-plane model of total dimension four.

Source: Aschbacher–Smith, 10.2.1, printed p.743, using G.6.4.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

@[expose] def SourceFixedCenterBinaryPlaneAction
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) : Prop :=
  ∃ H : Subgroup G, ∃ hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal,
    H ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ∧
    (let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
     W ≤ omegaOneCenterAmbient (ChapterB.baumann (T : Subgroup G)) ∧
     ∃ hred : IsPReduced 2 (W.subgroupOf H),
       letI := hred.normal
       letI := hred.elementary
       let q := QuotientGroup.mk' (centralizer (W.subgroupOf H : Set H))
       let ρ := centralizerQuotient (W.subgroupOf H)
       ∃ g : H, (g:G)∈(T : Subgroup G) ⊓ localOrbit T L ∧
         pResidual 2 (H ⧸ centralizer (W.subgroupOf H : Set H)) ≤ normalClosure ({q g} : Set _) ∧
         ∃ S : Subrepresentation ρ,
           S.toSubmodule = conjugateDisplacementSpan ρ (q g) ⊤ ∧
           S.toSubmodule = AddSubgroup.toZModSubmodule 2
             (((⁅W,H⁆ : Subgroup G).subgroupOf H).subgroupOf (W.subgroupOf H)).toAddSubgroup ∧
           S.toSubmodule.toAddSubgroup.toSubgroup'.map
             (H.subtype.comp (W.subgroupOf H).subtype) = ⁅W,H⁆ ∧
           ChapterG.Section06.Hypotheses KnownSimple.IsKnownSimple S.toRepresentation (q g) q ∧
           Module.finrank (ZMod 2) (LinearMap.range (S.toRepresentation (q g)-(LinearMap.id : S.toSubmodule →ₗ[ZMod 2] S.toSubmodule)))=1 ∧
           ChapterG.Section06.Conclusion S.toRepresentation (q g) ∧
           ∃ hP : ChapterB.IsMinimalParabolicOver ((T.subtype hH.1.1.2).mapSurjective
               (QuotientGroup.mk'_surjective (centralizer (W.subgroupOf H : Set H)))) ⊤,
             centralizer (W.subgroupOf H : Set H) ≤ D.maximalLocal.subgroupOf H ∧
             ChapterB.minimalParabolicMax _ hP = (D.maximalLocal.subgroupOf H).map q ∧
             Nat.Coprime 3 (Nat.card (ChapterB.minimalParabolicMax _ hP)) ∧
             ¬ ChapterG.Section06.HasModelOn S.toRepresentation ⊤ ⊤
               (ChapterG.Section06.binaryLinearAction 2) ∧
             ∃ d : ChapterG.Section06.TwoFactors S.toRepresentation (q g),
               (ChapterG.Section06.HasModelOn S.toRepresentation d.first
                   (subspaceCommutator S.toRepresentation ⊤ d.first) (ChapterG.Section06.binaryLinearAction 2) ∧
                ChapterG.Section06.HasModelOn S.toRepresentation d.second
                   (subspaceCommutator S.toRepresentation ⊤ d.second) (ChapterG.Section06.binaryLinearAction 2) ∧
                Module.finrank (ZMod 2) S.toSubmodule = 4))

/-- The actual source module and its quotient action have paired binary-plane models. -/
theorem source_exists_fixed_center_binary_plane_action
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hne : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
    SourceFixedCenterBinaryPlaneAction D := by
  obtain ⟨H,hH,hHN,hWE,hred,g,hg,hresq,S,hS,hSM,hSA,hG6,hr,hclass,
    hP,hC,hM,hthree,hnot,d,hmodels⟩ :=
    source_exists_fixed_center_compared_action D e hn hne hout
  let := hred.normal
  let := hred.elementary
  have hbinary := hmodels.resolve_right (fun hh =>
    d.not_paired_five_of_three_free_maximal hG6.faithful _ hP hthree hh.1 hh.2)
  exact ⟨H,hH,hHN,hWE,hred,g,hg,hresq,S,hS,hSM,hSA,hG6,hr,hclass,
    hP,hC,hM,hthree,hnot,d,hbinary⟩

end CFSG.Quasithin.Chapter10
