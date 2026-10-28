module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterBinaryPlanes
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.PairedBinaryOrthogonalAction

/-!
# The original positive-center action is the binary plus orthogonal action

The two original moved binary planes give coordinates on the original
commutator module. The original centralizer quotient is identified with the
full isometry group, here expressed as its literal wreath actor. Equivariance
and both plane markings are retained for the point-stabilizer construction.

Source: Aschbacher–Smith, 10.2.1, printed p.743, using G.6.4.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

@[expose] def SourceFixedCenterOrthogonalAction
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
                Module.finrank (ZMod 2) S.toSubmodule = 4) ∧
               ∃ (c : S.toSubmodule ≃ₗ[ZMod 2] BinaryFourPlus.V)
                 (ew : (H ⧸ centralizer (W.subgroupOf H : Set H)) ≃* BinaryFourPlus.Wreath),
                 (∀ x v, c (S.toRepresentation x v) =
                   (BinaryFourPlus.wreathToIsometry (ew x)).val (c v)) ∧
                 (∀ v, (c v).2 = 0 ↔ v ∈ subspaceCommutator S.toRepresentation ⊤ d.first) ∧
                 (∀ v, (c v).1 = 0 ↔ v ∈ subspaceCommutator S.toRepresentation ⊤ d.second))

/-- The original source action has literal orthogonal coordinates and marked planes. -/
theorem source_exists_fixed_center_orthogonal_action
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hne : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
    SourceFixedCenterOrthogonalAction D := by
  obtain ⟨H,hH,hHN,hWE,hred,g,hg,hresq,S,hS,hSM,hSA,hG6,hr,hclass,
    hP,hC,hM,hthree,hnot,d,hbinary⟩ :=
    source_exists_fixed_center_binary_plane_action D e hn hne hout
  let := hred.normal
  let := hred.elementary
  obtain ⟨c,ew,hw,hA,hB⟩ :=
    d.exists_paired_binary_wreath_action hbinary.1 hbinary.2.1 hG6.faithful
  exact ⟨H,hH,hHN,hWE,hred,g,hg,hresq,S,hS,hSM,hSA,hG6,hr,hclass,
    hP,hC,hM,hthree,hnot,d,hbinary,c,ew,hw,hA,hB⟩

end CFSG.Quasithin.Chapter10
