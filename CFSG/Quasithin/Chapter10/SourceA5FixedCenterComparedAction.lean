module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterMovedAction
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterQuotientParabolic
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterNonabelian
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.ThreeFreeMaximal
/-!
# The original fixed-center action has paired binary-plane or five-letter models

The same HStar group, original commutator module [W,H], and literal
H/C_H(W) quotient now retain their complete G.6.4 action classification and
minimal-parabolic structure. The original paired geometry makes the Sylow
image nonabelian and excludes the single binary plane. The original cubic
residual calculation makes the maximal quotient subgroup three-free, which
excludes the single five-letter model. Thus the remaining actual marked
models are paired binary planes of total dimension four or paired S₅ modules.
The final paired-five exclusion remains a separate transport step.
Source: Aschbacher--Smith, 10.2.1, printed p.743.
-/
public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private theorem not_binary_plane_model_of_large_two_subgroup
    {X V : Type*} [Group X] [Finite X] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) X V)
    (A : Subgroup X) (hA : IsPGroup 2 A) (hcard : 2 < Nat.card A) :
    ¬ ChapterG.Section06.HasModelOn ρ ⊤ ⊤ (ChapterG.Section06.binaryLinearAction 2) := by
  rintro ⟨e,_,_⟩
  have hG : Nat.card X = 6 := by
    have hh := Nat.card_congr ((topEquiv (G := X)).symm.trans
      (e.trans BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree)).toEquiv
    simpa [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] using hh
  have hd : Nat.card A ∣ 6 := hG ▸ card_subgroup_dvd_card A
  obtain ⟨n,hn⟩ := hA.exists_card_eq
  have hpow : 2^n ∣ 6 := hn ▸ hd
  have hnle : n ≤ 1 := by
    by_contra hh
    have hfour : 4 ∣ 6 := (pow_dvd_pow 2 (show 2 ≤ n by omega)).trans hpow
    norm_num at hfour
  rw [hn] at hcard
  interval_cases n <;> norm_num at hcard

@[expose] def SourceFixedCenterComparedAction
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
                Module.finrank (ZMod 2) S.toSubmodule = 4) ∨
               (ChapterG.Section06.HasModelOn S.toRepresentation d.first
                   (subspaceCommutator S.toRepresentation ⊤ d.first)
                   (BinaryPermutation.naturalRepresentation (Fin 5)) ∧
                ChapterG.Section06.HasModelOn S.toRepresentation d.second
                   (subspaceCommutator S.toRepresentation ⊤ d.second)
                   (BinaryPermutation.naturalRepresentation (Fin 5))))

theorem source_exists_fixed_center_compared_action
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hne : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
    SourceFixedCenterComparedAction D := by
  obtain ⟨H,hH,hHN,hWE,hred,g,hg,hresq,S,hS,hSM,hSA,hG6,hr,hclass⟩ :=
    source_exists_fixed_center_classified_moved_action D e hn hne hout
  let := hred.normal
  let := hred.elementary
  have hgC : g ∉ centralizer
      ((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H : Set H) :=
    fun hh => hG6.nonidentity ((QuotientGroup.eq_one_iff g).mpr hh)
  obtain ⟨hP,hC,hM⟩ := source_a5_HStar_reduced_quotient_parabolic D e hn hH _ hred g hgC
  let q := QuotientGroup.mk' (centralizer
    ((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H : Set H))
  have hthree : Nat.Coprime 3 (Nat.card (ChapterB.minimalParabolicMax _ hP)) := by
    rw [hM]
    exact source_a5_HStar_maximal_image_three_free D e hn hout hHN q
  have htwo := source_a5_fixed_center_sylow_image_card_gt_two D e hn hne hout H hH hWE hred
  have hnot := not_binary_plane_model_of_large_two_subgroup S.toRepresentation _
    ((T.subtype hH.1.1.2).isPGroup'.map q) htwo
  have hmodels := hG6.minimal_parabolic_models hclass _ hP
  have hpairs := (hmodels.resolve_left hnot).resolve_left
    (ChapterG.Section06.not_symmetricFive_model_of_three_free_maximal _ hP hthree ⊤)
  exact ⟨H,hH,hHN,hWE,hred,g,hg,hresq,S,hS,hSM,hSA,hG6,hr,hclass,hP,hC,hM,hthree,hnot,hpairs⟩
end CFSG.Quasithin.Chapter10
