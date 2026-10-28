module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianSuzukiCentralizer

/-!
# Suzuki section control on the original reduced actor

Construct the escaping abelian-branch C-component K and replace the given
H by J = K₀L₁T exactly as in the source. The original F.9 action then gives
the Suzuki module identifications and the normal centralizer fixing its
whole moved section. The same K, intrinsic quotient, ambient Sylow orbit,
point residual and quotient representation occur in every conclusion.

This discharges the module-recognition and centralizer-action steps of
the Suzuki paragraph. The centralizing actor's required seed movement,
the other 12.6.31 rows and the final natural reduction remain unproved.
Source: Aschbacher--Smith 12.6.30--31, printed pp.835--836.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components Chapter13.Section08.Components.SourceModels
open Chapter13.Section08.Components.Suzuki
open Chapter13.Section08.Components.Suzuki.NaturalSections
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged
open Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- Construct the escaping component and its faithful literal action, then
apply the Suzuki section and centralizer conclusions on K₀L₁T itself. -/
theorem SourceHypothesis.original_abelian_reduced_suzuki_control
    (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧ ¬ K ≤ M L ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧
      (D.fullSetup hZ T z).L₁ ≤ normalizer (K : Set G) ∧
      let K₀ := conjugateSpanBy K (T : Subgroup G)
      let J := K₀ ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)
      (K₀.subgroupOf H).Normal ∧ J ≤ H ∧ J ∈ (D.fullSetup hZ T z).Hz ∧
      ∃ hU : IsElementaryAbelian 2 ((D.fullSetup hZ T z).UH J),
        let _ := hU
        ∃ a : LocalQuotientAction J ((D.fullSetup hZ T z).UH J) (D.fullSetup hZ T z).V₁,
          ∀ m : ℕ, 0 < m →
            Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) →
            let Q₀ := actorImage J K₀
            let C := actorImage J (D.fullSetup hZ T z).L₁ ⊓
              centralizer (Q₀ : Set (J ⧸ pCore 2 J))
            let W := subspaceCommutator a.representation ⊤ Q₀
            C.Normal ∧ W ≤ fixedSpace a.representation C ∧
            (((K.subgroupOf J).Normal ∧
              Nonempty (ActionEquiv (centralQuotientRepresentation a.representation Q₀ W
                (subspaceCommutator_invariant a.representation ⊤ Q₀)) (natural m))) ∨
              (¬ (K.subgroupOf J).Normal ∧ (normalizer (K.subgroupOf J : Set J)).index = 2 ∧
              Nonempty (ActionEquiv (centralQuotientRepresentation a.representation Q₀ W
                (subspaceCommutator_invariant a.representation ⊤ Q₀)) (naturalPair m)))) := by
  obtain ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,hKJ⟩ :=
    S.original_abelian_quasisimple_reduced_actor_exists D hZ z hz hTV hTz hbound hTI hns hH
  have hKle := (le_conjugateSpanBy K (T : Subgroup G)).trans
    (le_sup_left.trans (le_sup_left :
      conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ≤
        conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)))
  refine ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,?_⟩
  obtain ⟨hU,a,_⟩ :=
    S.original_abelian_quadratic_actor D hZ z hz hTV hTz hbound hTI hns hJ
  let _ := hU
  refine ⟨hU,a,?_⟩
  rintro m hm ⟨eK⟩
  exact ⟨S.original_abelian_residual_centralizer_normal D hZ z hz hTV hJ hKle hKJ rfl,
    S.original_abelian_suzuki_centralizer_fixes_moved D hZ z hz hTV hTz hbound hTI hns
      hJ hKle hKJ rfl a hm eK,
    S.original_abelian_suzuki_sections D hZ z hz hTV hTz hbound hTI hns
      hJ hKle hKJ rfl a hm eK⟩

end CFSG.Quasithin.Chapter12.Section06
