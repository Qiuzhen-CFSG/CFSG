module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianSmallLinearSieve
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianSpecialLinearFourScalar
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianSpecialLinearFourQuotient
/-!
# Borel structure on the same original reduced catalogue

The existing selected component K and reduced actor J are retained.
In the SL₃(4) branch, the original L₁ lies in K, J=KT, and its full
Borel image has the prescribed component Sylow and edge-core containment.
Both quotient carriers and all exchanged PSL₂(4) markings remain present.

Source: Aschbacher–Smith 12.6.31, printed pp.836–837. The SL₃(4) module
exclusion, wreath and terminal branches, and universal NaturalReduction
remain unfinished.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)


include hz hTz hTV hbound hTI hns hH in
/-- The same reduced component carries its full special-linear Borel
and original edge-core containment. All exchanged-row witnesses are preserved. -/
theorem SourceHypothesis.original_abelian_reduced_smallLinear_structure :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧ ¬ K ≤ M L ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧
      (D.fullSetup hZ T z).L₁ ≤ normalizer (K : Set G) ∧
      let K₀ := conjugateSpanBy K (T : Subgroup G)
      let J := K₀ ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)
      (K₀.subgroupOf H).Normal ∧ J ≤ H ∧ J ∈ (D.fullSetup hZ T z).Hz ∧
      (K.subgroupOf J).IsCComponent ∧
      (((K.subgroupOf J).Normal ∧
          AbelianNormalSmallLinearModels (K ⧸ pCore 2 K)
            (Chapter13.Section08.Source.starImage J K) ∧
          (Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 4 →
            (D.fullSetup hZ T z).L₁ ≤ K ∧ K ⊔ (T : Subgroup G) = J ∧
            (T : Subgroup G) ⊓ K ≤ (D.fullSetup hZ T z).R₁ ∧
            ∃ P : Sylow 2 (actorImage J K),
              (P : Subgroup (actorImage J K)).map (actorImage J K).subtype =
                actorImage J ((T : Subgroup G) ⊓ K) ∧
              (normalizer (P : Set (actorImage J K))).map (actorImage J K).subtype =
                actorImage J (D.fullSetup hZ T z).L₁)) ∨
        (¬ (K.subgroupOf J).Normal ∧ (normalizer (K.subgroupOf J : Set J)).index = 2 ∧
          ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4 ∧
          ClassicalGroup.IsPSL (Chapter13.Section08.Source.starImage J K) 2 4 ∧
          (primeToResidual 3 J).map J.subtype = K₀ ∧
          (D.fullSetup hZ T z).L₁ ≤ K₀ ⊓ M L ∧
          K₀ ⊔ (T : Subgroup G) = J ∧
          J ⊓ M L = (K₀ ⊓ M L) ⊔ (T : Subgroup G) ∧
          Group.IsSolvable (K₀ ⊓ M L : Subgroup G) ∧
          primeRank 3 (K₀ ⊓ M L : Subgroup G) = 2 ∧
          (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G) ≤
            normalizer ((K₀ ⊓ M L : Subgroup G) : Set G) ∧
          (T : Subgroup G) ⊓ K₀ ≤ (D.fullSetup hZ T z).R₁ ∧
          ExchangedTorusAction J K (D.fullSetup hZ T z).L₁ T L (M L) 2 (by decide))) := by
  obtain ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,hKJ,halt⟩ :=
    S.original_abelian_reduced_smallLinear_models D hZ z hz hTz hTV hbound hTI hns hH
  refine ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,hKJ,?_⟩
  rcases halt with ⟨hn,hmodel⟩ | hexchanged
  · have hKle := (le_conjugateSpanBy K (T : Subgroup G)).trans
      (le_sup_left.trans (le_sup_left :
        conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ≤
          conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)))
    refine Or.inl ⟨hn,hmodel,?_⟩
    intro hm
    obtain ⟨hLK,hgen⟩ := S.original_abelian_normal_specialLinearFour_reduction
      D hZ z hz hTV hTz hbound hTI hns hJ hKle rfl hn hm
    exact ⟨hLK,hgen,
      S.original_abelian_normal_specialLinearFour_sylow_le_edge_core
        D hZ z hz hTV hTz hbound hTI hns hJ hKle hKJ hn hm,
      S.original_abelian_normal_specialLinearFour_borel_star
        D hZ z hz hTV hTz hbound hTI hns hJ hKle hKJ hn hm⟩
  · exact Or.inr hexchanged


end CFSG.Quasithin.Chapter12.Section06
