module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianSpecialLinearSieve
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianNormalLargeSpecialLinear
/-!
# The original reduced catalogue at field order four

Cubic rigidity on the full special-linear Borel excludes all even field
degrees at least four. The original normal rows are therefore PSL₂(4)
and SL₃(4). The same selected component and reduced subgroup are retained,
with both literal quotient carriers and every exchanged PSL₂(4) marking.

Source: Aschbacher--Smith 12.6.31, printed pp.836--837. The SL₃(4) module
exclusion, wreath/terminal arguments and universal NaturalReduction remain
obligations of the source assembly.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components

/-- The normal component carriers after the original field-size restriction. -/
inductive AbelianNormalSmallLinearModels (X Y : Type*) [Group X] [Group Y] : Prop
  | linear_two (left : ClassicalGroup.IsPSL X 2 4) (right : ClassicalGroup.IsPSL Y 2 4)
  | special_three (left : Chapter1.Section02.LocalModels.IsSL X 3 4)
      (right : Chapter1.Section02.LocalModels.IsSL Y 3 4)
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
    (T : Subgroup G) = H)


include hz hTz hTV hbound hTI hns hH hKH hK hgen in
/-- Both original quotient carriers have field order four. -/
theorem SourceHypothesis.original_abelian_normal_smallLinear_models
    (hn : (K.subgroupOf H).Normal) (hout : ¬ K ≤ M L) :
    AbelianNormalSmallLinearModels (K ⧸ pCore 2 K) (actorImage H K) := by
  have hm := S.original_abelian_normal_specialLinear_models D hZ z hz hTz hTV hbound hTI hns
    hH hKH hK hgen hn hout
  cases hm with
  | linear_two hl hr => exact .linear_two hl hr
  | special_three n hn2 heven hl hr =>
    have he := S.original_abelian_normal_specialLinear_degree_two D hZ z hz hTV hTz
      hbound hTI hns hH hKH hK hn hn2 heven hl
    subst n
    exact .special_three hl hr

include hz hTz hTV hbound hTI hns hH in
/-- Restrict the special-linear field to order four from the same original reduced actor,
preserving the complete exchanged-row markings and both quotient carriers. -/
theorem SourceHypothesis.original_abelian_reduced_smallLinear_models :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧ ¬ K ≤ M L ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧
      (D.fullSetup hZ T z).L₁ ≤ normalizer (K : Set G) ∧
      let K₀ := conjugateSpanBy K (T : Subgroup G)
      let J := K₀ ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)
      (K₀.subgroupOf H).Normal ∧ J ≤ H ∧ J ∈ (D.fullSetup hZ T z).Hz ∧
      (K.subgroupOf J).IsCComponent ∧
      (((K.subgroupOf J).Normal ∧
          AbelianNormalSmallLinearModels (K ⧸ pCore 2 K)
            (Chapter13.Section08.Source.starImage J K)) ∨
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
    S.original_abelian_reduced_specialLinear_models D hZ z hz hTz hTV hbound hTI hns hH
  refine ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,hKJ,?_⟩
  rcases halt with ⟨hn,_⟩ | hexchanged
  · have hKle := (le_conjugateSpanBy K (T : Subgroup G)).trans
      (le_sup_left.trans (le_sup_left :
        conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ≤
          conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)))
    exact Or.inl ⟨hn,S.original_abelian_normal_smallLinear_models D hZ z hz hTz hTV
      hbound hTI hns hJ hKle hKJ rfl hn hout⟩
  · exact Or.inr hexchanged
end CFSG.Quasithin.Chapter12.Section06
