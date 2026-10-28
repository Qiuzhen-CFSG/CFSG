module
public import CFSG.Quasithin.Chapter14.Section02.PairedKOne
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# Large outside parabolics on the original ambient carrier

Apply the genuine minimal-parabolic entry to each H in H*(T,M).
Uniqueness identifies its original maximal subgroup with H intersection M.
The component model sieve supplies an actual escaping component and the
marked normal or exchanged cases. In the latter case the original
component quotient is binary PSL₂ or Suzuki and its Sylow normalizer has
index two. This is the original source entry to 14.2.8; the normal Bender
unitary row and the rank-two K₁ choice remain explicit model branches.
Source: Aschbacher--Smith 14.2.2(8), 14.2.7--8, printed pp.982--983.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

theorem source_outside_large_models
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hn : 1 < generationParameter H) :
    let S := T.subtype hH.1.1.2
    let N := (H ⊓ M).subgroupOf H
    ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      K ⊔ (S : Subgroup H) = ⊤ ∧ ¬K.map H.subtype ≤ M ∧
      ∃ f : ℕ, generationParameter H ≤ f ∧ 1 < f ∧
        ((K.Normal ∧ SingleClauses N K (S : Subgroup H) ∧
          (BenderModel N K f ∨ DiagramModel N K (S : Subgroup H) f)) ∨
         (¬K.Normal ∧ ExchangedClauses N K (S : Subgroup H) ∧
          ExchangedModel N K f ∧ (normalizer (K : Set H)).index = 2 ∧
          ((normalizer (K : Set H)).subgroupOf (S : Subgroup H)).index = 2 ∧
          (K.subgroupOf (K ⊔ ((S : Subgroup H) ⊓ normalizer (K : Set H)))).IsCComponent ∧
          ((2 ≤ f ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^f)) ∨
            ∃ m : ℕ, 1 ≤ m ∧ f = 2*m+1 ∧
              Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)))) := by
  dsimp only
  obtain ⟨_,hP,hN,hsq,_,_⟩ :=
    source_lemma_14_2_2_8_minimal hG T hempty hM hu hmany hcard e H hH
  have hmax : (H ⊓ M).subgroupOf H = ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hP :=
    ChapterB.minimalParabolicMax_unique _ hP hN (by
      intro x hx
      exact ⟨x.property,hM.1.2 hx⟩)
  obtain ⟨K,hK,hq,hgen,f,hf,hf1,hm⟩ := source_large_parabolic_models hsq _ hP hn
  refine ⟨K,hK,hq,hgen,?_,f,hf,hf1,?_⟩
  · intro hKM
    have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
    change K ⊔ (T.subtype hTH : Subgroup H) = ⊤ at hgen
    have hSyl : (T.subtype hTH : Subgroup H).map H.subtype = (T : Subgroup G) :=
      map_subgroupOf_eq_of_le hTH
    have hh := congrArg (Subgroup.map H.subtype) hgen
    rw [Subgroup.map_sup,hSyl,← MonoidHom.range_eq_map,range_subtype] at hh
    exact hH.1.2 (hh ▸ sup_le hKM hM.1.2)
  · rw [hmax]
    rcases hm with hm | ⟨hnot,hc,hmodel,hi,hSi⟩
    · exact Or.inl hm
    · exact Or.inr ⟨hnot,hc,hmodel,hi,hSi,hK.subgroupOf le_sup_left,
        paired_original_bender_quotient _ hP K hK hc hmodel⟩
end CFSG.Quasithin.Chapter14.Section02
