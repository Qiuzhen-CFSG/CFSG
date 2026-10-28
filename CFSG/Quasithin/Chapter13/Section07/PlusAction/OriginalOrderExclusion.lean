module
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalCubicContainment
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalThompsonModels
/-!
# Cubic order of the original Thompson-contained actor

Chief irreducibility puts K/O₂(K) inside the literal Thompson section
modulo O₂(KR₁). In the one-factor case this section is S₃, so its
order cannot be nine. This rules out the sole remaining rank-two chief
cardinality.

Source: Aschbacher--Smith 13.7.4(1), printed p.937.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₃ M H : Subgroup G}
theorem source_primitive_order_three_of_thompson_s3
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (J : Subgroup H)
    (hJC : J.map H.subtype ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hJn : H ≤ normalizer (J.map H.subtype : Set G))
    (hchief : ChiefFactor.IsChief (J.map (QuotientGroup.mk' (pCore 2 H))) ⊥)
    (hE : IsElementaryAbelian 3 (J ⧸ pCore 2 J))
    (hcard : Nat.card (J ⧸ pCore 2 J) = 3 ∨ Nat.card (J ⧸ pCore 2 J) = 9)
    (hout : ¬ J.map H.subtype ≤ M)
    (hB : normalizer (ChapterB.baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M)
    (emodel : let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
      let X := J.map H.subtype ⊔ (F.L₁ ⊔ (T : Subgroup G)).pCoreIn 2
      let W := (elementaryAbelianMaxJ (⊤ : Subgroup X)).map (QuotientGroup.mk' (pCore 2 X))
      Nonempty (W ≃* Equiv.Perm (Fin 3))) :
    Nat.card (J ⧸ pCore 2 J) = 3 := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let K := J.map H.subtype
  let R := (F.L₁ ⊔ (T : Subgroup G)).pCoreIn 2
  let X := K ⊔ R
  let W := elementaryAbelianMaxJ (⊤ : Subgroup X)
  let q := QuotientGroup.mk' (pCore 2 X)
  let KX := K.subgroupOf X
  have hXH : X ≤ H := sup_le (hJC.trans (kernel_le_H (D := F)))
    ((pCoreIn_le 2 _).trans h.local_le)
  let : KX.Normal := normal_subgroupOf_of_le_normalizer (hXH.trans hJn)
  let eK : KX ≃* J := (subgroupOfEquivOfLe (show K ≤ X from le_sup_left)).trans
    (J.equivMapOfInjective H.subtype H.subtype_injective).symm
  let eQ := (QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)).symm.trans
    ((Normal.isSubnormal (inferInstance : KX.Normal)).quotientCoreImageEquiv 2)
  have hcardK : Nat.card (KX.map q) = Nat.card (J ⧸ pCore 2 J) := by
    exact (Nat.card_congr eQ.toEquiv).symm
  have hle : KX.map q ≤ W.map q :=
    source_primitive_three_chief_image_le_thompson h hU J hJC hJn hchief hE hcard hout hB
  rcases hcard with h3 | h9
  · exact h3
  · rcases emodel with ⟨em⟩
    have hd : (9:ℕ) ∣ 6 := by
      have hk : Nat.card (KX.map q) ∣ Nat.card (W.map q) := card_dvd_of_le hle
      rw [hcardK, h9, Nat.card_congr em.toEquiv] at hk
      norm_num [Fintype.card_perm] at hk
    norm_num at hd
end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
