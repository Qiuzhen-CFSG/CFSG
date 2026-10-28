module
public import CFSG.Quasithin.Chapter4.Section02.Unitary.CounterexampleC28
public import Theory.GroupTheory.PCoreCover

/-!
# The original intersection residual retains the component quotient

The actual covering equation for LH = (L ∩ H)∞ identifies LH/O₂(LH)
with L/O₂(L), by restriction of the original quotient map. The equality
of the two-residual and perfect residual is proved before using that map.

The odd-actor consumer retains the full C.2.8 configuration, relative
normality in H ∩ N(L), and the section-centralizer conjugation of the
chosen module. Thus its local model inspection can use the original
component quotient without assuming a second marking.

Source: Aschbacher–Smith 4.2.12–13 and 4.4.5–6, pp.610–612,620.
-/

public section
namespace CFSG.Quasithin.Chapter4.Section02.Unitary
open Subgroup Theory.GroupTheory
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

/-- The perfect intersection residual has the original component quotient,
through the literal restriction map, and is normal only in H ∩ N(L). -/
theorem source_intersection_quotient {κ : GroupClass} {T : Sylow 2 G}
    {L J H : Subgroup G} (h : Chapter12.Section02.Hypothesis1221 κ T L)
    (hM : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)))
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H) :
    let Y := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    (Y.subgroupOf (H ⊓ normalizer (L : Set G))).Normal ∧
    ∃ e : (Y ⧸ pCore 2 Y) ≃* (L ⧸ pCore 2 L),
      ∀ y : Y, e (QuotientGroup.mk' (pCore 2 Y) y) =
        QuotientGroup.mk' (pCore 2 L)
          ⟨y.val,((map_subtype_le _).trans inf_le_left) y.property⟩ := by
  have hyp := source_hypothesis411 h hM
  obtain ⟨hc,_,hn⟩ := residual_cover_of_containment hyp.plus_le hyp.plus_normal
    hyp.plus_perfect hcover hJH
  have he := Section04.chosen_intersection_twoResidual_eq_solvableResidual h hcover hJH
  rw [he] at hc hn
  exact ⟨hn,exists_pCoreQuotientEquiv_of_cover ((map_subtype_le _).trans inf_le_left) hc⟩

/-- Failure of odd-residual uniqueness gives the original C.2.8 datum
with its actual normal seed and the compatible original quotient. -/
theorem chosen_oddActorResidual_C28_quotient {κ : GroupClass} {T : Sylow 2 G}
    {L V : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 κ T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (B : Subgroup G) (hBN : B ≤ normalizer (L : Set G))
    (hcomm : ⁅B,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card B))
    (hBV : B ≤ centralizer (V : Set G))
    (hM : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)))
    (hnot : ¬ UniqueMaximalOvergroup (Section04.oddActorResidual L B)
      (normalizer (L : Set G))) :
    ∃ (J H : Subgroup G)
      (S : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L)),
      PushLE L (Section04.oddActorResidual L B) J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
      H ⊓ normalizer (L : Set G) < H ∧
      let Y := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      let W := fullModule L ((S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
        (sectionCentralizerIn (normalizer (L : Set G)) L).subtype)
      ChapterC.HypothesisC28 κ H (H ⊓ normalizer (L : Set G)) Y (J.pCoreIn 2) W ∧
      (Y.subgroupOf (H ⊓ normalizer (L : Set G))).Normal ∧
      (∃ e : (Y ⧸ pCore 2 Y) ≃* (L ⧸ pCore 2 L),
        ∀ y : Y, e (QuotientGroup.mk' (pCore 2 Y) y) =
          QuotientGroup.mk' (pCore 2 L)
            ⟨y.val,((map_subtype_le _).trans inf_le_left) y.property⟩) ∧
      ∃ c : sectionCentralizerIn (normalizer (L : Set G)) L,
        ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj (c : G)).toMonoidHom =
          (S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
            (sectionCentralizerIn (normalizer (L : Set G)) L).subtype ∧
        V.map (MulAut.conj (c : G)).toMonoidHom ≤ W := by
  obtain ⟨hc,_,_,hne⟩ := Section04.chosen_oddActorResidual_cover h D B hBN hcomm hodd hBV
  have hi := ((Section04.oddActorResidual_le L B).trans inf_le_left).trans L.le_normalizer
  obtain ⟨J,H,S,hJ,hIJ,hH,hJH,_,hlt,_,hs,hmark⟩ :=
    exists_source_C28_of_not_unique h D hM hi hc.subset hne hnot
  obtain ⟨hn,he⟩ := source_intersection_quotient h hM hJ.1.1.2.2.1 hJH
  exact ⟨J,H,S,hIJ,hH,hJH,hlt,hs,hn,he,hmark⟩
end CFSG.Quasithin.Chapter4.Section02.Unitary
