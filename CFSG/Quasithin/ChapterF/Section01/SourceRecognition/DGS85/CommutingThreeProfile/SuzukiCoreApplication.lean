module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCoreDichotomy
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCoreQuotient
/-!
# The exact central quotient in the original parabolic

Apply the full-stabilizer normality and Suzuki alternative to the original
completion inclusion. The image product is normal in the reduced full
endpoint P₀. It is either the entire original parabolic two-core, or the
literal image of V_x (Q_m ∩ Q_y) with index q in that core.

The previous central quotient is retained with its actual normal-subgroup
witness and quotient map. Its order is exactly one or q, sharpening the
order-dividing-q bound. The order-q alternative still needs exclusion by
the source geometry; no full middle-core product or TYPE recognition is
claimed. Original and starred markings and the earlier common Sylows are
those in the input, with no replacement of the full edge or original S.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.1), (12.3), printed pp.178--180.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction
open BenderSuzuki.MatrixGroups BenderSuzuki.Converse
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The original core alternative and the literal central quotient of exact order one or q. -/
theorem source_suzuki_middle_core_exact_quotient
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {a x : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hxm : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) (!i)))
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL2 k)
    (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (T U : Sylow 2 (star L S (!i)))
    (hT : (T : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hU : (U : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i))) :
    let F := reducedFamily L S
    let A := star L S (!i)
    let m := base F (!i)
    let y := base F i
    let N := (Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m)
    ((N.map (G₀ L S).subtype).subgroupOf (P₀ L S (if !i then 1 else 0))).Normal ∧
    (N.map (G₀ L S).subtype = (parabolic L S (if !i then 1 else 0)).pCoreIn 2 ∨
      N.map (G₀ L S).subtype = (V F x 1).map (G₀ L S).subtype ⊔
        (Q F m ⊓ Q F y).map (G₀ L S).subtype ∧
      (N.map (G₀ L S).subtype).relIndex
        ((parabolic L S (if !i then 1 else 0)).pCoreIn 2) = 2 ^ (2 * n + 1)) ∧
    ∃ hN : (N.subgroupOf A).Normal,
      let : (N.subgroupOf A).Normal := hN
      ((Q F m).subgroupOf A).map (QuotientGroup.mk' (N.subgroupOf A)) ≤
        center (A ⧸ N.subgroupOf A) ∧
      (Nat.card (((Q F m).subgroupOf A).map (QuotientGroup.mk' (N.subgroupOf A))) = 1 ∨
        Nat.card (((Q F m).subgroupOf A).map (QuotientGroup.mk' (N.subgroupOf A))) =
          2 ^ (2 * n + 1)) := by
  let F := reducedFamily L S
  let A := star L S (!i)
  let m := base F (!i)
  let y := base F i
  let N := (Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m)
  obtain ⟨hfull,hd⟩ := source_suzuki_middle_core_product_or_seed h i hb hc hxa hxm hn eSuz eLin R hR T U hT hU
  have hcore : (Q F m).map (G₀ L S).subtype =
      (parabolic L S (if !i then 1 else 0)).pCoreIn 2 := by
    rw [← star_core h (!i), ← Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective
      2 _ (G₀ L S).subtype_injective]
    change (((starredParabolic L S (if !i then 1 else 0)).subgroupOf (G₀ L S)).map
      (G₀ L S).subtype).pCoreIn 2 = _
    rw [map_subgroupOf_eq_of_le (star_le_completion _)]
    exact h.starredParabolic_same_core _
  have hnmap := (map_mono (f := (G₀ L S).subtype) hfull).trans
    (N.le_normalizer_map (G₀ L S).subtype)
  have hstab : (stabilizer F m).map (G₀ L S).subtype = P₀ L S (if !i then 1 else 0) := by
    rw [stabilizer, Subgroup.CosetGeometry.stabilizer_base]
    cases i
    · change ((P₀ L S 1).subgroupOf (G₀ L S)).map (G₀ L S).subtype = P₀ L S 1
      exact map_subgroupOf_eq_of_le (show P₀ L S 1 ≤ G₀ L S from le_sup_right)
    · change ((P₀ L S 0).subgroupOf (G₀ L S)).map (G₀ L S).subtype = P₀ L S 0
      exact map_subgroupOf_eq_of_le (show P₀ L S 0 ≤ G₀ L S from le_sup_left)
  rw [hstab] at hnmap
  refine ⟨normal_subgroupOf_of_le_normalizer hnmap, ?_, ?_⟩
  · rcases hd with he | ⟨he,hi⟩
    · exact Or.inl ((congrArg (Subgroup.map (G₀ L S).subtype) he).trans hcore)
    · refine Or.inr ⟨?_, ?_⟩
      · have hh := congrArg (Subgroup.map (G₀ L S).subtype) he
        simpa only [Subgroup.map_sup] using hh
      · rw [← hcore, relIndex_map_map_of_injective _ _ (G₀ L S).subtype_injective]
        exact hi
  obtain ⟨_,_,hN,hcentral,_⟩ := source_suzuki_middle_core_central_quotient h i hb hc hxa hxm
    hn eSuz eLin R hR T U hT hU
  refine ⟨hN,hcentral,?_⟩
  let : (N.subgroupOf A).Normal := hN
  have hQA : Q F m ≤ A := by
    rw [← star_core h (!i)]
    exact map_subtype_le _
  have hcard : Nat.card (((Q F m).subgroupOf A).map
      (QuotientGroup.mk' (N.subgroupOf A))) = N.relIndex (Q F m) := by
    rw [← relIndex_ker, QuotientGroup.ker_mk', relIndex_subgroupOf hQA]
  rw [hcard]
  rcases hd with he | ⟨_,hi⟩
  · left
    change N = Q F m at he
    rw [he]
    exact Subgroup.relIndex_self (Q F m)
  · exact Or.inr hi
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
