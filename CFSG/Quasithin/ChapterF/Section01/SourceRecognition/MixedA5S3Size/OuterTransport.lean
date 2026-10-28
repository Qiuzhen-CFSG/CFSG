module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.ReducedBorel

/-!
# Literal outer transport for the mixed reduced pair

Put R = O₂(B), where B is the full original common Borel, and let Pᵢ₀
be the parabolics obtained by replacing S with R. The local Sylow
normalizer formulas give Pᵢ₀ ∩ B = B₀, and Sylow maximality gives
S ∩ Pᵢ₀ = R. Since Pᵢ = Pᵢ₀ B, both endpoint extension indices equal
[B:B₀] = [S:R]. Thus the already proved bound [B:B₀] ≤ 2 applies to
the literal original Sylow and to both endpoint inclusions.

The reduced generated group M is normal in the original generated group W,
with W = MB and [W:M] dividing [B:B₀]. This does not identify M ∩ B
with B₀ or assert that R is Sylow in M. The source local analysis uses
R as the Sylow of each reduced parabolic; no global Sylow upgrade is needed.

Source: Delgado–Goldschmidt–Stellmacher, *Groups and Graphs: New Results and
Methods*, Part II, (15.1), printed p.226. The mixed size assembly still
requires the exhaustive branch restriction and the numerical core bounds
from (10.9), pp.162–163, and (11.7), pp.174–175. Their shared source
producers and the final specialized assembly retain those obligations.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source
variable {G : Type*} [Group G] [Finite G]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}

omit [Finite G] in
private theorem core_normalizes (A : Subgroup G) :
    A ≤ normalizer (twoCore A : Set G) :=
  A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 A))

omit [Finite G] in
private theorem core_le_S (h : HypothesisF11 L S) :
    twoCore (commonBorel L S) ≤ S := by
  obtain ⟨T,hT⟩ := h.sylow_commonBorel
  exact (pCoreIn_le_sylow _ T).trans_eq hT

omit [Finite G] in
private theorem core_localSylow (h : HypothesisF11 L S) (i : Fin 2) :
    twoCore (commonBorel L S) ⊓ L i = S ⊓ L i := by
  apply le_antisymm (inf_le_inf_right _ (core_le_S h))
  exact le_inf (le_pCoreIn_of_normalizes (h.S_isP.to_le inf_le_left)
    (inf_le_left.trans le_sup_right) (h.commonBorel_normalizes_localSylow i)) inf_le_right

omit [Finite G] in
private theorem core_localBorel (h : HypothesisF11 L S) (i : Fin 2) :
    borel (L i) (twoCore (commonBorel L S)) = borel (L i) S := by
  unfold borel
  rw [core_localSylow h]

omit [Finite G] in
private theorem core_parabolic_le (h : HypothesisF11 L S) (i : Fin 2) :
    parabolic L (twoCore (commonBorel L S)) i ≤ parabolic L S i := by
  unfold parabolic
  rw [core_localBorel h]
  exact sup_le_sup (sup_le_sup_left (core_le_S h) _) le_rfl

/-- Intersecting either reduced parabolic with the original Borel gives the reduced overlap. -/
theorem HypothesisF11.borel_core_parabolic_inf_commonBorel (h : HypothesisF11 L S)
    (i : Fin 2) :
    parabolic L (twoCore (commonBorel L S)) i ⊓ commonBorel L S =
      commonBorel L (twoCore (commonBorel L S)) := by
  have hnew := h.restrict_to_borel_core.commonBorel_eq_normalizer i
  rw [core_localSylow h i] at hnew
  rw [hnew]
  conv_lhs => arg 2; rw [h.commonBorel_eq_normalizer i]
  rw [← inf_assoc, inf_eq_left.mpr (core_parabolic_le h i)]

omit [Finite G] in
/-- Either reduced endpoint, together with the original overlap, recovers the original endpoint. -/
theorem HypothesisF11.borel_core_parabolic_sup_commonBorel (h : HypothesisF11 L S)
    (i : Fin 2) :
    parabolic L (twoCore (commonBorel L S)) i ⊔ commonBorel L S = parabolic L S i := by
  apply le_antisymm (sup_le (core_parabolic_le h i) (commonBorel_le_parabolic i))
  rw [parabolic_eq_sup_commonBorel]
  exact sup_le ((le_sup_left.trans le_sup_left).trans le_sup_left) le_sup_right

omit [Finite G] in
/-- DGS (15.1)(b) for the literal reduced completion. -/
theorem HypothesisF11.borel_core_generated_normalizes (h : HypothesisF11 L S) :
    generated L S ≤ normalizer (generated L (twoCore (commonBorel L S)) : Set G) := by
  let M := generated L (twoCore (commonBorel L S))
  have hSN : S ≤ normalizer (M : Set G) := by
    apply (le_inf ?_ ?_).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact (le_inf (h.S_normalizes 0) (h.S_normalizes 1)).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact (le_sup_right : S ≤ commonBorel L S).trans (core_normalizes _)
  exact sup_le (le_sup_left.trans M.le_normalizer) hSN

omit [Finite G] in
/-- The original Borel supplements the literal reduced completion. -/
theorem HypothesisF11.borel_core_generated_sup_commonBorel (h : HypothesisF11 L S) :
    generated L (twoCore (commonBorel L S)) ⊔ commonBorel L S = generated L S := by
  apply le_antisymm
  · apply sup_le (sup_le_sup_left (core_le_S h) _)
    exact sup_le (sup_le ((borel_le _ _).trans (le_sup_left.trans le_sup_left))
      ((borel_le _ _).trans (le_sup_right.trans le_sup_left))) le_sup_right
  · exact sup_le (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_right)

omit [Finite G] in
private theorem index_sup_normalizes (A B : Subgroup G)
    (hn : B ≤ normalizer (A : Set G)) : A.relIndex (A ⊔ B) = A.relIndex B := by
  let P := A ⊔ B
  let X := A.subgroupOf P
  let Y := B.subgroupOf P
  let : X.Normal := normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hn)
  have he := relIndex_sup_left Y X
  have hsup : X ⊔ Y = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right]
    exact subgroupOf_self P
  rw [hsup, relIndex_top_right] at he
  have hm := relIndex_map_map_of_injective X Y P.subtype_injective
  rw [map_subgroupOf_eq_of_le le_sup_left, map_subgroupOf_eq_of_le le_sup_right] at hm
  exact (hm.trans he.symm).symm

/-- The original Sylow meets each reduced endpoint in precisely the full Borel core. -/
theorem HypothesisF11.borel_core_parabolic_inf_S (h : HypothesisF11 L S)
    (i : Fin 2) :
    S ⊓ parabolic L (twoCore (commonBorel L S)) i = twoCore (commonBorel L S) := by
  let R := twoCore (commonBorel L S)
  let P := parabolic L R i
  obtain ⟨T,hT⟩ := h.restrict_to_borel_core.sylow_parabolic i
  have ht : (T : Subgroup P) = R.subgroupOf P := by
    apply map_injective P.subtype_injective
    rw [map_subgroupOf_eq_of_le (show R ≤ P from le_sup_right.trans le_sup_left)]
    exact hT
  have hle : (T : Subgroup P) ≤ S.subgroupOf P := by
    rw [ht]
    exact comap_mono (core_le_S h)
  have he := T.is_maximal' h.S_isP.comap_subtype hle
  have hm := congrArg (fun X : Subgroup P => X.map P.subtype) he
  change (S.subgroupOf P).map P.subtype = (T : Subgroup P).map P.subtype at hm
  rw [subgroupOf_map_subtype] at hm
  exact hm.trans hT

/-- The original Sylow meets the reduced overlap in precisely the full Borel core. -/
theorem HypothesisF11.borel_core_commonBorel_inf_S (h : HypothesisF11 L S) :
    S ⊓ commonBorel L (twoCore (commonBorel L S)) = twoCore (commonBorel L S) := by
  apply le_antisymm
  · exact (inf_le_inf_left S (commonBorel_le_parabolic 0)).trans_eq
      (h.borel_core_parabolic_inf_S 0)
  · exact le_inf (core_le_S h) le_sup_right

/-- The outer factor in the full Borel is exactly the original Sylow extension factor. -/
theorem HypothesisF11.mixed_reduced_borel_index_eq_sylow_index {K U : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    (mixedReducedBorel ![K,U] S).relIndex (commonBorel ![K,U] S) =
      (twoCore (commonBorel ![K,U] S)).relIndex S := by
  have hsup : mixedReducedBorel ![K,U] S ⊔ S = commonBorel ![K,U] S := by
    rw [h.mixedReducedBorel_eq eU, sup_assoc, sup_eq_right.mpr (core_le_S h)]
    exact (h.commonBorel_eq_of_cubic_second eU).symm
  calc
    _ = (mixedReducedBorel ![K,U] S).relIndex (mixedReducedBorel ![K,U] S ⊔ S) :=
      congrArg (fun X : Subgroup G => (mixedReducedBorel ![K,U] S).relIndex X) hsup.symm
    _ = (mixedReducedBorel ![K,U] S).relIndex S :=
      index_sup_normalizes _ _ ((le_sup_right : S ≤ commonBorel ![K,U] S).trans
        (h.mixedReducedBorel_normalizes eU))
    _ = _ := by
      rw [← inf_relIndex_left, ← h.mixed_reduced_commonBorel eU,
        h.borel_core_commonBorel_inf_S]

/-- The extension factor is identical at the whole overlap and at both endpoints. -/
theorem HypothesisF11.mixed_reduced_parabolic_index {K U : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) (i : Fin 2) :
    (parabolic ![K,U] (twoCore (commonBorel ![K,U] S)) i).relIndex
        (parabolic ![K,U] S i) =
      (mixedReducedBorel ![K,U] S).relIndex (commonBorel ![K,U] S) := by
  rw [← h.borel_core_parabolic_sup_commonBorel i]
  rw [index_sup_normalizes _ _ ((commonBorel_le_parabolic i).trans
    (h.borel_core_parabolic_normalizes i))]
  rw [← inf_relIndex_right,
    h.borel_core_parabolic_inf_commonBorel i, h.mixed_reduced_commonBorel eU]

/-- The index of the reduced completion divides the actual outer Borel index. -/
theorem HypothesisF11.mixed_reduced_generated_index_dvd {K U : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    (generated ![K,U] (twoCore (commonBorel ![K,U] S))).relIndex
        (generated ![K,U] S) ∣
      (mixedReducedBorel ![K,U] S).relIndex (commonBorel ![K,U] S) := by
  rw [← h.borel_core_generated_sup_commonBorel]
  rw [index_sup_normalizes _ _ (?_)]
  · apply relIndex_dvd_of_le_left
    rw [← h.mixed_reduced_commonBorel eU]
    exact sup_le (sup_le ((borel_le _ _).trans (le_sup_left.trans le_sup_left))
      ((borel_le _ _).trans (le_sup_right.trans le_sup_left))) le_sup_right
  · apply le_trans ?_ h.borel_core_generated_normalizes
    exact sup_le (sup_le ((borel_le _ _).trans (le_sup_left.trans le_sup_left))
      ((borel_le _ _).trans (le_sup_right.trans le_sup_left))) le_sup_right

/-- The entire completion also has outer index at most two. -/
theorem HypothesisF11.mixed_reduced_generated_index_le_two {K U : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    (generated ![K,U] (twoCore (commonBorel ![K,U] S))).relIndex
        (generated ![K,U] S) ≤ 2 :=
  (Nat.le_of_dvd (Nat.pos_of_ne_zero index_ne_zero_of_finite)
    (h.mixed_reduced_generated_index_dvd eU)).trans (h.mixedReducedBorel_index_le_two eK eU)

end CFSG.Quasithin.ChapterF.Source
