module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Asymmetric.Track
public import Theory.GroupTheory.ElementaryThompsonComponent
open Subgroup Theory.GroupTheory Stellmacher
/-!
# Thompson escape from one local two-core

If the elementary Thompson subgroup of the common Sylow were contained in both
local two-cores, its elementary Thompson subgroup computed inside either core
would be the same subgroup. Core normalization then makes that subgroup normal
in both vertices, contradicting faithfulness of the global amalgam. Thus one
vertex has a genuine Thompson escape. This is the source-side escape used before
constructing a critical F.7 track.

Source: Aschbacher--Smith F.1.12 and Stellmacher's elementary Thompson
subgroup argument; the proof uses the literal common Sylow and the actual
core-normalization hypotheses.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Asymmetric
variable {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
omit [Finite G] in
private theorem normalizer_J (P : Subgroup G) :
    normalizer (P : Set G) ≤ normalizer (elementaryAbelianMaxJ P : Set G) := by
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq] at hx ⊢
  change P.map (MulAut.conj x).toMonoidHom = P at hx
  change (elementaryAbelianMaxJ P).map (MulAut.conj x).toMonoidHom = _
  rw [←elementaryAbelianMaxJ_map_equiv, hx]

theorem thompson_escapes_one_core
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A)
    (S : Sylow 2 G) (hS : A⊓B=(S : Subgroup G)) :
    (¬ elementaryAbelianMaxJ (S : Subgroup G)≤(pCore 2 A).map A.subtype) ∨
    (¬ elementaryAbelianMaxJ (S : Subgroup G)≤(pCore 2 B).map B.subtype) := by
  by_contra! hc
  let J := elementaryAbelianMaxJ (S : Subgroup G)
  have hJS : J≤(S : Subgroup G) := sSup_le fun _ h => h.1
  have hJA : elementaryAbelianMaxJ ((pCore 2 A).map A.subtype)=J :=
    elementaryAbelianMaxJ_eq_of_intermediate _ _ hc.1
      (h.local_twoCore_le_intersection.trans hS.le)
  have hJB : elementaryAbelianMaxJ ((pCore 2 B).map B.subtype)=J :=
    elementaryAbelianMaxJ_eq_of_intermediate _ _ hc.2
      (h.symm.local_twoCore_le_intersection.trans ((inf_comm B A).trans hS).le)
  have hnA : A≤normalizer (J : Set G) := by
    rw [←hJA]
    exact h.left_core_normalized.trans (normalizer_J _)
  have hnB : B≤normalizer (J : Set G) := by
    rw [←hJB]
    exact h.symm.left_core_normalized.trans (normalizer_J _)
  have hbot := h.common_normal_eq_bot hcore J (hJS.trans hS.symm.le)
    ((normal_subgroupOf_iff_le_normalizer (hJS.trans (hS.symm.le.trans inf_le_left))).mpr hnA)
    ((normal_subgroupOf_iff_le_normalizer (hJS.trans (hS.symm.le.trans inf_le_right))).mpr hnB)
  have hs : 1<Nat.card S := by
    have hh := BothAbelian.intersection_card_gt_four h hA
    rw [hS] at hh
    omega
  let : Nontrivial (S : Subgroup G) := (Finite.one_lt_card_iff_nontrivial).mp hs
  have he : (elementaryAbelianMaxJ (⊤ : Subgroup S)).map (S : Subgroup G).subtype=J := by
    rw [←elementaryAbelianMaxJ_map_injective _ (S : Subgroup G).subtype_injective,
      ←MonoidHom.range_eq_map, range_subtype]
  apply elementaryAbelianMaxJ_top_ne_bot_of_isPGroup S.isPGroup'
  exact (map_eq_bot_iff_of_injective _ (S : Subgroup G).subtype_injective).mp (he.trans hbot)
end CFSG.Quasithin.ChapterF.SourceAssembly.Asymmetric
