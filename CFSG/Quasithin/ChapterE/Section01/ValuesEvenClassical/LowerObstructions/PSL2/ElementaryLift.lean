module
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.Bounds
public import Theory.GroupTheory.RankOneSylowExtension.QuotientRank

/-!
# E-generation obstructed by an elementary lift of a rank-one Sylow subgroup

Let q be a surjection with a normal nonsolvable simple rank-one subgroup L
in its target. An actual elementary subgroup A upstairs mapping onto a
Sylow subgroup P of L gives a conjugation-invariant elementary family.
Inside a Sylow containing A, every family's image is the same P. Its weak
closure normalizer and all small-rank E-members therefore map into N(P).
The two literal E-member quotients preserve P's rank by solvability of
their kernels. This proves the lower bound in the original group, without
an assertion that E-generation descends through q.

The elementary lift is essential: a central cover can have no such lift.
Source: Aschbacher--Smith E.1.2--6 and E.1.14(1), pp.209--211,214;
application to the original nonsolvable branch of 13.2.8(1), p.880.
-/

public section
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical
open Subgroup Subgroup.RankOneSylowExtension
variable {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]

/-- A genuine elementary lift, rather than a quotient parameter, supplies
an obstruction in the original group. -/
theorem not_isEGenerated_of_rankOne_quotient_lift
    (q : G →* Q) (hq : Function.Surjective q)
    (L : Subgroup Q) [L.Normal] [IsSimpleGroup L]
    (hL : ¬ Group.IsSolvable L) (P : Sylow 2 L)
    (hproper : ∀ D : Subgroup L, (P : Subgroup L) ≤ D → D ≠ ⊤ →
      D ≤ normalizer (P : Set L))
    (hn : normalizer (P : Set L) ≠ ⊤)
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : A.map q = (P : Subgroup L).map L.subtype)
    (i : ℕ) (hi : i < Group.rank P) : ¬ IsEGenerated i G := by
  let B := (P : Subgroup L).map L.subtype
  change A.map q = B at hA
  have hBL : B ≤ L := map_subtype_le _
  obtain ⟨T,hAT⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  let S := T.mapSurjective hq
  have hBS : B ≤ (S : Subgroup Q) := hA ▸ map_mono hAT
  have hB : B = (S : Subgroup Q) ⊓ L := by
    have hPS := map_le_iff_le_comap.mp hBS
    have he := P.is_maximal' S.isPGroup'.comap_subtype hPS
    change (S : Subgroup Q).subgroupOf L = (P : Subgroup L) at he
    rw [← subgroupOf_map_subtype,he]
  let Ω : Set (Subgroup G) :=
    {D | IsElementaryAbelian 2 D ∧ D.map q ≤ L ∧ Nat.card (D.map q) = Nat.card B}
  have hΩ : IsElementaryFamily Ω := by
    refine ⟨fun D hD => hD.1,?_⟩
    intro g D hD
    let : IsElementaryAbelian 2 D := hD.1
    have he : (D.map (MulAut.conj g).toMonoidHom).map q =
        (D.map q).map (MulAut.conj (q g)).toMonoidHom := by
      rw [map_map,map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply]
    refine ⟨IsElementaryAbelian.map _,?_,?_⟩
    · rw [he]
      rintro _ ⟨x,hx,rfl⟩
      exact (inferInstance : L.Normal).conj_mem x (hD.2.1 hx) (q g)
    · rw [he,card_map_of_injective (MulAut.conj (q g)).injective]
      exact hD.2.2
  have huniq : ∀ D ∈ Ω, D ≤ (T : Subgroup G) → D.map q = B := by
    intro D hD hDT
    apply eq_of_le_of_card_ge
    · rw [hB]
      exact le_inf (map_mono hDT) hD.2.1
    · exact hD.2.2.ge
  have hw : (weakClosure (T : Subgroup G) Ω).map q = B := by
    apply le_antisymm
    · apply map_le_iff_le_comap.mpr
      apply sSup_le
      intro D hD
      exact map_le_iff_le_comap.mp (huniq D hD.1 hD.2).le
    · rw [← hA]
      exact map_mono (le_sSup ⟨⟨inferInstance,hA ▸ hBL,by rw [hA]⟩,hAT⟩)
  let M := (normalizer (B : Set Q)).comap q
  have hM : M ≠ ⊤ := by
    intro he
    have hnB : normalizer (B : Set Q) = ⊤ := by
      have hh := congrArg (map q) he
      rwa [map_comap_eq_self_of_surjective hq,map_top_of_surjective q hq] at hh
    apply hn
    have hh := congrArg (comap L.subtype) hnB
    rw [comap_normalizer_eq_of_le_range (by simpa using hBL),
      comap_map_eq_self_of_injective L.subtype_injective,comap_top] at hh
    exact hh
  apply not_isEGenerated_of_members_le T Ω hΩ M hM
  · apply map_le_iff_le_comap.mp
    exact (le_normalizer_map q).trans (by rw [hw])
  · intro D hD hDT K hK
    have hDq := huniq D hD hDT
    have hPK : B ≤ K.map q := hDq ▸ map_mono hK.1.2.2.1
    rcases le_or_le_normalizer L P hproper (K.map q) hPK with hLK | hKN
    · exfalso
      have hri : i < Group.rank (D.map q) := by
        rw [hDq]
        exact hi.trans_eq (Group.rank_congr
          ((P : Subgroup L).equivMapOfInjective L.subtype L.subtype_injective))
      rcases hK.2 with hodd | hcomp
      · let : Group.IsNilpotent (pCore 2 K) := pCore_isPGroup.isNilpotent
        exact (not_le_of_gt hri) ((rank_image_le_solvable_quotient_image q L hL
          D K hK.1.2.2.1 hD.2.1 hLK (pCore 2 K)).trans hodd.2)
      · exact (not_le_of_gt hri) ((rank_image_le_solvable_quotient_image q L hL
          D K hK.1.2.2.1 hD.2.1 hLK (solvableRadical K)).trans hcomp.2)
    · exact map_le_iff_le_comap.mp hKN
end CFSG.Quasithin.ChapterE.ValuesEvenClassical
