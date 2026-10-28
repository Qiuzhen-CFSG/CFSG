module
public import CFSG.Quasithin.ChapterE.Section01.Basic
public import Theory.GroupTheory.PrimeRankWitness

/-!
# Bounding E-member ranks modulo the ambient two-core

For an elementary abelian `A ≤ K ≤ G`, any local quotient killing
`O₂(G) ∩ K` has its image of `A` as a quotient of the image in `G/O₂(G)`.
The rank of that image is therefore bounded by `m₂(G/O₂(G))`. Both E-member
quotients kill `O₂(G) ∩ K`, since this is a normal 2-subgroup of `K`.
Consequently any existing E-generation bound can be reduced to this rank.
The structural E-member conditions, including the local-tau orbit in (E2),
are preserved verbatim.

This strengthens the rank bookkeeping in Aschbacher--Smith, E.1.5--E.1.7,
printed p.210. It does not establish existence of an E-generation bound for
an arbitrary even-order group. That independent generation theorem is still
required when applying the result to HS local subgroups. Odd-order groups
are handled directly: their Sylow 2-subgroup and weak closure are trivial.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE

private theorem rank_range_le_of_ker_le {X Y Z : Type*}
    [Group X] [Group Y] [Group Z] [Finite X]
    (f : X →* Y) (g : X →* Z) (hker : f.ker ≤ g.ker) :
    Group.rank g.range ≤ Group.rank f.range := by
  rw [← Group.rank_congr (QuotientGroup.quotientKerEquivRange g),
    ← Group.rank_congr (QuotientGroup.quotientKerEquivRange f)]
  exact Group.rank_le_of_surjective
    (QuotientGroup.map f.ker g.ker (MonoidHom.id X) hker)
    (QuotientGroup.map_surjective_of_surjective _ _ _ QuotientGroup.mk_surjective hker)

variable {G : Type*} [Group G] [Finite G]

private theorem rank_local_image_le (A K : Subgroup G)
    [IsElementaryAbelian 2 A] (hAK : A ≤ K)
    (N : Subgroup K) [N.Normal] (hN : (pCore 2 G).subgroupOf K ≤ N) :
    Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' N)) ≤
      primeRank 2 (G ⧸ pCore 2 G) := by
  let X := A.subgroupOf K
  let : IsElementaryAbelian 2 X := IsElementaryAbelian.subgroupOf hAK
  let f := ((QuotientGroup.mk' (pCore 2 G)).comp K.subtype).comp X.subtype
  let g := (QuotientGroup.mk' N).comp X.subtype
  have hker : f.ker ≤ g.ker := by
    intro x hx
    apply (QuotientGroup.eq_one_iff _).mpr
    change (QuotientGroup.mk' (pCore 2 G)) (x : G) = 1 at hx
    have hx' : (x : G) ∈ pCore 2 G := (QuotientGroup.eq_one_iff _).mp hx
    exact hN hx'
  have : IsMulCommutative f.range := inferInstance
  have hbound := f.range.rank_le_primeRank 2
    ((IsElementaryAbelian.isPGroup 2 X).of_surjective
      f.rangeRestrict f.rangeRestrict_surjective)
  have h := (rank_range_le_of_ker_le f g hker).trans hbound
  have he : g.range = (A.subgroupOf K).map (QuotientGroup.mk' N) := by
    simp only [g, MonoidHom.range_comp, range_subtype, X]
  exact (Group.rank_congr (MulEquiv.subgroupCongr he)).symm.le.trans h

omit [Finite G] in
private theorem ambient_core_le_local_core (K : Subgroup G) :
    (pCore 2 G).subgroupOf K ≤ pCore 2 K :=
  le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩

/-- Every E-member satisfies the ambient rank bound modulo the two-core. -/
theorem IsEMember.at_quotient_rank {T A K : Subgroup G}
    (h : IsEMember T A K) :
    IsEMemberAt (primeRank 2 (G ⧸ pCore 2 G)) T A K := by
  let : IsElementaryAbelian 2 A := h.1
  refine ⟨h, ?_⟩
  rcases h.2.2.2.2.2 with ho | hc
  · exact Or.inl ⟨ho, rank_local_image_le A K h.2.2.1 _
      (ambient_core_le_local_core K)⟩
  · have : Group.IsNilpotent (pCore 2 K) := pCore_isPGroup.isNilpotent
    have hn : pCore 2 K ≤ solvableRadical K :=
      le_solvableRadical _ inferInstance inferInstance
    exact Or.inr ⟨hc, rank_local_image_le A K h.2.2.1 _
      ((ambient_core_le_local_core K).trans hn)⟩

/-- Reduce any established generation bound to the rank modulo the two-core. -/
theorem isEGenerated_quotient_rank_of_isEGenerated {i : ℕ}
    (hgen : IsEGenerated i G) :
    IsEGenerated (primeRank 2 (G ⧸ pCore 2 G)) G := by
  intro T Ω hΩ
  apply top_unique
  rw [← hgen T Ω hΩ]
  apply sup_le_sup_right
  apply iSup_mono
  intro A
  apply sSup_le_sSup
  intro K hK
  exact hK.1.at_quotient_rank

/-- The existence premise is essential; this is only a rank-reduction lemma. -/
theorem isEGenerated_of_quotient_rank_le {n : ℕ}
    (hrank : primeRank 2 (G ⧸ pCore 2 G) ≤ n)
    (hex : ∃ i : ℕ, IsEGenerated i G) : IsEGenerated n G := by
  obtain ⟨i, hi⟩ := hex
  exact (isEGenerated_quotient_rank_of_isEGenerated hi).mono hrank

/-- For odd-order groups the weak-closure normalizer alone is the whole group. -/
theorem isEGenerated_of_odd {i : ℕ} (ho : Odd (Nat.card G)) : IsEGenerated i G := by
  intro T Ω _
  have hnd : ¬ 2 ∣ Nat.card G := by
    intro hd
    exact (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr hd)) ho
  have hcard : Nat.card T = 1 := T.isPGroup'.card_eq_or_dvd.resolve_right
    (fun hd => hnd (hd.trans (T : Subgroup G).card_subgroup_dvd_card))
  have hT : (T : Subgroup G) = ⊥ := Subgroup.card_eq_one.mp hcard
  have hW : weakClosure (T : Subgroup G) Ω = ⊥ :=
    le_antisymm ((weakClosure_le _ _).trans_eq hT) bot_le
  simp only [hW, normalizer_eq_top, sup_top_eq]

end CFSG.Quasithin.ChapterE
