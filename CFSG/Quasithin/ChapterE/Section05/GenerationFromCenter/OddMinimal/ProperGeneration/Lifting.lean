module

public import CFSG.Quasithin.ChapterE.Section05.GenerationFromCenter.OddMinimal.ProperGeneration.Defs
public import Theory.GroupTheory.PCoreSurjective.OddExtension
public import CFSG.Quasithin.ChapterE.Section01.Inheritance

/-!
# Lifting proper odd quotient pieces to E-members

The preimage of a quotient piece contains the whole prescribed Sylow
intersection, hence also the ambient tau subgroup. Restricting the quotient
map gives a surjection with two-group kernel. Core transport identifies
the intrinsic two-core quotients; the normal odd subgroup verifies every
E1 clause. Its nontrivial full commutator forces the actor image still to
have rank one, so every positive E-index is allowed.

Source: the reducible odd-member reduction in Aschbacher–Smith, E.5.2,
printed p.243, using E.1.2 and E.1.5 (1 March 2004 manuscript).
-/

open Subgroup
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

private theorem member_of_odd_between {j : ℕ} (hj : 0 < j)
    {T A K L : Subgroup G} (hK : IsEMemberAt j T A K)
    (hTL : T ⊓ K ≤ L) (hLK : L ≤ K) (ho : ECaseOdd A L) :
    IsEMemberAt j T A L := by
  obtain ⟨S, hS⟩ := hK.1.2.2.2.2.1
  have hAL : A ≤ L := (le_inf hK.1.2.1 hK.1.2.2.1).trans hTL
  have hs : ∃ R : Sylow 2 L, (R : Subgroup L) = T.subgroupOf L := by
    let f := inclusion hLK
    have hi : Function.Injective f := inclusion_injective hLK
    have hr : (S : Subgroup K) ≤ f.range := by
      intro x hx
      have hxT : x.val ∈ T := by
        rw [hS] at hx
        exact hx
      exact ⟨⟨x.val, hTL ⟨hxT, x.property⟩⟩, rfl⟩
    refine ⟨S.comapOfInjective f hi hr, ?_⟩
    ext x
    change f x ∈ (S : Subgroup K) ↔ x.val ∈ T
    rw [hS]
    rfl
  have hrank : Group.rank ((A.subgroupOf L).map (QuotientGroup.mk' (pCore 2 L))) = 1 := by
    obtain ⟨p, hp, hod, hq, hn, hc, hr⟩ := ho
    exact hr
  exact ⟨⟨hK.1.1, hK.1.2.1, hAL,
    le_inf (hK.1.2.2.2.1.trans inf_le_left) (hK.1.2.2.2.1.trans hTL), hs, Or.inl ho⟩,
    Or.inl ⟨ho, by simpa only [hrank] using Nat.succ_le_of_lt hj⟩⟩

private theorem image_restrict_preimage {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (B : Subgroup X) (J : Subgroup Y) :
    (B.subgroupOf (J.comap f)).map (f.subgroupComap J) = (B.map f).subgroupOf J := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.val, hx, rfl⟩
  · rintro ⟨x, hx, hxy⟩
    exact ⟨⟨x, show f x ∈ J from hxy.symm ▸ y.property⟩, hx, Subtype.ext hxy⟩

/-- A proper quotient piece lifts to a genuine proper E-member, with its
own intrinsic two-core and the original ambient tau and Sylow conditions. -/
public theorem proper_member_of_quotient_piece {j p : ℕ} (hj : 0 < j)
    (hp : p.Prime) (hpodd : Odd p) {T A K : Subgroup G}
    (hK : IsEMemberAt j T A K)
    (hrank : Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) = 1)
    (J : Subgroup (K ⧸ pCore 2 K))
    (hJ : OddQuotientPiece p
      ((A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K)))
      ((T.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) J) :
    let L := (J.comap (QuotientGroup.mk' (pCore 2 K))).map K.subtype
    L < K ∧ IsEMemberAt j T A L := by
  let _ : Fact p.Prime := ⟨hp⟩
  let q := QuotientGroup.mk' (pCore 2 K)
  let B := A.subgroupOf K
  let I := J.comap q
  let L := I.map K.subtype
  have hBJ : B.map q ≤ J := (map_mono (show B ≤ T.subgroupOf K from
    fun x hx => hK.1.2.1 hx)).trans hJ.1
  have hTI : T.subgroupOf K ≤ I := map_le_iff_le_comap.mp hJ.1
  have hTL : T ⊓ K ≤ L := by
    intro x hx
    exact ⟨⟨x, hx.2⟩, hTI hx.1, rfl⟩
  have hproper : L < K := by
    refine lt_of_le_of_ne (map_subtype_le I) ?_
    intro he
    have hItop : I = ⊤ := by
      apply map_injective K.subtype_injective
      rw [← MonoidHom.range_eq_map, K.range_subtype]
      exact he
    apply hJ.2.1
    calc
      J = I.map q := (map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) J).symm
      _ = (⊤ : Subgroup K).map q := congrArg (map q) hItop
      _ = ⊤ := map_top_of_surjective q (QuotientGroup.mk'_surjective _)
  have ho : ECaseOdd B I := by
    obtain ⟨N, hnormal, hN, hquot, hne, hcomm⟩ := hJ.2.2
    let _ : N.Normal := hnormal
    let f := q.subgroupComap J
    have hker : f.ker = (pCore 2 K).subgroupOf I := by
      ext x
      change (f x = 1) ↔ x.val ∈ pCore 2 K
      rw [Subtype.ext_iff]
      exact QuotientGroup.eq_one_iff x.val
    have hk : IsPGroup 2 f.ker := by
      rw [hker]
      exact pCore_isPGroup.comap_subtype
    have hf : Function.Surjective f := q.subgroupComap_surjective_of_surjective J
      (QuotientGroup.mk'_surjective _)
    have hb : (B.subgroupOf I).map f = (B.map q).subgroupOf J :=
      image_restrict_preimage q B J
    have hbcomm : N = ⁅N, (B.subgroupOf I).map f⁆ := by rwa [hb]
    have hbRank : Group.rank ((B.subgroupOf I).map f) = 1 := by
      rw [hb]
      exact (Group.rank_congr (subgroupOfEquivOfLe hBJ)).trans hrank
    have hp2 : p ≠ 2 := by intro he; subst p; norm_num at hpodd
    exact ⟨p, hp, hpodd, odd_quotient_commutator_rank_of_surjective hp2
      f hf hk N (B.subgroupOf I) hN hquot hne hbcomm hbRank⟩
  have hoL : ECaseOdd A L := by
    have hm := ho.map_injective K.subtype K.subtype_injective
    rwa [map_subgroupOf_eq_of_le hK.1.2.2.1] at hm
  exact ⟨hproper, member_of_odd_between hj hK hTL hproper.le hoL⟩


end CFSG.Quasithin.ChapterE
