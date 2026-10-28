module

public import CFSG.Quasithin.ChapterE.Section01.ReverseLift.Preparation
public import CFSG.Quasithin.ChapterE.Section01.MinimalStructure.OddSeries
public import CFSG.Quasithin.ChapterE.Section01.ReverseLift.Odd.Minimal
public import CFSG.Quasithin.ChapterE.Section01.ReverseLift.Odd.Reduction

/-!
# The odd-prime branch of reverse E-member quotient lifting

The odd E-member supplies the intrinsic odd-case data for its source
residual--tau subgroup through `IsEMember.residualTau_odd_data`. We lift its
full preimage using a genuine minimal supplement, apply E.1.8(2) to inherit
E-membership in the original group, and identify the embedded two-residual
through the literal quotient map. The lifted subgroup need only cover the
residual--tau subgroup; its image need not be the original member.

The conditional assembly interface is retained, and
`exists_odd_quotient_lift` discharges its shrinking premise from the original
odd disjunct of `IsEMemberAt`. No condition on the whole supplement kernel
is imposed.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
proof of E.1.10(7), printed pp.211--212 (1 March 2004 manuscript).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

/-- Assemble the odd quotient lift from intrinsic data on the residual--tau
subgroup. This theorem keeps the source shrinking step explicit. -/
theorem exists_odd_quotient_lift_of_residualTau_data {i : ℕ} (T : Sylow 2 G)
    (A Y : Subgroup G) [Y.Normal] [IsElementaryAbelian 2 A]
    (hAT : A ≤ (T : Subgroup G)) {I : Subgroup (G ⧸ Y)}
    (h0 : IsEMember ((T : Subgroup G).map (QuotientGroup.mk' Y))
      (A.map (QuotientGroup.mk' Y)) I)
    (ho : ECaseOdd (A.map (QuotientGroup.mk' Y)) I)
    (hi : Group.rank (((A.map (QuotientGroup.mk' Y)).subgroupOf I).map
      (QuotientGroup.mk' (pCore 2 I))) ≤ i)
    (hred :
      let R := residualTau ((T : Subgroup G).map (QuotientGroup.mk' Y))
        (A.map (QuotientGroup.mk' Y)) I
      ∃ p : ℕ, p.Prime ∧ Odd p ∧
        IsPGroup 2 ((R ⧸ pCore 2 R) ⧸ pCore p (R ⧸ pCore 2 R)) ∧
        pCore p (R ⧸ pCore 2 R) ≠ ⊥ ∧
        pCore p (R ⧸ pCore 2 R) = ⁅pCore p (R ⧸ pCore 2 R),
          ((A.map (QuotientGroup.mk' Y)).subgroupOf R).map
            (QuotientGroup.mk' (pCore 2 R))⁆ ∧
        Group.rank (((A.map (QuotientGroup.mk' Y)).subgroupOf R).map
          (QuotientGroup.mk' (pCore 2 R))) = 1 ∧
        tau (((T : Subgroup G).map (QuotientGroup.mk' Y)).subgroupOf R)
          ((A.map (QuotientGroup.mk' Y)).subgroupOf R) =
            ((T : Subgroup G).map (QuotientGroup.mk' Y)).subgroupOf R) :
    ∃ J : Subgroup G, IsEMemberAt i (T : Subgroup G) A J ∧
      ((pResidual 2 J).map J.subtype).map (QuotientGroup.mk' Y) =
        (pResidual 2 I).map I.subtype := by
  let q := QuotientGroup.mk' Y
  let R := residualTau ((T : Subgroup G).map q) (A.map q) I
  let U := R.comap q
  have hI : IsEMemberAt i ((T : Subgroup G).map q) (A.map q) I :=
    ⟨h0, Or.inl ⟨ho, hi⟩⟩
  obtain ⟨hτU, hAU, S, hS⟩ := hI.residualTau_preimage T A Y hAT
  let f : U →* R := (q.comp U.subtype).codRestrict R (fun x => x.property)
  have hf : Function.Surjective f := by
    intro r
    obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective Y r.val
    exact ⟨⟨u, by change q u ∈ R; rw [hu]; exact r.property⟩, Subtype.ext hu⟩
  have hAf : (A.subgroupOf U).map f = (A.map q).subgroupOf R := by
    ext r
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact mem_map_of_mem q ha
    · rintro ⟨a, ha, he⟩
      exact ⟨⟨a, hAU ha⟩, ha, Subtype.ext he⟩
  have hSf : (S : Subgroup U).map f = ((T : Subgroup G).map q).subgroupOf R := by
    rw [hS]
    ext r
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact mem_map_of_mem q hs
    · rintro ⟨s, hs, he⟩
      have hsU : s ∈ U := by change q s ∈ R; rw [he]; exact r.property
      exact ⟨⟨s, hsU⟩, hs, Subtype.ext he⟩
  have hAS : A.subgroupOf U ≤ (S : Subgroup U) := by
    rw [hS]
    exact subgroupOf_mono U hAT
  have hAUelem : IsElementaryAbelian 2 (A.subgroupOf U) :=
    IsElementaryAbelian.subgroupOf hAU
  let := hAUelem
  obtain ⟨p, hp, hpodd, hquot, hne, hcomm, hrank, htau⟩ := hred
  let : Fact p.Prime := ⟨hp⟩
  have hi' : 1 ≤ i := by
    obtain ⟨_, _, _, _, _, _, hr⟩ := ho
    rwa [hr] at hi
  obtain ⟨J, hJ, hJf⟩ := exists_odd_lift_of_surjective_reduced_image S
    (A.subgroupOf U) hAS f hf (by rintro rfl; norm_num at hpodd) hquot hne
    (by rwa [hAf]) (by rwa [hAf]) (by rwa [hAf, hSf]) hi'
  have hJ' : IsEMemberAt i ((T : Subgroup G).subgroupOf U) (A.subgroupOf U) J :=
    hS ▸ hJ
  refine ⟨J.map U.subtype, hJ'.inherit T A U hAT hτU, ?_⟩
  have himage : (J.map U.subtype).map q = R := by
    calc
      _ = (J.map f).map R.subtype := by rw [map_map, map_map]; rfl
      _ = R := by rw [hJf, ← MonoidHom.range_eq_map, range_subtype]
  rw [map_embedded_pResidual, himage]
  exact h0.residualTau_residual

/-- The odd-prime branch of E.1.10(7): lift a quotient E-member with the same
rank bound and the same embedded two-residual image. All shrinking and
minimal-supplement premises are discharged from the original odd E-case. -/
theorem exists_odd_quotient_lift {i : ℕ} (T : Sylow 2 G)
    (A Y : Subgroup G) [Y.Normal] [IsElementaryAbelian 2 A]
    (hAT : A ≤ (T : Subgroup G)) {I : Subgroup (G ⧸ Y)}
    (h0 : IsEMember ((T : Subgroup G).map (QuotientGroup.mk' Y))
      (A.map (QuotientGroup.mk' Y)) I)
    (ho : ECaseOdd (A.map (QuotientGroup.mk' Y)) I)
    (hi : Group.rank (((A.map (QuotientGroup.mk' Y)).subgroupOf I).map
      (QuotientGroup.mk' (pCore 2 I))) ≤ i) :
    ∃ J : Subgroup G, IsEMemberAt i (T : Subgroup G) A J ∧
      ((pResidual 2 J).map J.subtype).map (QuotientGroup.mk' Y) =
        (pResidual 2 I).map I.subtype :=
  exists_odd_quotient_lift_of_residualTau_data T A Y hAT h0 ho hi
    (h0.residualTau_odd_data ho)

end CFSG.Quasithin.ChapterE
