module
public import Stellmacher.ExceptionalType
public import Stellmacher.SectionEleven.C2S4SylowPairGeometry
public import Theory.SpecificGroups.CyclicTwoSymmetricFourSquarePlane

/-!
# Two noncommuting square four-groups in the local Sp₄(2) type

A finite group of local `Sp₄(2)` type has a Sylow two-subgroup isomorphic
to `C₂ × D₈` containing two normal elementary abelian subgroups of order
four. Their join is noncommutative, and every element of either subgroup
is a square in the ambient group. Only the source local-pair data is used;
no simplicity, local-solvability, or ambient generation assumption is needed.

Each vertex `Pᵢ ≃ C₂ × S₄` supplies a normal square four-group whose
centralizer is its elementary two-core of order eight. Normality puts each
four-group in the shared Sylow intersection and remains true after
restriction. The vertex two-cores are distinct: an equal core would be a
nontrivial normal two-subgroup of the generated join, contradicting the
pair's trivial join two-core. The existing Sylow elementary-pair theorem
then shows that the two cores generate the intersection, of order sixteen.
If the square four-groups commuted, the second would lie in both cores;
both elementary cores would centralize it, so the whole Sylow subgroup
would centralize it, contradicting its centralizer of order eight.

This supplies the local square-plane configuration used in
Kurzweil–Stellmacher, *The Theory of Finite Groups*, Chapter 12, proof of
Theorem 3, printed pp. 365–366 (`refs/latex/kurzweil.tex`). The local-type
hypotheses are the definition after (8.2) in
`refs/latex/stellmacher-n-group.tex`. The final subgroup transport preserves
normality, orders, noncommutativity, and the ambient square roots.
-/

namespace Stellmacher.Recognition
open SectionsFiveToSeven
open scoped IsMulCommutative

private theorem core_data {G : Type*} [Group G] [Finite G]
    (P : Subgroup G) (hModel : Later.IsModel P (Later.C2 × Later.S4)) :
    IsElementaryAbelian 2 (twoCoreIn P) ∧ Nat.card (twoCoreIn P) = 8 := by
  obtain ⟨hCore, hCards⟩ := symmetric_four_model_twoCore_data (Or.inr hModel)
  have hPcard : Nat.card P = 48 := by
    obtain ⟨model⟩ := hModel
    rw [Nat.card_congr model.toEquiv, Nat.card_prod]
    norm_num [Later.C2, Later.S4, Nat.card_eq_fintype_card, Fintype.card_perm]
  have hCoreCard : Nat.card (pCore 2 P) = 8 := by
    rcases hCards with hSmall | hLarge
    · omega
    · exact hLarge.1
  exact ⟨hCore.map P.subtype,
    (Subgroup.card_map_of_injective P.subtype_injective).trans hCoreCard⟩

private theorem core_normalizer {G : Type*} [Group G] (P : Subgroup G) :
    P ≤ Subgroup.normalizer (twoCoreIn P : Set G) := by
  have hnormal : ((twoCoreIn P).subgroupOf P).Normal := by
    change ((pCore 2 P).map P.subtype |>.comap P.subtype).Normal
    rw [Subgroup.comap_map_eq_self (by simp)]
    infer_instance
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.map_subtype_le (pCore 2 P))).mp hnormal

private theorem pair_cores_ne {G : Type*} [Group G] [Finite G]
    (pair : LocalTypePair G) (hCard : Nat.card (twoCoreIn pair.first) = 8) :
    twoCoreIn pair.first ≠ twoCoreIn pair.second := by
  intro heq
  let E := twoCoreIn pair.first
  let J := pair.first ⊔ pair.second
  have hEJ : E ≤ J := (Subgroup.map_subtype_le (pCore 2 pair.first)).trans le_sup_left
  have hJN : J ≤ Subgroup.normalizer (E : Set G) := by
    apply sup_le (core_normalizer pair.first)
    simpa only [E, heq] using core_normalizer pair.second
  have hnormal : (E.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEJ).mpr hJN
  have htwo : IsPGroup 2 E := pCore_isPGroup.map pair.first.subtype
  have htwoJ : IsPGroup 2 (E.subgroupOf J) :=
    htwo.of_equiv (Subgroup.subgroupOfEquivOfLe hEJ).symm
  have hbot : E.subgroupOf J = ⊥ := by
    apply bot_unique
    exact (show E.subgroupOf J ≤ pCore 2 J from le_sSup ⟨hnormal, htwoJ⟩).trans_eq
      pair.join_twoCore_eq_bot
  have hEbot : E = ⊥ := by
    have hm := congrArg (Subgroup.map J.subtype) hbot
    simpa only [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hEJ,
      Subgroup.map_bot] using hm
  have : Nat.card E = 1 := by rw [hEbot]; simp
  change Nat.card E = 8 at hCard
  omega

private theorem local_sylow {G : Type*} [Group G] (S : Sylow 2 G)
    (P : Subgroup G) (hSP : (S : Subgroup G) ≤ P) :
    IsSylowTwoIn (S : Subgroup G) P := by
  refine ⟨hSP, S.subtype hSP, ?_⟩
  rw [Sylow.coe_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSP]

private theorem plane_transport {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (P : Subgroup G) (hSP : (S : Subgroup G) ≤ P)
    (Q : Subgroup P) (hN : Q.Normal) (hE : IsElementaryAbelian 2 Q)
    (hC : Nat.card Q = 4)
    (hSq : ∀ q : P, q ∈ Q → ∃ x : P, x ^ 2 = q)
    (hCent : Subgroup.centralizer (Q : Set P) = pCore 2 P) :
    ∃ A : Subgroup G, A ≤ (S : Subgroup G) ∧
      (A.subgroupOf (S : Subgroup G)).Normal ∧ IsElementaryAbelian 2 A ∧
      Nat.card A = 4 ∧ (∀ q : G, q ∈ A → ∃ x : G, x ^ 2 = q) ∧
      (S : Subgroup G) ⊓ Subgroup.centralizer (A : Set G) = twoCoreIn P := by
  let _ := hN
  let _ := hE
  let A := Q.map P.subtype
  have hQS : Q ≤ (S.subtype hSP : Subgroup P) :=
    (IsElementaryAbelian.isPGroup 2 Q).le_sylow_of_normal (S.subtype hSP)
  have hAS : A ≤ (S : Subgroup G) := by
    have hh := Subgroup.map_mono (f := P.subtype) hQS
    rwa [Sylow.coe_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSP] at hh
  have hPN : P ≤ Subgroup.normalizer (A : Set G) := by
    have hh := Q.le_normalizer_map P.subtype
    simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] using hh
  have hCoreS : twoCoreIn P ≤ (S : Subgroup G) := by
    have hh := Subgroup.map_mono (f := P.subtype)
      ((pCore_isPGroup (p := 2) (G := P)).le_sylow_of_normal (S.subtype hSP))
    rwa [Sylow.coe_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSP] at hh
  refine ⟨A, hAS,
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAS).mpr (hSP.trans hPN),
    hE.map P.subtype, (Subgroup.card_map_of_injective P.subtype_injective).trans hC,
    ?_, le_antisymm ?_ ?_⟩
  · rintro q ⟨qP, hq, rfl⟩
    obtain ⟨x, hx⟩ := hSq qP hq
    exact ⟨x, congrArg Subtype.val hx⟩
  · intro x hx
    let xP : P := ⟨x, hSP hx.1⟩
    have hxc : xP ∈ Subgroup.centralizer (Q : Set P) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro y hy
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hx.2 y ⟨y, hy, rfl⟩
    exact ⟨xP, hCent ▸ hxc, rfl⟩
  · rintro x ⟨xP, hx, rfl⟩
    refine ⟨hCoreS ⟨xP, hx, rfl⟩, ?_⟩
    apply Subgroup.mem_centralizer_iff.mpr
    rintro y ⟨yP, hy, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp (hCent.symm ▸ hx) yP hy)

private theorem planes_noncommuting {G : Type*} [Group G] [Finite G]
    (S E1 E2 A1 A2 : Subgroup G)
    (hE1 : IsElementaryAbelian 2 E1) (hE2 : IsElementaryAbelian 2 E2)
    (hAS2 : A2 ≤ S)
    (hElem2 : IsElementaryAbelian 2 A2)
    (hC1 : S ⊓ Subgroup.centralizer (A1 : Set G) = E1)
    (hC2 : S ⊓ Subgroup.centralizer (A2 : Set G) = E2)
    (hJoin : E1 ⊔ E2 = S) (hProper : E2 ≠ S) :
    ¬ IsMulCommutative (A1 ⊔ A2 : Subgroup G) := by
  intro hComm
  have hA2E1 : A2 ≤ E1 := by
    rw [← hC1]
    refine le_inf hAS2 ?_
    have hc := Subgroup.le_centralizer_iff_isMulCommutative.mpr hComm
    exact (le_sup_right.trans hc).trans (Subgroup.centralizer_le (show A1 ≤ A1 ⊔ A2 from le_sup_left))
  have hA2E2 : A2 ≤ E2 := by
    rw [← hC2]
    exact le_inf hAS2 (Subgroup.le_centralizer_iff_isMulCommutative.mpr
      hElem2.toIsMulCommutative)
  have hScent : S ≤ Subgroup.centralizer (A2 : Set G) := by
    rw [← hJoin]
    apply sup_le
    · exact (Subgroup.le_centralizer_iff_isMulCommutative.mpr
        hE1.toIsMulCommutative).trans (Subgroup.centralizer_le hA2E1)
    · exact (Subgroup.le_centralizer_iff_isMulCommutative.mpr
        hE2.toIsMulCommutative).trans (Subgroup.centralizer_le hA2E2)
  exact hProper (hC2.symm.trans (inf_eq_left.mpr hScent))


/-- A local Sp₄(2) pair supplies two normal elementary four-groups in its
Sylow intersection whose join is noncommutative and whose elements are
squares in the ambient group. -/
public theorem sp4Two_square_planes {G : Type*} [Group G] [Finite G]
    (hType : IsOfSp4TwoType G) :
    ∃ S : Sylow 2 G, Nonempty (S ≃* (Multiplicative (ZMod 2) × DihedralGroup 4)) ∧
      ∃ Q1 Q2 : Subgroup S, Q1.Normal ∧ Q2.Normal ∧
        IsElementaryAbelian 2 Q1 ∧ IsElementaryAbelian 2 Q2 ∧
        Nat.card Q1 = 4 ∧ Nat.card Q2 = 4 ∧
        ¬ IsMulCommutative (Q1 ⊔ Q2 : Subgroup S) ∧
        (∀ q : S, q ∈ Q1 → ∃ x : G, x ^ 2 = (q : G)) ∧
        (∀ q : S, q ∈ Q2 → ∃ x : G, x ^ 2 = (q : G)) := by
  obtain ⟨pair, hModel1, hModel2⟩ := hType
  let S := pair.sylowIntersection
  have hSP1 : (S : Subgroup G) ≤ pair.first := by
    rw [← pair.intersection_eq]
    exact inf_le_left
  have hSP2 : (S : Subgroup G) ≤ pair.second := by
    rw [← pair.intersection_eq]
    exact inf_le_right
  obtain ⟨hE1, hCard1⟩ := core_data pair.first hModel1
  obtain ⟨hE2, hCard2⟩ := core_data pair.second hModel2
  have hne := pair_cores_ne pair hCard1
  obtain ⟨hSModel, B, hE1S, _, _, _, hBCard, hJoinB, _, hCover, _⟩ :=
    SectionEleven.c2s4_sylow_elementary_pair (S : Subgroup G) pair.first
      (local_sylow S pair.first hSP1) hModel1 hE1 hCard1
  have hE2S : twoCoreIn pair.second ≤ (S : Subgroup G) := by
    obtain ⟨_, T, hT⟩ := local_sylow S pair.second hSP2
    exact (Subgroup.map_mono
      ((pCore_isPGroup (p := 2) (G := pair.second)).le_sylow_of_normal T)).trans_eq hT
  have hJoin : twoCoreIn pair.first ⊔ twoCoreIn pair.second = (S : Subgroup G) := by
    rcases hCover _ hE2S hE2 with hle | hle
    · exact (hne (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm).elim
    · have heq : twoCoreIn pair.second = B :=
        Subgroup.eq_of_le_of_card_ge hle (by omega)
      simpa only [heq] using hJoinB
  have hSCard : Nat.card S = 16 := by
    obtain ⟨model⟩ := hSModel
    rw [Nat.card_congr model.toEquiv, Nat.card_prod]
    norm_num [DihedralGroup.card, Later.C2]
  have hProper : twoCoreIn pair.second ≠ (S : Subgroup G) := by
    intro heq
    rw [heq] at hCard2
    omega
  obtain ⟨Q1, hN1, hElem1, hFour1, hSquare1, hCent1⟩ := c2s4_exists_square_plane hModel1
  obtain ⟨Q2, hN2, hElem2, hFour2, hSquare2, hCent2⟩ := c2s4_exists_square_plane hModel2
  obtain ⟨A1, hAS1, hAN1, hAE1, hAC1, hSq1, hC1⟩ :=
    plane_transport S pair.first hSP1 Q1 hN1 hElem1 hFour1 hSquare1 hCent1
  obtain ⟨A2, hAS2, hAN2, hAE2, hAC2, hSq2, hC2⟩ :=
    plane_transport S pair.second hSP2 Q2 hN2 hElem2 hFour2 hSquare2 hCent2
  have hNoncomm := planes_noncommuting (S : Subgroup G)
    (twoCoreIn pair.first) (twoCoreIn pair.second) A1 A2
    hE1 hE2 hAS2 hAE2 hC1 hC2 hJoin hProper
  let _ := hAE1
  let _ := hAE2
  refine ⟨S, hSModel, A1.subgroupOf (S : Subgroup G), A2.subgroupOf (S : Subgroup G),
    hAN1, hAN2, IsElementaryAbelian.subgroupOf hAS1,
    IsElementaryAbelian.subgroupOf hAS2,
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAS1).toEquiv).trans hAC1,
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAS2).toEquiv).trans hAC2,
    ?_, ?_, ?_⟩
  · intro hcomm
    let _ := hcomm
    have hm : IsMulCommutative
        (((A1.subgroupOf (S : Subgroup G)) ⊔ (A2.subgroupOf (S : Subgroup G))).map
          (S : Subgroup G).subtype) := Subgroup.map_isMulCommutative _ _
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAS1, inf_eq_left.mpr hAS2] at hm
    exact hNoncomm hm
  · intro q hq
    exact hSq1 q hq
  · intro q hq
    exact hSq2 q hq

end Stellmacher.Recognition
