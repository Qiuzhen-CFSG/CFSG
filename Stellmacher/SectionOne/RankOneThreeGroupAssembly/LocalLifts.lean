module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Basic
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaGeneration
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.FactorLifts
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Defs
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.LocalFixedIndex

/-!
# Lifted recursive factor families

Each factor in the recursive SL2 product lifts through the cardinal-preserving odd-core quotient map. Its coordinate preserves full fixed index two and generates the Sylow subgroup together with the distinguished involution.

This module supports the rank-at-least-two case of Stellmacher (1.6).
The action is on an elementary abelian two-group; the local hypotheses and
minimal-offender conditions are explicit in the declarations that use them.
Source: `refs/latex/stellmacher-n-group.tex`, proof of (1.6), journal pp.18–19.
-/

open scoped Pointwise symmDiff

namespace Stellmacher.SectionOne.RankOneThreeGroupAssembly

universe u v

/-- Every derived order-three factor supplied by the recursive quotient
decomposition lifts, with unchanged order, into the corresponding ambient
commutator subgroup `W_A`. -/
public theorem local_hypothesis_gives_derived_factor_lifts
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S A : Subgroup G)
    (hlocal : RankOneAssemblyLocalHypothesis (G := G) (V := V) S)
    (hAmax : oneAmax (G := G) (V := V) S A)
    (hAcard : Nat.card A = 2) :
    let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
    let H := W_A ⊔ S
    let A_H := A.subgroupOf H
    ∃ hA_H : A_H.Normal,
      let _ : A_H.Normal := hA_H
      let V_A := FixedPoints.subgroup A_H V
      ∃ P : Sylow 2 (H ⧸ A_H),
      ∃ Fbar : Finset (Subgroup (H ⧸ A_H)),
        (P : Subgroup (H ⧸ A_H)) =
            (S.subgroupOf H).map (QuotientGroup.mk' A_H) ∧
        oddCore (H ⧸ A_H) =
            (W_A.subgroupOf H).map (QuotientGroup.mk' A_H) ∧
        Nat.card ((W_A.subgroupOf H).map (QuotientGroup.mk' A_H)) =
            Nat.card W_A ∧
        (∀ E : Subgroup (H ⧸ A_H), E ∈ Fbar →
          IsSL2Two (↑E) ∧
          oneOmega (G := H ⧸ A_H) (V := V_A)
            ((commutator (↑E)).map E.subtype)) ∧
        IsInternalDirectProduct
          (oddCore (H ⧸ A_H) ⊔ (P : Subgroup (H ⧸ A_H))) Fbar ∧
        oddCore (H ⧸ A_H) =
          ⨆ E : {E : Subgroup (H ⧸ A_H) // E ∈ Fbar},
            (commutator (E : Subgroup (H ⧸ A_H))).map E.val.subtype ∧
        ∀ E : Subgroup (H ⧸ A_H), E ∈ Fbar →
          ∃ F : Subgroup G,
            F ≤ W_A ∧
            F ≤ oddCore G ∧
            (F.subgroupOf H).map (QuotientGroup.mk' A_H) =
              ((commutator (↑E)).map E.subtype) ∧
            Nat.card F = 3 ∧
            (F.subgroupOf H).Normal ∧
            S ≤ Subgroup.normalizer F ∧
            ∃ Aᵢ : Subgroup G,
              A ≤ Aᵢ ∧ Aᵢ ≤ S ∧ Nat.card Aᵢ = 4 ∧
              (Aᵢ.subgroupOf H).map (QuotientGroup.mk' A_H) =
                ((P : Subgroup (H ⧸ A_H)) ⊓ E) ∧
              Nat.card (↥((P : Subgroup (H ⧸ A_H)) ⊓ E)) = 2 ∧
              ⁅(commutator (↑E)).map E.subtype,
                  (P : Subgroup (H ⧸ A_H)) ⊓ E⁆ =
                (commutator (↑E)).map E.subtype ∧
              fixedQuotientCard (G := H ⧸ A_H) (V := V_A)
                ((P : Subgroup (H ⧸ A_H)) ⊓ E)
                (commutatorAction (oddCore (H ⧸ A_H)) V_A) = 2 ∧
              (Nat.card V_A : ℚ) /
                  Nat.card (FixedPoints.subgroup
                    (↥((P : Subgroup (H ⧸ A_H)) ⊓ E)) V_A) = 2 ∧
              ⁅W_A, Aᵢ⁆ = F ∧
              ∀ x : G, x ∈ Aᵢ → x ∉ A →
                ⁅F, Subgroup.zpowers x⁆ = F ∧
                (Nat.card V_A : ℚ) /
                    Nat.card (↥(V_A ⊓ FixedPoints.subgroup
                      (Subgroup.zpowers x) V)) = 2 := by
  let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
  let H := W_A ⊔ S
  let A_H := A.subgroupOf H
  obtain ⟨hA_H, P, hP, hcore, hcard, hdata, hmP⟩ :=
    hlocal A hAmax hAcard
  let _ : A_H.Normal := hA_H
  let V_A := FixedPoints.subgroup A_H V
  let _ : IsElementaryAbelian 2 V_A := isElementaryAbelian_subgroup V_A
  obtain ⟨Fbar, hFbar, hprod, hgen, hcoord⟩ :=
    Stellmacher.SectionOne.rankOneLocalSL2Data_full_coordinates P hdata hmP
  refine ⟨hA_H, P, Fbar, hP, hcore, hcard, hFbar, hprod, hgen, ?_⟩
  intro E hE
  let D : Subgroup (H ⧸ A_H) := (commutator (↑E)).map E.subtype
  let Q : Subgroup (H ⧸ A_H) := (P : Subgroup (H ⧸ A_H)) ⊓ E
  have hDomega : oneOmega (G := H ⧸ A_H) (V := V_A) D :=
    (hFbar E hE).2
  have hDle : D ≤ (W_A.subgroupOf H).map (QuotientGroup.mk' A_H) := by
    rw [← hcore]
    exact hDomega.1
  have htop : oddCore (H ⧸ A_H) ⊔
      (P : Subgroup (H ⧸ A_H)) = ⊤ := by
    calc
      oddCore (H ⧸ A_H) ⊔ (P : Subgroup (H ⧸ A_H)) =
          (W_A.subgroupOf H).map (QuotientGroup.mk' A_H) ⊔
            (S.subgroupOf H).map (QuotientGroup.mk' A_H) := by
        rw [hcore, hP]
      _ = ((W_A.subgroupOf H) ⊔ (S.subgroupOf H)).map
          (QuotientGroup.mk' A_H) := by rw [Subgroup.map_sup]
      _ = ((W_A ⊔ S).subgroupOf H).map
          (QuotientGroup.mk' A_H) := by
        rw [Subgroup.subgroupOf_sup le_sup_left le_sup_right]
      _ = ⊤ := by
        change (H.subgroupOf H).map (QuotientGroup.mk' A_H) = ⊤
        rw [Subgroup.subgroupOf_self,
          Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective A_H)]
  have hDnormal : D.Normal :=
    derived_factor_normal_of_internalDirectProduct_eq_top
      (oddCore (H ⧸ A_H)) (P : Subgroup (H ⧸ A_H)) Fbar hprod htop E hE
  have hAle : A ≤ W_A ⊔ S := hAmax.1.trans le_sup_right
  obtain ⟨F, hFW, hFmap, hFcard⟩ :=
    exists_local_order_three_factor_lift
      (V := V_A) W_A S A hAle D hDomega hDle hcard
  have hFnorm : (F.subgroupOf H).Normal := by
    apply local_factor_lift_normal W_A S A F le_sup_left
      (local_commutator_normal_in_join
        (oddCore G ⊓ Subgroup.centralizer (A : Set G)) S)
      hFW hcard
    rw [hFmap]
    exact hDnormal
  have hFH : F ≤ H := hFW.trans le_sup_left
  have hSnorm : S ≤ Subgroup.normalizer F :=
    le_sup_right.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hFH).mp hFnorm)
  obtain ⟨hQcard, hDcomm, hfixed, hfullFixed⟩ := hcoord E hE
  change Nat.card Q = 2 at hQcard
  change ⁅D, Q⁆ = D at hDcomm
  have hQle : Q ≤
      (S.subgroupOf H).map (QuotientGroup.mk' A_H) := by
    rw [← hP]
    exact inf_le_left
  obtain ⟨Aᵢ, hAleAᵢ, hAᵢleS, hAᵢcard, hAᵢmap⟩ :=
    exists_order_four_coordinate_lift S A H hAmax.1 le_sup_right
      Q hQle hAcard hQcard
  let Dbar (K : {K : Subgroup (H ⧸ A_H) // K ∈ Fbar}) :
      Subgroup (H ⧸ A_H) :=
    (commutator (K : Subgroup (H ⧸ A_H))).map K.val.subtype
  let _ : D.Normal := hDnormal
  have hcoreCommLe : ⁅oddCore (H ⧸ A_H), Q⁆ ≤ D := by
    apply commutator_le_normal_of_eq_iSup
      (oddCore (H ⧸ A_H)) Q D Dbar hgen
    intro K
    by_cases hKE : (K : Subgroup (H ⧸ A_H)) = E
    · have hK : K = ⟨E, hE⟩ := Subtype.ext hKE
      subst K
      exact le_of_eq hDcomm
    · have hbot : ⁅Dbar K, Q⁆ = ⊥ := by
        rw [Subgroup.commutator_comm,
          Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro q hq
        rw [Subgroup.mem_centralizer_iff]
        intro d hd
        exact (hprod.2.2.2 E hE (K : Subgroup (H ⧸ A_H)) K.property
          (Ne.symm hKE) q hq.2 d
          (Subgroup.map_subtype_le (commutator K) hd)).symm
      rw [hbot]
      exact bot_le
  have hcoreComm : ⁅oddCore (H ⧸ A_H), Q⁆ = D := by
    apply le_antisymm hcoreCommLe
    rw [← hDcomm]
    exact Subgroup.commutator_mono hDomega.1 le_rfl
  let K : Subgroup H := W_A.subgroupOf H
  let L : Subgroup H := F.subgroupOf H
  let R : Subgroup H := Aᵢ.subgroupOf H
  let q : H →* H ⧸ A_H := QuotientGroup.mk' A_H
  have hKnormal : K.Normal :=
    local_commutator_normal_in_join
      (oddCore G ⊓ Subgroup.centralizer (A : Set G)) S
  let _ : K.Normal := hKnormal
  have hcommLeK : ⁅K, R⁆ ≤ K := Subgroup.commutator_le_left K R
  have hLleK : L ≤ K := fun x hx => hFW hx
  have hKcard : Nat.card (K.map q) = Nat.card K := by
    change Nat.card ((W_A.subgroupOf H).map (QuotientGroup.mk' A_H)) =
      Nat.card (W_A.subgroupOf H)
    exact hcard.trans (natCard_subgroupOf_eq W_A H le_sup_left).symm
  have hcommMap : (⁅K, R⁆).map q = L.map q := by
    have hRmap : R.map q = Q := hAᵢmap
    have hKmap : K.map q = oddCore (H ⧸ A_H) := hcore.symm
    have hLmap : L.map q = D := hFmap
    rw [Subgroup.map_commutator, hRmap, hKmap, hLmap, hcoreComm]
  have hcommSub : ⁅K, R⁆ = L :=
    eq_of_le_of_le_of_map_eq_of_inf_ker_eq_bot K ⁅K, R⁆ L q
      hcommLeK hLleK hcommMap
      (inf_ker_eq_bot_of_natCard_map_eq K q hKcard)
  have hWAcomm : ⁅W_A, Aᵢ⁆ = F := by
    calc
      ⁅W_A, Aᵢ⁆ = (⁅K, R⁆).map H.subtype := by
        symm
        exact commutator_subgroupOf_map_eq (S := H) (H := Aᵢ)
          (R := W_A) (hAᵢleS.trans le_sup_right) le_sup_left
      _ = L.map H.subtype := congrArg (fun X : Subgroup H => X.map H.subtype) hcommSub
      _ = F := Subgroup.map_subgroupOf_eq_of_le hFH
  have hpointComm : ∀ x : G, x ∈ Aᵢ → x ∉ A →
      ⁅F, Subgroup.zpowers x⁆ = F ∧
      (Nat.card V_A : ℚ) /
          Nat.card (↥(V_A ⊓ FixedPoints.subgroup
            (Subgroup.zpowers x) V)) = 2 := by
    intro x hxAᵢ hxnotA
    let xH : H := ⟨x, hAᵢleS.trans le_sup_right hxAᵢ⟩
    let XH : Subgroup H := Subgroup.zpowers xH
    have hqxQ : q xH ∈ Q := by
      rw [← hAᵢmap]
      exact ⟨xH, hxAᵢ, rfl⟩
    have hqxne : q xH ≠ 1 := by
      intro hxone
      have hxAH := (QuotientGroup.eq_one_iff (N := A_H) (x := xH)).mp hxone
      exact hxnotA hxAH
    have hQzp : Q = Subgroup.zpowers (q xH) :=
      subgroup_card_two_eq_zpowers_of_mem_ne_one Q hQcard hqxQ hqxne
    have hXHmap : XH.map q = Q := by
      change (Subgroup.zpowers xH).map q = Q
      rw [MonoidHom.map_zpowers, ← hQzp]
    have hXHambient : XH.map H.subtype = Subgroup.zpowers x := by
      change (Subgroup.zpowers xH).map H.subtype = Subgroup.zpowers x
      rw [MonoidHom.map_zpowers]
      rfl
    have hfixedCard := natCard_fixedPoints_quotient_map_eq_inf
      (V := V) H A_H XH Q hXHmap
    have hfullAmbient : (Nat.card V_A : ℚ) /
        Nat.card (↥(V_A ⊓ FixedPoints.subgroup
          (Subgroup.zpowers x) V)) = 2 := by
      rw [← hXHambient, ← hfixedCard]
      exact hfullFixed
    let hLnormal : L.Normal := hFnorm
    let _ : L.Normal := hLnormal
    have hcommXL : ⁅L, XH⁆ ≤ L := Subgroup.commutator_le_left L XH
    have hcommXmap : (⁅L, XH⁆).map q = L.map q := by
      rw [Subgroup.map_commutator, hFmap, hXHmap, hDcomm]
    have hcommX : ⁅L, XH⁆ = L :=
      eq_of_le_of_le_of_map_eq_of_inf_ker_eq_bot K ⁅L, XH⁆ L q
        (hcommXL.trans hLleK) hLleK hcommXmap
        (inf_ker_eq_bot_of_natCard_map_eq K q hKcard)
    refine ⟨?_, hfullAmbient⟩
    calc
        ⁅F, Subgroup.zpowers x⁆ = (⁅L, XH⁆).map H.subtype := by
          rw [Subgroup.map_commutator,
            Subgroup.map_subgroupOf_eq_of_le hFH]
          change ⁅F, Subgroup.zpowers x⁆ =
            ⁅F, (Subgroup.zpowers xH).map H.subtype⁆
          rw [MonoidHom.map_zpowers]
          rfl
        _ = L.map H.subtype :=
          congrArg (fun Y : Subgroup H => Y.map H.subtype) hcommX
        _ = F := Subgroup.map_subgroupOf_eq_of_le hFH
  exact ⟨F, hFW, hFW.trans (local_commutator_le_oddCore S A), hFmap,
    hFcard, hFnorm, hSnorm, Aᵢ, hAleAᵢ, hAᵢleS, hAᵢcard,
    hAᵢmap, hQcard, hDcomm, hfixed, hfullFixed, hWAcomm, hpointComm⟩

/-- In the local direct product, the intersections of the factors with the
Sylow two-subgroup generate that Sylow subgroup.  This is the quotient-level
generation statement that lets the lifted order-four subgroups generate
`S/A` simultaneously. -/
public theorem local_factor_coordinates_generate_sylow
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (P : Sylow 2 G) (F : Finset (Subgroup G))
    (hEF : ∀ E : Subgroup G, E ∈ F →
      IsSL2Two (↑E) ∧
        oneOmega (G := G) (V := V)
          ((commutator (↑E)).map E.subtype))
    (hprod : IsInternalDirectProduct
      (oddCore G ⊔ (P : Subgroup G)) F)
    (hcoord : ∀ E : Subgroup G, E ∈ F →
      Nat.card (↥((P : Subgroup G) ⊓ E)) = 2) :
    (P : Subgroup G) =
      ⨆ E : {E : Subgroup G // E ∈ F},
        (P : Subgroup G) ⊓ (E : Subgroup G) := by
  classical
  let R : Subgroup G :=
    ⨆ E : {E : Subgroup G // E ∈ F},
      (P : Subgroup G) ⊓ (E : Subgroup G)
  have hRleP : R ≤ (P : Subgroup G) := by
    dsimp only [R]
    exact iSup_le fun E => inf_le_left
  have hfactor
      (E : Subgroup G) (hE : E ∈ F) :
      E = (commutator (↑E)).map E.subtype ⊔
        ((P : Subgroup G) ⊓ E) := by
    let D : Subgroup G := (commutator (↑E)).map E.subtype
    let Q : Subgroup G := (P : Subgroup G) ⊓ E
    have hDcard : Nat.card D = 3 := (hEF E hE).2.2.1
    have hQcard : Nat.card Q = 2 := hcoord E hE
    have hDleE : D ≤ E := Subgroup.map_subtype_le (commutator E)
    have hQleE : Q ≤ E := inf_le_right
    let DE : Subgroup E := commutator E
    let QE : Subgroup E := Q.subgroupOf E
    have hDEmap : DE.map E.subtype = D := by
      rfl
    have hDEcard : Nat.card DE = 3 := by
      calc
        Nat.card DE = Nat.card (DE.map E.subtype) :=
          (Nat.card_congr
            (Subgroup.equivMapOfInjective DE E.subtype
              E.subtype_injective).toEquiv)
        _ = Nat.card D := by rw [hDEmap]
        _ = 3 := hDcard
    have hQEcard : Nat.card QE = 2 := by
      rw [natCard_subgroupOf_eq Q E hQleE]
      exact hQcard
    let _ : DE.Normal := by
      dsimp only [DE]
      infer_instance
    have hdisj : Disjoint DE QE := by
      apply Subgroup.disjoint_of_coprime_natCard
      rw [hDEcard, hQEcard]
      decide
    have hcompl := isComplement'_subgroupOf_sup_of_disjoint DE QE hdisj
    have hcardSup : Nat.card ↥(DE ⊔ QE) = 6 := by
      have hc := hcompl.card_mul_card
      rw [natCard_subgroupOf_eq DE (DE ⊔ QE) le_sup_left,
        natCard_subgroupOf_eq QE (DE ⊔ QE) le_sup_right,
        hDEcard, hQEcard] at hc
      omega
    have hsupTop : DE ⊔ QE = ⊤ :=
      Subgroup.eq_of_le_of_card_ge le_top (by
        rw [Subgroup.card_top, isSL2Two_card (hEF E hE).1, hcardSup])
    calc
      E = (⊤ : Subgroup E).map E.subtype := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      _ = (DE ⊔ QE).map E.subtype := by rw [hsupTop]
      _ = D ⊔ Q := by
        rw [Subgroup.map_sup, hDEmap,
          Subgroup.map_subgroupOf_eq_of_le hQleE]
  have hjoinLe : oddCore G ⊔ (P : Subgroup G) ≤ oddCore G ⊔ R := by
    rw [hprod.1]
    refine iSup_le ?_
    intro E
    rw [hfactor (E : Subgroup G) E.property]
    apply sup_le
    · exact (hEF (E : Subgroup G) E.property).2.1.trans le_sup_left
    · exact (le_iSup
        (fun K : {K : Subgroup G // K ∈ F} =>
          (P : Subgroup G) ⊓ (K : Subgroup G)) E).trans le_sup_right
  have hjoinEq : oddCore G ⊔ (P : Subgroup G) = oddCore G ⊔ R := by
    apply le_antisymm hjoinLe
    exact sup_le le_sup_left (hRleP.trans le_sup_right)
  have hcop : Nat.Coprime (Nat.card (P : Subgroup G))
      (Nat.card (oddCore G)) := by
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    rw [hn]
    exact (pPrimeCore_coprime_card (G := G) (p := 2)).pow_left n
  have hinf : (P : Subgroup G) ⊓ oddCore G = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  apply le_antisymm
  · intro p hp
    have hpJoin : p ∈ oddCore G ⊔ R := by
      rw [← hjoinEq]
      exact (show (P : Subgroup G) ≤
        oddCore G ⊔ (P : Subgroup G) from le_sup_right) hp
    let _ : (oddCore G).Normal := pPrimeCore_normal
    rcases Subgroup.mem_sup_of_normal_left.mp hpJoin with
      ⟨w, hw, r, hr, hwr⟩
    have hwP : w ∈ (P : Subgroup G) := by
      have hrP : r ∈ (P : Subgroup G) := hRleP hr
      have hweq : w = p * r⁻¹ := by
        calc
          w = (w * r) * r⁻¹ := by simp
          _ = p * r⁻¹ := by rw [hwr]
      rw [hweq]
      exact (P : Subgroup G).mul_mem hp ((P : Subgroup G).inv_mem hrP)
    have hwone : w = 1 := by
      have hwInf : w ∈ (P : Subgroup G) ⊓ oddCore G := ⟨hwP, hw⟩
      rw [hinf] at hwInf
      exact hwInf
    rw [hwone] at hwr
    have hrp : r = p := by simpa using hwr
    rwa [← hrp]
  · exact hRleP

end Stellmacher.SectionOne.RankOneThreeGroupAssembly
