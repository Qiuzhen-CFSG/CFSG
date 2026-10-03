module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Basic
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaGeneration
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Defs
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.LocalLifts

/-!
# Compatible generic coordinates and omega families

The lifted coordinates retain the same family through the quotient and ambient group. Generic containment identifies their four-point action modules and makes each lifted factor an ambient omega factor.

This module supports the rank-at-least-two case of Stellmacher (1.6).
The action is on an elementary abelian two-group; the local hypotheses and
minimal-offender conditions are explicit in the declarations that use them.
Source: `refs/latex/stellmacher-n-group.tex`, proof of (1.6), journal pp.18–19.
-/

open scoped Pointwise symmDiff

namespace Stellmacher.SectionOne.RankOneThreeGroupAssembly

universe u v

/-- Passing from an ambient subgroup to the same subgroup inside an
intermediate actor group does not change its fixed-point subgroup. -/
public theorem fixedPoints_subgroup_subgroupOf_eq
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    (H A : Subgroup G) (hAH : A ≤ H) :
    FixedPoints.subgroup (A.subgroupOf H) V =
      FixedPoints.subgroup A V := by
  ext v
  rw [FixedPoints.mem_subgroup, FixedPoints.mem_subgroup]
  constructor
  · intro hv a
    let aH : A.subgroupOf H := ⟨⟨a, hAH a.property⟩, a.property⟩
    simpa only [Subgroup.smul_def, aH] using hv aH
  · intro hv a
    simpa only [Subgroup.smul_def] using
      hv ⟨((a : H) : G), a.property⟩

public structure LocalGenericCoordinateFamily
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V] (W S A : Subgroup G) where
  index : Type u
  index_finite : Finite index
  factor : index → Subgroup G
  coordinate : index → Subgroup G
  factor_generated : W = ⨆ i, factor i
  factor_injective : Function.Injective factor
  factor_omega : ∀ i, oneOmega (G := G) (V := V) (factor i)
  factor_normalized : ∀ i, S ≤ Subgroup.normalizer (factor i)
  A_le_coordinate : ∀ i, A ≤ coordinate i
  coordinate_le_S : ∀ i, coordinate i ≤ S
  coordinate_card_four : ∀ i, Nat.card (coordinate i) = 4
  local_commutator : ∀ i, ⁅W, coordinate i⁆ = factor i
  point_coordinate : ∀ i x, x ∈ coordinate i → x ∉ A →
    ⁅factor i, Subgroup.zpowers x⁆ = factor i ∧
      (Nat.card (FixedPoints.subgroup A V) : ℚ) /
        Nat.card (↥(FixedPoints.subgroup A V ⊓
          FixedPoints.subgroup (Subgroup.zpowers x) V)) = 2
  coordinate_generated : S = A ⊔ ⨆ i, coordinate i

/-- The local generic factors and their lifted order-four Sylow coordinates
can be chosen simultaneously.  The coordinates generate `S` modulo `A`,
and every point outside `A` retains the local full fixed-index equation. -/
public theorem exists_local_generic_coordinate_family
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S A : Subgroup G)
    (hlocal : RankOneAssemblyLocalHypothesis (G := G) (V := V) S)
    (hAmax : oneAmax (G := G) (V := V) S A)
    (hAcard : Nat.card A = 2)
    (hgeneric : RankOneLocalGenericHypothesis
      (G := G) (V := V) S A) :
    Nonempty (LocalGenericCoordinateFamily (G := G) (V := V)
      ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆ S A) := by
  classical
  let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
  let H := W_A ⊔ S
  let A_H := A.subgroupOf H
  obtain ⟨hA_H, P, Fbar, hP, hcore, hcard, hFbar, hprod, hgen, hlift⟩ :=
    local_hypothesis_gives_derived_factor_lifts S A hlocal hAmax hAcard
  let _ : A_H.Normal := hA_H
  let V_A := FixedPoints.subgroup A_H V
  let _ : IsElementaryAbelian 2 V_A := isElementaryAbelian_subgroup V_A
  let D (E : {E : Subgroup (H ⧸ A_H) // E ∈ Fbar}) :
      Subgroup (H ⧸ A_H) :=
    (commutator (E : Subgroup (H ⧸ A_H))).map E.val.subtype
  choose liftF hliftWA hliftCore hliftMap hliftCard hliftNormal
      hliftSnormal coordinate hAleCoordinate hcoordinateLeS
      hcoordinateCard hcoordinateMap hQcard _hDcomm _hfixed _hfullFixed
      hlocalComm hpoint using
    fun E : {E : Subgroup (H ⧸ A_H) // E ∈ Fbar} =>
      hlift (E : Subgroup (H ⧸ A_H)) E.property
  have hliftLocalOmega
      (E : {E : Subgroup (H ⧸ A_H) // E ∈ Fbar}) :
      oneOmega (G := H ⧸ A_H) (V := V_A)
        ((liftF E).subgroupOf H |>.map (QuotientGroup.mk' A_H)) := by
    rw [hliftMap E]
    exact (hFbar (E : Subgroup (H ⧸ A_H)) E.property).2
  have hfixedEq : V_A = FixedPoints.subgroup A V :=
    fixedPoints_subgroup_subgroupOf_eq H A (hAmax.1.trans le_sup_right)
  have hliftCoordinate
      (E : {E : Subgroup (H ⧸ A_H) // E ∈ Fbar}) :
      RankOneLocalFactorCoordinate (G := G) (V := V)
        S A (liftF E) := by
    refine ⟨coordinate E, hAleCoordinate E, hcoordinateLeS E,
      hcoordinateCard E, hlocalComm E, ?_⟩
    intro x hx hxA
    have hp := hpoint E x hx hxA
    change ⁅liftF E, Subgroup.zpowers x⁆ = liftF E ∧
      (Nat.card V_A : ℚ) /
        Nat.card (↥(V_A ⊓ FixedPoints.subgroup
          (Subgroup.zpowers x) V)) = 2 at hp
    rwa [hfixedEq] at hp
  have hliftGeneric
      (E : {E : Subgroup (H ⧸ A_H) // E ∈ Fbar}) :
      commutatorAction (liftF E) V ≤ V_A :=
    hgeneric hA_H (liftF E) (hliftWA E) (hliftCard E)
      (hliftLocalOmega E) (hliftCoordinate E)
  have hliftAmbientOmega
      (E : {E : Subgroup (H ⧸ A_H) // E ∈ Fbar}) :
      oneOmega (G := G) (V := V) (liftF E) := by
    exact oneOmega_of_local_lift_of_commutator_le_fixedPoints
      H A_H (liftF E) (hliftWA E |>.trans le_sup_left) (hliftCore E)
      (hliftCard E) (D E)
      ((hFbar (E : Subgroup (H ⧸ A_H)) E.property).2)
      (hliftMap E) (hliftGeneric E)
  let q : H →* H ⧸ A_H := QuotientGroup.mk' A_H
  let K : Subgroup H := W_A.subgroupOf H
  let L : Subgroup H :=
    ⨆ E : {E : Subgroup (H ⧸ A_H) // E ∈ Fbar},
      (liftF E).subgroupOf H
  have hWAleH : W_A ≤ H := le_sup_left
  have hliftH
      (E : {E : Subgroup (H ⧸ A_H) // E ∈ Fbar}) : liftF E ≤ H :=
    (hliftWA E).trans hWAleH
  have hLleK : L ≤ K := by
    dsimp only [L]
    exact iSup_le fun E x hx => hliftWA E hx
  have hKcard : Nat.card (K.map q) = Nat.card K := by
    change Nat.card ((W_A.subgroupOf H).map (QuotientGroup.mk' A_H)) =
      Nat.card (W_A.subgroupOf H)
    exact hcard.trans (natCard_subgroupOf_eq W_A H hWAleH).symm
  have hLmap : L.map q = K.map q := by
    calc
      L.map q = ⨆ E : {E : Subgroup (H ⧸ A_H) // E ∈ Fbar},
          ((liftF E).subgroupOf H).map q := by
        dsimp only [L]
        rw [Subgroup.map_iSup]
      _ = ⨆ E : {E : Subgroup (H ⧸ A_H) // E ∈ Fbar}, D E := by
        congr 1
        funext E
        exact hliftMap E
      _ = oddCore (H ⧸ A_H) := hgen.symm
      _ = K.map q := hcore
  have hLK : L = K :=
    eq_of_le_of_map_eq_of_inf_ker_eq_bot K L q hLleK hLmap
      (inf_ker_eq_bot_of_natCard_map_eq K q hKcard)
  have hgenerated : W_A =
      ⨆ E : {E : Subgroup (H ⧸ A_H) // E ∈ Fbar}, liftF E := by
    calc
      W_A = K.map H.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hWAleH).symm
      _ = L.map H.subtype :=
        congrArg (fun X : Subgroup H => X.map H.subtype) hLK.symm
      _ = ⨆ E : {E : Subgroup (H ⧸ A_H) // E ∈ Fbar},
          ((liftF E).subgroupOf H).map H.subtype := by
        dsimp only [L]
        rw [Subgroup.map_iSup]
      _ = ⨆ E : {E : Subgroup (H ⧸ A_H) // E ∈ Fbar}, liftF E := by
        congr 1
        funext E
        exact Subgroup.map_subgroupOf_eq_of_le (hliftH E)
  have hliftInjective : Function.Injective liftF := by
    intro E K hEK
    apply Subtype.ext
    by_contra hval
    have hdisj := hprod.2.2.1
      (E : Subgroup (H ⧸ A_H)) E.property
      (K : Subgroup (H ⧸ A_H)) K.property hval
    have hDleE : D E ≤ (E : Subgroup (H ⧸ A_H)) :=
      Subgroup.map_subtype_le (commutator E)
    have hDleK : D E ≤ (K : Subgroup (H ⧸ A_H)) := by
      rw [show D E = D K by
        dsimp only [D]
        rw [← hliftMap E, ← hliftMap K, hEK]]
      exact Subgroup.map_subtype_le (commutator K)
    have hDbot : D E = ⊥ := by
      apply le_antisymm
      · exact (le_inf hDleE hDleK).trans hdisj.eq_bot.le
      · exact bot_le
    have hDcard : Nat.card (D E) = 3 := by
      dsimp only [D]
      exact (hFbar (E : Subgroup (H ⧸ A_H)) E.property).2.2.1
    rw [hDbot] at hDcard
    norm_num at hDcard
  have hPgenerated : (P : Subgroup (H ⧸ A_H)) =
      ⨆ E : {E : Subgroup (H ⧸ A_H) // E ∈ Fbar},
        (P : Subgroup (H ⧸ A_H)) ⊓ (E : Subgroup (H ⧸ A_H)) :=
    local_factor_coordinates_generate_sylow P Fbar hFbar hprod
      (fun E hE => hQcard ⟨E, hE⟩)
  let R : Subgroup G :=
    A ⊔ ⨆ E : {E : Subgroup (H ⧸ A_H) // E ∈ Fbar}, coordinate E
  have hRleS : R ≤ S := by
    apply sup_le hAmax.1
    exact iSup_le hcoordinateLeS
  have hRleH : R ≤ H := hRleS.trans le_sup_right
  have hSleH : S ≤ H := le_sup_right
  have hRmap : (R.subgroupOf H).map q =
      (P : Subgroup (H ⧸ A_H)) := by
    apply le_antisymm
    · rw [hP]
      exact Subgroup.map_mono (fun x hx => hRleS hx)
    · rw [hPgenerated]
      refine iSup_le ?_
      intro E
      rw [← hcoordinateMap E]
      apply Subgroup.map_mono
      intro x hx
      exact (show coordinate E ≤ R from
        (le_iSup (fun i => coordinate i) E).trans le_sup_right) hx
  have hkerLeR : q.ker ≤ R.subgroupOf H := by
    rw [show q.ker = A_H from QuotientGroup.ker_mk' A_H]
    intro a ha
    exact (show A ≤ R from le_sup_left) ha
  have hkerLeS : q.ker ≤ S.subgroupOf H := by
    rw [show q.ker = A_H from QuotientGroup.ker_mk' A_H]
    intro a ha
    exact hAmax.1 ha
  have hRsubEq : R.subgroupOf H = S.subgroupOf H := by
    calc
      R.subgroupOf H = ((R.subgroupOf H).map q).comap q :=
        (Subgroup.comap_map_eq_self hkerLeR).symm
      _ = ((S.subgroupOf H).map q).comap q := by rw [hRmap, hP]
      _ = S.subgroupOf H := Subgroup.comap_map_eq_self hkerLeS
  have hcoordinateGenerated : S = R := by
    calc
      S = (S.subgroupOf H).map H.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hSleH).symm
      _ = (R.subgroupOf H).map H.subtype := by rw [hRsubEq]
      _ = R := Subgroup.map_subgroupOf_eq_of_le hRleH
  let hindexFinite : Finite {E : Subgroup (H ⧸ A_H) // E ∈ Fbar} :=
    inferInstance
  refine ⟨⟨{E : Subgroup (H ⧸ A_H) // E ∈ Fbar}, hindexFinite,
    liftF, coordinate, hgenerated, hliftInjective, hliftAmbientOmega,
    hliftSnormal,
    hAleCoordinate, hcoordinateLeS, hcoordinateCard, hlocalComm, ?_, ?_⟩⟩
  · intro E x hx hxA
    have hp := hpoint E x hx hxA
    change ⁅liftF E, Subgroup.zpowers x⁆ = liftF E ∧
      (Nat.card V_A : ℚ) /
        Nat.card (↥(V_A ⊓ FixedPoints.subgroup
          (Subgroup.zpowers x) V)) = 2 at hp
    rw [hfixedEq] at hp
    exact hp
  · simpa only [R] using hcoordinateGenerated

public structure LocalGenericOmegaFamily
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V] (W S : Subgroup G) where
  index : Type u
  factor : index → Subgroup G
  generated : W = ⨆ i, factor i
  omega : ∀ i, oneOmega (G := G) (V := V) (factor i)
  normalized : ∀ i, S ≤ Subgroup.normalizer (factor i)

/-- In the generic case, the lifted quotient factors form an ambient
`oneOmega` family which generates `W_A`, and every factor is normalized by
`S`. -/
public theorem exists_local_generic_omega_family
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S A : Subgroup G)
    (hlocal : RankOneAssemblyLocalHypothesis (G := G) (V := V) S)
    (hAmax : oneAmax (G := G) (V := V) S A)
    (hAcard : Nat.card A = 2)
    (hgeneric : RankOneLocalGenericHypothesis
      (G := G) (V := V) S A) :
    Nonempty (LocalGenericOmegaFamily (G := G) (V := V)
      ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆ S) := by
  classical
  let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
  let H := W_A ⊔ S
  let A_H := A.subgroupOf H
  obtain ⟨hA_H, P, Fbar, hP, hcore, hcard, hFbar, hprod, hgen, hlift⟩ :=
    local_hypothesis_gives_derived_factor_lifts S A hlocal hAmax hAcard
  let _ : A_H.Normal := hA_H
  let V_A := FixedPoints.subgroup A_H V
  let D (E : {E : Subgroup (H ⧸ A_H) // E ∈ Fbar}) :
      Subgroup (H ⧸ A_H) :=
    (commutator (E : Subgroup (H ⧸ A_H))).map E.val.subtype
  choose liftF hliftWA hliftCore hliftMap hliftCard hliftNormal hliftSnormal
      coordinate hAleCoordinate hcoordinateLeS hcoordinateCard
      _hcoordinateMap _hQcard _hDcomm _hfixed _hfullFixed
      hlocalComm hpoint using
    fun E : {E : Subgroup (H ⧸ A_H) // E ∈ Fbar} =>
      hlift (E : Subgroup (H ⧸ A_H)) E.property
  have hliftOmega (E : {E : Subgroup (H ⧸ A_H) // E ∈ Fbar}) :
      oneOmega (G := H ⧸ A_H) (V := V_A) (D E) := by
    exact (hFbar (E : Subgroup (H ⧸ A_H)) E.property).2
  have hliftLocalOmega
      (E : {E : Subgroup (H ⧸ A_H) // E ∈ Fbar}) :
      oneOmega (G := H ⧸ A_H) (V := V_A)
        ((liftF E).subgroupOf H |>.map (QuotientGroup.mk' A_H)) := by
    rw [hliftMap E]
    exact hliftOmega E
  have hfixedEq : V_A = FixedPoints.subgroup A V :=
    fixedPoints_subgroup_subgroupOf_eq H A (hAmax.1.trans le_sup_right)
  have hliftCoordinate
      (E : {E : Subgroup (H ⧸ A_H) // E ∈ Fbar}) :
      RankOneLocalFactorCoordinate (G := G) (V := V)
        S A (liftF E) := by
    refine ⟨coordinate E, hAleCoordinate E, hcoordinateLeS E,
      hcoordinateCard E, hlocalComm E, ?_⟩
    intro x hx hxA
    have hp := hpoint E x hx hxA
    change ⁅liftF E, Subgroup.zpowers x⁆ = liftF E ∧
      (Nat.card V_A : ℚ) /
        Nat.card (↥(V_A ⊓ FixedPoints.subgroup
          (Subgroup.zpowers x) V)) = 2 at hp
    rwa [hfixedEq] at hp
  have hliftGeneric
      (E : {E : Subgroup (H ⧸ A_H) // E ∈ Fbar}) :
      commutatorAction (liftF E) V ≤ V_A := by
    exact hgeneric hA_H (liftF E) (hliftWA E) (hliftCard E)
      (hliftLocalOmega E) (hliftCoordinate E)
  have hliftAmbientOmega
      (E : {E : Subgroup (H ⧸ A_H) // E ∈ Fbar}) :
      oneOmega (G := G) (V := V) (liftF E) := by
    exact oneOmega_of_local_lift_of_commutator_le_fixedPoints
      H A_H (liftF E) (hliftWA E |>.trans le_sup_left) (hliftCore E)
      (hliftCard E) (D E) (hliftOmega E) (hliftMap E)
      (hliftGeneric E)
  let q : H →* H ⧸ A_H := QuotientGroup.mk' A_H
  let K : Subgroup H := W_A.subgroupOf H
  let L : Subgroup H :=
    ⨆ E : {E : Subgroup (H ⧸ A_H) // E ∈ Fbar},
      (liftF E).subgroupOf H
  have hWAleH : W_A ≤ H := le_sup_left
  have hliftH
      (E : {E : Subgroup (H ⧸ A_H) // E ∈ Fbar}) : liftF E ≤ H :=
    (hliftWA E).trans hWAleH
  have hLleK : L ≤ K := by
    dsimp only [L]
    refine iSup_le ?_
    intro E x hx
    exact hliftWA E hx
  have hKcard : Nat.card (K.map q) = Nat.card K := by
    change Nat.card ((W_A.subgroupOf H).map (QuotientGroup.mk' A_H)) =
      Nat.card (W_A.subgroupOf H)
    exact hcard.trans (natCard_subgroupOf_eq W_A H hWAleH).symm
  have hLmap : L.map q = K.map q := by
    calc
      L.map q = ⨆ E : {E : Subgroup (H ⧸ A_H) // E ∈ Fbar},
          ((liftF E).subgroupOf H).map q := by
        dsimp only [L]
        rw [Subgroup.map_iSup]
      _ = ⨆ E : {E : Subgroup (H ⧸ A_H) // E ∈ Fbar}, D E := by
        congr 1
        funext E
        exact hliftMap E
      _ = oddCore (H ⧸ A_H) := hgen.symm
      _ = K.map q := hcore
  have hLK : L = K :=
    eq_of_le_of_map_eq_of_inf_ker_eq_bot K L q hLleK hLmap
      (inf_ker_eq_bot_of_natCard_map_eq K q hKcard)
  have hgenerated : W_A =
      ⨆ E : {E : Subgroup (H ⧸ A_H) // E ∈ Fbar}, liftF E := by
    calc
      W_A = K.map H.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hWAleH).symm
      _ = L.map H.subtype := congrArg (fun X : Subgroup H => X.map H.subtype) hLK.symm
      _ = ⨆ E : {E : Subgroup (H ⧸ A_H) // E ∈ Fbar},
          ((liftF E).subgroupOf H).map H.subtype := by
        dsimp only [L]
        rw [Subgroup.map_iSup]
      _ = ⨆ E : {E : Subgroup (H ⧸ A_H) // E ∈ Fbar}, liftF E := by
        congr 1
        funext E
        exact Subgroup.map_subgroupOf_eq_of_le (hliftH E)
  exact ⟨⟨{E : Subgroup (H ⧸ A_H) // E ∈ Fbar}, liftF,
    hgenerated, hliftAmbientOmega, hliftSnormal⟩⟩

end Stellmacher.SectionOne.RankOneThreeGroupAssembly
