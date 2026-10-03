module

public import Stellmacher.SectionThree.ThreeNineLocalOneSeven
public import Stellmacher.ElementaryAbelianMaxJWeakClosure
public import Stellmacher.MaxElementaryOffender
public import Stellmacher.ElementaryAbelianMaxJMap
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.LocalFamilies
public import Stellmacher.SectionThree.LemmaThreeFour
public import Stellmacher.SectionThree.LemmaThreeSeven

/-!
# Ambient promotion of the local residual in Stellmacher (3.9)

Let `q : H → H / C_H(V)` be the faithful quotient action occurring in
Stellmacher (3.9), and let `R` be the image of `O²(P)`.  Under the
source hypotheses `J(S) = J(T)`, `q(S) ∩ O₂(H / C_H(V)) = 1`, and
`[R, q(J(T))] = R`, this module proves that `R ≤ O₃(H / C_H(V))`.

The proof applies the local (1.7) package to
`L = O₂'(F(H / C_H(V))) R q(J(T))`.  The barred two-core condition makes
`O₂(L)` trivial, while the quotient conjugation action on `V` is faithful.
Images of maximal elementary abelian subgroups of `T` form an offender
family generating the local Thompson image, so (1.7) places `R` in the
derived subgroup of a selected internal product of `SL₂(2)` factors.

For the ambient promotion, each selected factor-derived `C₃` is normalized
by the odd part of the ambient Fitting subgroup and centralizes the ambient
two-core.  If it is not contained in the odd Fitting part, prime order and
mutual normalization force it to centralize that part as well.  Fitting
self-centralization then puts it in the ambient Fitting subgroup, and hence
in `O₃`.  The direct-product commutator calculation promotes the entire
selected derived subgroup, and therefore `R`, into the ambient three-core.

This is the source jump immediately after the application of (1.7) on
journal page 24 of `refs/files/stellmacher-n-group.pdf`.  The proof uses
neither Stellmacher (2.2) nor an unproved normality or subnormality assertion
for the local group.
-/

open scoped Pointwise

namespace Stellmacher.SectionThree

universe u

private theorem normal_subgroupOf_range_of_normal_promotion
    {G X : Type*} [Group G] [Group X]
    (f : G →* X) (N : Subgroup G) (hN : N.Normal) :
    ((N.map f).subgroupOf f.range).Normal := by
  let fr : G →* f.range := f.rangeRestrict
  have hmap : N.map fr = (N.map f).subgroupOf f.range := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n, hn, rfl⟩
    · rintro ⟨n, hn, hnx⟩
      refine ⟨n, hn, ?_⟩
      exact Subtype.ext hnx
  rw [← hmap]
  exact hN.map fr f.rangeRestrict_surjective

private theorem isSylowSubgroupIn_map_range_promotion
    {G X : Type*} [Group G] [Group X] [Finite G]
    (f : G →* X) (T : Sylow 2 G) :
    IsSylowSubgroupIn ((T : Subgroup G).map f) f.range := by
  let fr : G →* f.range := f.rangeRestrict
  let U : Sylow 2 f.range := T.mapSurjective f.rangeRestrict_surjective
  refine ⟨U, ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map]
  congr 1

private noncomputable abbrev quotientConjugationAction_promotion
    {H : Type u} [Group H] (V : Subgroup H) (hVnormal : V.Normal)
    {X : Type u} [Group X] (q : H →* X) (hq : Function.Surjective q)
    (hker : q.ker = Subgroup.centralizer (V : Set H)) :
    MulDistribMulAction X V := by
  classical
  letI : V.Normal := hVnormal
  let act : H →* MulAut V := MulAut.conjNormal
  have hact : q.ker ≤ act.ker := by
    intro g hg
    rw [hker] at hg
    rw [Subgroup.mem_centralizer_iff] at hg
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change g * (x : H) * g⁻¹ = x
    rw [← hg x x.property, mul_inv_cancel_right]
  exact MulDistribMulAction.compHom V
    (q.liftOfSurjective hq ⟨act, hact⟩)

private theorem quotientConjugationAction_smul_coe_promotion
    {H : Type u} [Group H] (V : Subgroup H) (hVnormal : V.Normal)
    {X : Type u} [Group X] (q : H →* X) (hq : Function.Surjective q)
    (hker : q.ker = Subgroup.centralizer (V : Set H))
    (g : H) (x : V) :
    letI := quotientConjugationAction_promotion V hVnormal q hq hker
    ((q g • x : V) : H) = g * (x : H) * g⁻¹ := by
  let : V.Normal := hVnormal
  change (((q.liftOfSurjective hq _ : X →* MulAut V) (q g)) x : H) = _
  rw [MonoidHom.liftOfRightInverse_comp_apply]
  rfl

private theorem quotientConjugationAction_faithful_promotion
    {H : Type u} [Group H] (V : Subgroup H) (hVnormal : V.Normal)
    {X : Type u} [Group X] (q : H →* X) (hq : Function.Surjective q)
    (hker : q.ker = Subgroup.centralizer (V : Set H)) :
    letI := quotientConjugationAction_promotion V hVnormal q hq hker
    fixingSubgroup X (Set.univ : Set V) = ⊥ := by
  let := quotientConjugationAction_promotion V hVnormal q hq hker
  apply bot_unique
  intro b hb
  obtain ⟨g, rfl⟩ := hq b
  have hg : g ∈ q.ker := by
    rw [hker]
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [mem_fixingSubgroup_iff] at hb
    have hfix := hb ⟨x, hx⟩ (Set.mem_univ _)
    have heq := congrArg Subtype.val hfix
    rw [quotientConjugationAction_smul_coe_promotion
      V hVnormal q hq hker] at heq
    exact (mul_inv_eq_iff_eq_mul.mp heq).symm
  exact hg

private theorem quotientConjugationAction_fixedPoints_image_map_promotion
    {H : Type u} [Group H] (V : Subgroup H) (hVnormal : V.Normal)
    {X : Type u} [Group X] (q : H →* X) (hq : Function.Surjective q)
    (hker : q.ker = Subgroup.centralizer (V : Set H))
    (A : Subgroup H) :
    letI := quotientConjugationAction_promotion V hVnormal q hq hker
    (FixedPoints.subgroup (A.map q) V).map V.subtype =
      V ⊓ Subgroup.centralizer (A : Set H) := by
  let := quotientConjugationAction_promotion V hVnormal q hq hker
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.property, ?_⟩
    change (y : H) ∈ Subgroup.centralizer (A : Set H)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hfix := (FixedPoints.mem_subgroup (M := A.map q) (a := y)).mp hy
      ⟨q a, Subgroup.mem_map_of_mem q ha⟩
    change q a • y = y at hfix
    have heq := congrArg Subtype.val hfix
    rw [quotientConjugationAction_smul_coe_promotion
      V hVnormal q hq hker] at heq
    exact mul_inv_eq_iff_eq_mul.mp heq
  · rintro ⟨hxV, hxA⟩
    refine ⟨⟨x, hxV⟩, ?_, rfl⟩
    change (⟨x, hxV⟩ : V) ∈ FixedPoints.subgroup (A.map q) V
    rw [FixedPoints.mem_subgroup]
    intro a
    obtain ⟨a₀, ha₀, heq⟩ := a.property
    apply Subtype.ext
    change ((a.val • (⟨x, hxV⟩ : V) : V) : H) = x
    rw [← heq, quotientConjugationAction_smul_coe_promotion
      V hVnormal q hq hker]
    change x ∈ Subgroup.centralizer (A : Set H) at hxA
    rw [Subgroup.mem_centralizer_iff] at hxA
    rw [hxA a₀ ha₀, mul_inv_cancel_right]

private theorem quotientConjugationAction_fixedPoints_card_promotion
    {H : Type u} [Group H] (V : Subgroup H) (hVnormal : V.Normal)
    {X : Type u} [Group X] (q : H →* X) (hq : Function.Surjective q)
    (hker : q.ker = Subgroup.centralizer (V : Set H))
    (A : Subgroup H) :
    letI := quotientConjugationAction_promotion V hVnormal q hq hker
    Nat.card (FixedPoints.subgroup (A.map q) V) =
      Nat.card (V ⊓ Subgroup.centralizer (A : Set H) : Subgroup H) := by
  let := quotientConjugationAction_promotion V hVnormal q hq hker
  rw [← quotientConjugationAction_fixedPoints_image_map_promotion
      V hVnormal q hq hker A,
    Subgroup.card_map_of_injective V.subtype_injective]

private theorem maxElementary_map_mem_oneA_promotion
    {H : Type u} [Group H] [Finite H]
    (T : Sylow 2 H) (V : Subgroup H) (hVnormal : V.Normal)
    [IsElementaryAbelian 2 V] (hVT : V ≤ (T : Subgroup H))
    {X : Type u} [Group X] [Finite X]
    (q : H →* X) (hq : Function.Surjective q)
    (hker : q.ker = Subgroup.centralizer (V : Set H))
    (A : Subgroup H)
    (hA : A ∈ elementaryAbelianMaxSubgroups (T : Subgroup H)) :
    letI := quotientConjugationAction_promotion V hVnormal q hq hker
    SectionOne.oneA (V := V) ((T : Subgroup H).map q) (A.map q) := by
  let := quotientConjugationAction_promotion V hVnormal q hq hker
  have hbound := maxElementary_card_le_fixed_mul_image
    (T : Subgroup H) V A hVT hA q hker
  rw [← quotientConjugationAction_fixedPoints_card_promotion
      V hVnormal q hq hker A] at hbound
  refine ⟨Subgroup.map_mono hA.1, hA.2.1.map q, ?_⟩
  unfold SectionOne.m
  have hpos : 0 < (Nat.card (FixedPoints.subgroup (A.map q) V) : ℚ) *
      (Nat.card (A.map q) : ℚ) := by
    exact_mod_cast Nat.mul_pos Nat.card_pos Nat.card_pos
  apply (div_le_one hpos).mpr
  exact_mod_cast hbound

private theorem subgroup_le_centralizer_twoCore_of_normalized_by_sylow_promotion
    {G : Type u} [Group G] [Finite G]
    (T : Sylow 2 G) (S J : Subgroup G)
    (hJS : J ≤ S) (hTnormJ : (T : Subgroup G) ≤ Subgroup.normalizer (J : Set G))
    (hSCore : S ⊓ pCore 2 G = ⊥) :
    J ≤ Subgroup.centralizer (pCore 2 G : Set G) := by
  have hOT : pCore 2 G ≤ (T : Subgroup G) :=
    (pCore_isPGroup (p := 2) (G := G)).le_sylow_of_normal T
  have hcommJ : ⁅J, pCore 2 G⁆ ≤ J :=
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (hOT.trans hTnormJ))
  have hcommO : ⁅J, pCore 2 G⁆ ≤ pCore 2 G :=
    Subgroup.commutator_le_right J (pCore 2 G)
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  apply le_bot_iff.mp
  exact (le_inf (hcommJ.trans hJS) hcommO).trans hSCore.le

private theorem oddFitting_le_centralizer_twoCore_promotion
    {G : Type u} [Group G] [Finite G] :
    (pPrimeCore 2 (fittingSubgroup G)).map (fittingSubgroup G).subtype ≤
      Subgroup.centralizer (pCore 2 G : Set G) := by
  let O : Subgroup G := pCore 2 G
  let Fit : Subgroup G := fittingSubgroup G
  let OF : Subgroup Fit := O.subgroupOf Fit
  have hOFnormal : OF.Normal := by
    dsimp [OF, O, Fit]
    exact (pCore_normal (G := G) (p := 2)).subgroupOf (fittingSubgroup G)
  have hOFp : IsPGroup 2 OF :=
    (pCore_isPGroup (G := G) (p := 2)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (pCore_le_fitting G 2)).symm
  have hOFcore : OF ≤ pCore 2 Fit := le_sSup ⟨hOFnormal, hOFp⟩
  have hm := Subgroup.map_mono (f := Fit.subtype) hOFcore
  have hOmap : OF.map Fit.subtype = O :=
    Subgroup.map_subgroupOf_eq_of_le (pCore_le_fitting G 2)
  rw [hOmap] at hm
  exact (pPrimeCore_map_le_centralizer_pCore_map (p := 2) Fit).trans
    (Subgroup.centralizer_le hm)

private theorem oneA_subgroupOf_promotion
    {G V : Type u} [Group G] [Group V] [Finite V]
    [MulDistribMulAction G V] (L A S : Subgroup G) (hAL : A ≤ L)
    (U : Subgroup L) (hAU : A.subgroupOf L ≤ U)
    (hA : SectionOne.oneA (V := V) S A) :
    SectionOne.oneA (V := V) U (A.subgroupOf L) := by
  let : IsElementaryAbelian 2 A := hA.2.1
  refine ⟨hAU, IsElementaryAbelian.subgroupOf hAL, ?_⟩
  unfold SectionOne.m
  rw [SectionOne.RankOneThreeGroupAssembly.fixedPoints_subgroup_subgroupOf_eq L A hAL,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv]
  exact hA.2.2

private theorem fixingSubgroup_subgroup_eq_bot_promotion
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    (L : Subgroup G)
    (hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥) :
    fixingSubgroup L (Set.univ : Set V) = ⊥ := by
  apply bot_unique
  intro x hx
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  have hxG : (x : G) ∈ fixingSubgroup G (Set.univ : Set V) := by
    rw [mem_fixingSubgroup_iff]
    intro v _
    rw [mem_fixingSubgroup_iff] at hx
    simpa only [Subgroup.smul_def] using hx v (Set.mem_univ v)
  rw [hfaith, Subgroup.mem_bot] at hxG
  exact hxG

private theorem isPGroup_le_pCore_of_le_fitting_promotion
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Subgroup G) (hPp : IsPGroup p P)
    (hPF : P ≤ fittingSubgroup G) :
    P ≤ pCore p G := by
  classical
  let PF : Subgroup (fittingSubgroup G) := P.subgroupOf (fittingSubgroup G)
  have hPFp : IsPGroup p PF :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPF).symm
  obtain ⟨U, hPFU⟩ := hPFp.exists_le_sylow
  have hUnormal : (U : Subgroup (fittingSubgroup G)).Normal :=
    Group.IsNilpotent.sylow_normal
      (G := fittingSubgroup G)
      (inferInstance : Group.IsNilpotent (fittingSubgroup G)) p U
  have hUchar : (U : Subgroup (fittingSubgroup G)).Characteristic :=
    Sylow.characteristic_of_normal U hUnormal
  have hUmapNormal : ((U : Subgroup (fittingSubgroup G)).map
      (fittingSubgroup G).subtype).Normal := by
    infer_instance
  have hUmapP : IsPGroup p ((U : Subgroup (fittingSubgroup G)).map
      (fittingSubgroup G).subtype) := U.isPGroup'.map (fittingSubgroup G).subtype
  have hUcore : (U : Subgroup (fittingSubgroup G)).map
      (fittingSubgroup G).subtype ≤ pCore p G :=
    le_sSup ⟨hUmapNormal, hUmapP⟩
  have hm := Subgroup.map_mono (f := (fittingSubgroup G).subtype) hPFU
  rw [Subgroup.map_subgroupOf_eq_of_le hPF] at hm
  exact hm.trans hUcore

private theorem fitting_le_twoCore_sup_oddFitting_promotion
    {G : Type u} [Group G] [Finite G] :
    fittingSubgroup G ≤ pCore 2 G ⊔
      (pPrimeCore 2 (fittingSubgroup G)).map
        (fittingSubgroup G).subtype := by
  let Fit : Subgroup G := fittingSubgroup G
  have hgen := nilpotent_top_le_pCore_sup_pPrimeCore
    (Q := Fit) (p := 2) (inferInstance : Group.IsNilpotent Fit)
  have hm := Subgroup.map_mono (f := Fit.subtype) hgen
  rw [Subgroup.map_sup] at hm
  have htopMap : (⊤ : Subgroup Fit).map Fit.subtype = Fit := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [htopMap] at hm
  apply hm.trans
  apply sup_le_sup_right
  exact le_sSup ⟨(by infer_instance),
    (pCore_isPGroup (G := Fit) (p := 2)).map Fit.subtype⟩

private theorem selected_factor_derived_le_threeCore_promotion
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    (L : Subgroup G) [MulDistribMulAction L V]
    (hsolv : Group.IsSolvable G)
    (hLcent : L ≤ Subgroup.centralizer (pCore 2 G : Set G))
    (hWL : (pPrimeCore 2 (fittingSubgroup G)).map
      (fittingSubgroup G).subtype ≤ L)
    (D : Subgroup L) (hD : SectionOne.IsOneSevenFactor (V := V) D) :
    ((commutator D).map D.subtype).map L.subtype ≤ pCore 3 G := by
  classical
  let W : Subgroup G := (pPrimeCore 2 (fittingSubgroup G)).map
    (fittingSubgroup G).subtype
  let A0 : Subgroup L := (commutator D).map D.subtype
  let A : Subgroup G := A0.map L.subtype
  have hWnormal : W.Normal := by
    dsimp [W]
    infer_instance
  let _ : W.Normal := hWnormal
  have hWLnormal : (W.subgroupOf L).Normal := hWnormal.subgroupOf L
  have hWLcop : Nat.Coprime 2 (Nat.card (W.subgroupOf L)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWL).toEquiv,
      show Nat.card W = Nat.card (pPrimeCore 2 (fittingSubgroup G)) by
        exact Subgroup.card_map_of_injective (fittingSubgroup G).subtype_injective]
    exact pPrimeCore_coprime_card
  have hWLodd : W.subgroupOf L ≤ SectionOne.oddCore L :=
    le_sSup ⟨hWLnormal, hWLcop⟩
  have hWnormA0 : W.subgroupOf L ≤ Subgroup.normalizer (A0 : Set L) :=
    hWLodd.trans (SectionOne.oneSevenFactor_oddCore_normalizes_derived D hD)
  have hWnormA : W ≤ Subgroup.normalizer (A : Set G) := by
    have hm := (Subgroup.map_mono (f := L.subtype) hWnormA0).trans
      (Subgroup.le_normalizer_map L.subtype)
    simpa [W, A, A0, Subgroup.map_subgroupOf_eq_of_le hWL] using hm
  have hAnormW : A ≤ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hAcard : Nat.card A = 3 := by
    rw [show Nat.card A = Nat.card A0 by
      exact Subgroup.card_map_of_injective L.subtype_injective]
    exact hD.2.1.2.1
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simp [hAcard])
  have hAfit : A ≤ fittingSubgroup G := by
    let I : Subgroup A := (A ⊓ W).subgroupOf A
    let : Fact (Nat.card A).Prime := ⟨hAcard ▸ Nat.prime_three⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card I with hI | hI
    · have hAWbot : A ⊓ W = ⊥ := by
        have hm := congrArg (Subgroup.map A.subtype) hI
        simpa [I, inf_comm, Subgroup.map_subgroupOf_eq_of_le inf_le_left] using hm
      have hcommAW : ⁅A, W⁆ = ⊥ := by
        apply le_bot_iff.mp
        exact (le_inf
          ((Subgroup.le_normalizer_iff_commutator_le_left).mp hWnormA)
          ((Subgroup.le_normalizer_iff_commutator_le_right).mp hAnormW)).trans
          (by simp [hAWbot])
      have hAcentW : A ≤ Subgroup.centralizer (W : Set G) := by
        rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
        exact hcommAW
      have hAcentO : A ≤ Subgroup.centralizer (pCore 2 G : Set G) :=
        (Subgroup.map_subtype_le A0).trans hLcent
      have hAcentFit : A ≤ Subgroup.centralizer (fittingSubgroup G : Set G) :=
        (Subgroup.le_centralizer_sup_of_le_centralizers hAcentO hAcentW).trans
          (Subgroup.centralizer_le fitting_le_twoCore_sup_oddFitting_promotion)
      exact hAcentFit.trans
        (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv)
    · have hAW : A ≤ W := by
        intro a ha
        have haI : (⟨a, ha⟩ : A) ∈ I := by simp [hI]
        exact haI.2
      exact hAW.trans (by
        dsimp [W]
        exact Subgroup.map_subtype_le _)
  exact isPGroup_le_pCore_of_le_fitting_promotion A hAp hAfit

private theorem selected_product_derived_le_threeCore_promotion
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    (L : Subgroup G) [MulDistribMulAction L V]
    (hsolv : Group.IsSolvable G)
    (hLcent : L ≤ Subgroup.centralizer (pCore 2 G : Set G))
    (hWL : (pPrimeCore 2 (fittingSubgroup G)).map
      (fittingSubgroup G).subtype ≤ L)
    {n : ℕ} (E : Subgroup L) (D : Fin n → Subgroup L)
    (hprod : IsInternalDirectProductFamily E D)
    (hD : ∀ i, SectionOne.IsOneSevenFactor (V := V) (D i)) :
    ((commutator E).map E.subtype).map L.subtype ≤ pCore 3 G := by
  classical
  let P := ∀ i : Fin n, (D i)
  have hcomm : Pairwise (fun i j : Fin n => ∀ x y : L,
      x ∈ D i → y ∈ D j → Commute x y) := by
    intro i j hij x y hx hy
    exact hprod.2.2 i j hij x hx y hy
  let f : P →* L := Subgroup.noncommPiCoprod hcomm
  have hf : f.range = E := (Subgroup.noncommPiCoprod_range).trans hprod.1.symm
  let A (i : Fin n) : Subgroup G :=
    ((commutator (D i)).map (D i).subtype).map L.subtype
  have hAi (i : Fin n) : A i ≤ pCore 3 G :=
    selected_factor_derived_le_threeCore_promotion L hsolv hLcent hWL (D i) (hD i)
  have hderived : ((commutator E).map E.subtype).map L.subtype ≤ ⨆ i, A i := by
    have hmap : (commutator P).map f = (commutator E).map E.subtype := by
      rw [map_commutator_eq, hf, Subgroup.map_subtype_commutator]
    rw [← hmap, Subgroup.map_map]
    rintro x ⟨p, hp, rfl⟩
    change f p ∈ (⨆ i, A i).comap L.subtype
    rw [Subgroup.noncommPiCoprod_apply]
    apply Subgroup.noncommProd_mem
    intro i _
    have hpi : p i ∈ commutator (D i) := by
      have hm := Subgroup.mem_map_of_mem
        (Pi.evalMonoidHom (fun i : Fin n => (D i)) i) hp
      rw [map_commutator_eq] at hm
      exact Subgroup.commutator_mono le_top le_top hm
    change L.subtype (p i) ∈ ⨆ i, A i
    exact (le_iSup A i) (Subgroup.mem_map_of_mem L.subtype
      (Subgroup.mem_map_of_mem (D i).subtype hpi))
  exact hderived.trans (iSup_le hAi)

/-- In the faithful centralizer quotient used in Stellmacher (3.9), the image
of the selected local two-residual lies in the ambient three-core. -/
public theorem threeNine_residual_image_le_threeCore
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P H : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (hPH : P ≤ H) (hsolvP : Group.IsSolvable P)
    (T : Sylow 2 H) (hST : S ≤ sylowAmbient T)
    (hsolvH : Group.IsSolvable H)
    (hJ : elementaryAbelianMaxJ S = elementaryAbelianMaxJ (sylowAmbient T))
    (V C : Subgroup H) (hVnormal : V.Normal)
    (hVelem : IsElementaryAbelian 2 V)
    (hCdef : C = Subgroup.centralizer (V : Set H))
    (hCnormal : C.Normal)
    (hRnotC : ¬ twoResidualAmbient P ≤ C.map H.subtype)
    (hJnotCore : ¬ elementaryAbelianMaxJ S ≤ twoCoreAmbient P)
    (hbarCore :
      letI : C.Normal := hCnormal
      let q : H →* H ⧸ C := QuotientGroup.mk' C
      (S.subgroupOf H).map q ⊓ pCore 2 (H ⧸ C) = ⊥) :
    letI : C.Normal := hCnormal
    let q : H →* H ⧸ C := QuotientGroup.mk' C
    ((twoResidualAmbient P).subgroupOf H).map q ≤ pCore 3 (H ⧸ C) := by
  classical
  let _ : C.Normal := hCnormal
  let _ : V.Normal := hVnormal
  let _ : IsElementaryAbelian 2 V := hVelem
  let _ : Group.IsSolvable H := hsolvH
  let _ : Group.IsSolvable P := hsolvP
  let q : H →* H ⧸ C := QuotientGroup.mk' C
  let X : Type u := H ⧸ C
  let R₀ : Subgroup G := twoResidualAmbient P
  let J₀ : Subgroup G := elementaryAbelianMaxJ S
  let R : Subgroup X := (R₀.subgroupOf H).map q
  let JH : Subgroup H := elementaryAbelianMaxJ (T : Subgroup H)
  let J : Subgroup X := JH.map q
  let SH : Subgroup H := S.subgroupOf H
  let Sbar : Subgroup X := SH.map q
  let PH : Subgroup H := P.subgroupOf H
  let Pbar : Subgroup X := PH.map q
  let W : Subgroup X := (pPrimeCore 2 (fittingSubgroup X)).map
    (fittingSubgroup X).subtype
  let L : Subgroup X := W ⊔ R ⊔ J
  have hSP : S ≤ P := by
    obtain ⟨U, hU⟩ := hP.1.2.1
    rw [← hU]
    exact Subgroup.map_subtype_le _
  have hSH : S ≤ H := hST.trans (Subgroup.map_subtype_le (T : Subgroup H))
  have hR₀H : R₀ ≤ H := (Subgroup.map_subtype_le _).trans hPH
  have hJ₀S : J₀ ≤ S := sSup_le fun A hA => hA.1
  have hJ₀H : J₀ ≤ H := hJ₀S.trans hSH
  have hJHmap : JH.map H.subtype = J₀ := by
    calc
      JH.map H.subtype = elementaryAbelianMaxJ (sylowAmbient T) :=
        (elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective
          (T : Subgroup H)).symm
      _ = J₀ := hJ.symm
  have hJHsub : J₀.subgroupOf H = JH := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hJ₀H, hJHmap]
  have hJleSbar : J ≤ Sbar := by
    dsimp [J, Sbar, SH]
    rw [← hJHsub]
    exact Subgroup.map_mono (by
      intro j hj
      exact Subgroup.mem_subgroupOf.mpr (hJ₀S hj))
  have hTnormJH : (T : Subgroup H) ≤ Subgroup.normalizer (JH : Set H) := by
    intro t ht
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    exact elementaryAbelianMaxJ_map_eq_of_le (T : Subgroup H) (MulAut.conj t) (by
      have hJT : JH ≤ (T : Subgroup H) := sSup_le fun A hA => hA.1
      have hm := Subgroup.map_mono (f := (MulAut.conj t).toMonoidHom) hJT
      have hmapT : (T : Subgroup H).map (MulAut.conj t).toMonoidHom = T :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup H).le_normalizer ht)
      exact hm.trans_eq hmapT)
  let Tbar : Sylow 2 X := T.mapSurjective (QuotientGroup.mk'_surjective C)
  have hTbarNormJ : (Tbar : Subgroup X) ≤ Subgroup.normalizer (J : Set X) := by
    have hm := (Subgroup.map_mono (f := q) hTnormJH).trans
      (Subgroup.le_normalizer_map q)
    change (T : Subgroup H).map q ≤ Subgroup.normalizer (JH.map q : Set (H ⧸ C))
    exact hm
  have hJcentO : J ≤ Subgroup.centralizer (pCore 2 X : Set X) :=
    subgroup_le_centralizer_twoCore_of_normalized_by_sylow_promotion
      Tbar Sbar J hJleSbar hTbarNormJ (by simpa [Sbar, SH, q, X] using hbarCore)
  have hJ₀normalS : (J₀.subgroupOf S).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hJ₀S).mpr
    intro s hs
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    exact elementaryAbelianMaxJ_map_eq_of_le S (MulAut.conj s) (by
      have hm := Subgroup.map_mono (f := (MulAut.conj s).toMonoidHom) hJ₀S
      have hmapS : S.map (MulAut.conj s).toMonoidHom = S :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer hs)
      exact hm.trans_eq hmapS)
  have hcomm₀ : ⁅R₀, J₀⁆ = R₀ := by
    rcases lemma_three_four S h P hP J₀ ⟨hJ₀S, hJ₀normalS⟩ hsolvP with hc | hc
    · exact False.elim (hJnotCore hc)
    · exact hc
  have hcommH : ⁅R₀.subgroupOf H, JH⁆ = R₀.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, hJHmap]
    simpa [Subgroup.map_subgroupOf_eq_of_le hR₀H] using hcomm₀
  have hcommRJ : ⁅R, J⁆ = R := by
    have hm := congrArg (Subgroup.map q) hcommH
    simpa [R, J, Subgroup.map_commutator] using hm
  have hRcentO : R ≤ Subgroup.centralizer (pCore 2 X : Set X) := by
    rw [← hcommRJ]
    exact (Subgroup.commutator_mono le_rfl hJcentO).trans
      (Subgroup.commutator_le_right R (Subgroup.centralizer (pCore 2 X : Set X)))
  have hRJcent : R ⊔ J ≤ Subgroup.centralizer (pCore 2 X : Set X) :=
    sup_le hRcentO hJcentO
  have hLcent : L ≤ Subgroup.centralizer (pCore 2 X : Set X) := by
    exact sup_le (sup_le oddFitting_le_centralizer_twoCore_promotion
      (le_sup_left.trans hRJcent)) (le_sup_right.trans hRJcent)
  have hRne : R ≠ ⊥ := by
    intro hRbot
    apply hRnotC
    intro r hr
    let rH : H := ⟨r, hR₀H hr⟩
    have hrker : rH ∈ q.ker := by
      apply (Subgroup.map_eq_bot_iff (f := q) (R₀.subgroupOf H)).mp
        (by simpa [R] using hRbot)
      exact hr
    rw [QuotientGroup.ker_mk'] at hrker
    exact ⟨rH, hrker, rfl⟩
  have hJne : J ≠ ⊥ := by
    intro hJbot
    apply hRne
    rw [← hcommRJ, hJbot]
    simp
  let fP : P →* X := q.comp (Subgroup.inclusion hPH)
  have hfPrange : fP.range = Pbar := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨⟨p, hPH p.property⟩, p.property, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  have hR₀P : R₀ ≤ P := Subgroup.map_subtype_le _
  have hJ₀P : J₀ ≤ P := hJ₀S.trans hSP
  have hRmapP : (R₀.subgroupOf P).map fP = R := by
    have hmapH : (R₀.subgroupOf P).map (Subgroup.inclusion hPH) =
        R₀.subgroupOf H := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, hR₀P hx⟩, hx, rfl⟩
    rw [show fP = q.comp (Subgroup.inclusion hPH) from rfl,
      ← Subgroup.map_map, hmapH]
  have hJmapP : (J₀.subgroupOf P).map fP = J := by
    have hmapH : (J₀.subgroupOf P).map (Subgroup.inclusion hPH) = JH := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [← hJHsub]
        exact hy
      · intro hx
        rw [← hJHsub] at hx
        exact ⟨⟨x, hJ₀P hx⟩, hx, rfl⟩
    rw [show fP = q.comp (Subgroup.inclusion hPH) from rfl,
      ← Subgroup.map_map, hmapH]
  have hRnormalP : (R₀.subgroupOf P).Normal := by
    dsimp [R₀, twoResidualAmbient]
    rw [subgroupOf_map_subtype_eq]
    unfold twoResidualSubgroup
    rw [sInf_eq_iInf]
    exact Subgroup.normal_iInf_normal
      (fun N => Subgroup.normal_iInf_normal (fun hN => hN.1))
  let N₀ : Subgroup G := R₀ ⊔ J₀
  have hN₀P : N₀ ≤ P := sup_le hR₀P hJ₀P
  have hN₀normalP : (N₀.subgroupOf P).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hN₀P).mpr
    have hPnormR : P ≤ Subgroup.normalizer (R₀ : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hR₀P).mp hRnormalP
    have hSnormJ : S ≤ Subgroup.normalizer (J₀ : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hJ₀S).mp hJ₀normalS
    have hSnormN : S ≤ Subgroup.normalizer (N₀ : Set G) :=
      (le_inf (hSP.trans hPnormR) hSnormJ).trans
        (Subgroup.normalizer_inf_normalizer_le_normalizer_sup R₀ J₀)
    rw [← twoResidual_sup_sylowImage hP.1.2.1]
    exact sup_le (le_sup_left.trans N₀.le_normalizer) hSnormN
  have hNmap : (N₀.subgroupOf P).map fP = R ⊔ J := by
    rw [show N₀.subgroupOf P = R₀.subgroupOf P ⊔ J₀.subgroupOf P by
      exact Subgroup.subgroupOf_sup hR₀P hJ₀P,
      Subgroup.map_sup, hRmapP, hJmapP]
  have hRJnormal : ((R ⊔ J).subgroupOf Pbar).Normal := by
    rw [← hfPrange, ← hNmap]
    exact normal_subgroupOf_range_of_normal_promotion
      fP (N₀.subgroupOf P) hN₀normalP
  obtain ⟨UP, hUP⟩ := hP.1.2.1
  have hUmapH : (UP : Subgroup P).map (Subgroup.inclusion hPH) = SH := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change (y : G) ∈ S
      rw [← hUP]
      exact ⟨y, hy, rfl⟩
    · intro hx
      change (x : G) ∈ S at hx
      rw [← hUP] at hx
      obtain ⟨y, hy, heq⟩ := hx
      refine ⟨y, hy, ?_⟩
      exact Subtype.ext heq
  have hUmap : (UP : Subgroup P).map fP = Sbar := by
    rw [show fP = q.comp (Subgroup.inclusion hPH) from rfl,
      ← Subgroup.map_map, hUmapH]
  have hSylowbar : IsSylowSubgroupIn Sbar Pbar := by
    have hs := isSylowSubgroupIn_map_range_promotion fP UP
    simpa [hfPrange, hUmap] using hs
  have hRJlePbar : R ⊔ J ≤ Pbar := by
    rw [← hNmap, ← hfPrange]
    exact Subgroup.map_le_range fP _
  have hsolvX : Group.IsSolvable X :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective C)
  let _ : Group.IsSolvable X := hsolvX
  have hcoreL : pCore 2 L = ⊥ := by
    simpa [L, W] using threeNine_barF_twoCore_eq_bot
      Sbar Pbar R J hsolvX hSylowbar hRJlePbar hRJnormal hRJcent
        (by simpa [Sbar, SH, q, X] using hbarCore)
  have hker : q.ker = Subgroup.centralizer (V : Set H) := by
    rw [QuotientGroup.ker_mk', hCdef]
  let _ := quotientConjugationAction_promotion V hVnormal q
    (QuotientGroup.mk'_surjective C) hker
  have hfaithX : fixingSubgroup X (Set.univ : Set V) = ⊥ :=
    quotientConjugationAction_faithful_promotion V hVnormal q
      (QuotientGroup.mk'_surjective C) hker
  have hfaithL : fixingSubgroup L (Set.univ : Set V) = ⊥ :=
    fixingSubgroup_subgroup_eq_bot_promotion L hfaithX
  have hVT : V ≤ (T : Subgroup H) :=
    (IsElementaryAbelian.isPGroup 2 V).le_sylow_of_normal T
  have hJL : J ≤ L := le_sup_right
  have hRL : R ≤ L := le_sup_right.trans le_sup_left
  let JL : Subgroup L := J.subgroupOf L
  let RL : Subgroup L := R.subgroupOf L
  have hJHT : JH ≤ (T : Subgroup H) := sSup_le fun _ hA => hA.1
  have hJp : IsPGroup 2 J := (T.isPGroup'.to_le hJHT).map q
  have hJLp : IsPGroup 2 JL :=
    hJp.of_equiv (Subgroup.subgroupOfEquivOfLe hJL).symm
  obtain ⟨U, hJLU⟩ := hJLp.exists_le_sylow
  have hJLne : JL ≠ ⊥ := by
    intro hbot
    apply hJne
    apply le_antisymm
    · intro x hx
      have hxL : (⟨x, hJL hx⟩ : L) ∈ JL := hx
      rw [hbot] at hxL
      apply Subgroup.mem_bot.mpr
      exact congrArg Subtype.val (Subgroup.mem_bot.mp hxL)
    · exact bot_le
  have hUne : (U : Subgroup L) ≠ ⊥ := by
    intro hbot
    apply hJLne
    exact le_antisymm (hJLU.trans (by rw [hbot])) bot_le
  have hevenL : Even (Nat.card L) := by
    have htwo : 2 ∣ Nat.card U := by
      rcases U.isPGroup'.card_eq_or_dvd with hone | htwo
      · exact False.elim (hUne ((Subgroup.eq_bot_iff_card _).mpr hone))
      · exact htwo
    exact even_iff_two_dvd.mpr
      (htwo.trans (U : Subgroup L).card_subgroup_dvd_card)
  have hlocal : SectionOne.Hypotheses L V :=
    ⟨inferInstance, hevenL, hfaithL, hcoreL⟩
  let I := {A : Subgroup H //
    A ∈ elementaryAbelianMaxSubgroups (T : Subgroup H)}
  let Aq : I → Subgroup X := fun a => a.val.map q
  have hAqJ (i : I) : Aq i ≤ J := Subgroup.map_mono (le_sSup i.property)
  have hAqL (i : I) : Aq i ≤ L := (hAqJ i).trans hJL
  let AL : I → Subgroup L := fun i => (Aq i).subgroupOf L
  have hAL (i : I) : SectionOne.oneA (V := V) (U : Subgroup L) (AL i) := by
    apply oneA_subgroupOf_promotion L (Aq i) ((T : Subgroup H).map q)
      (hAqL i) (U : Subgroup L)
    · exact (Subgroup.subgroupOf_mono L (hAqJ i)).trans hJLU
    · exact maxElementary_map_mem_oneA_promotion T V hVnormal hVT q
        (QuotientGroup.mk'_surjective C) hker i.val i.property
  have hJgenX : J = ⨆ i, Aq i := by
    apply le_antisymm
    · apply Subgroup.map_le_iff_le_comap.mpr
      apply sSup_le
      intro A hA
      exact Subgroup.map_le_iff_le_comap.mp
        (le_iSup Aq (⟨A, hA⟩ : I))
    · exact iSup_le fun i => Subgroup.map_mono (le_sSup i.property)
  have hJgenL : JL = ⨆ i, AL i := by
    apply Subgroup.map_injective L.subtype_injective
    rw [show JL.map L.subtype = J from
      Subgroup.map_subgroupOf_eq_of_le hJL,
      Subgroup.map_iSup, hJgenX]
    apply le_antisymm
    · refine iSup_le fun i => ?_
      calc
        Aq i = (AL i).map L.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le (hAqL i)).symm
        _ ≤ ⨆ j, (AL j).map L.subtype :=
          le_iSup (fun j : I => (AL j).map L.subtype) i
    · refine iSup_le fun i => ?_
      calc
        (AL i).map L.subtype = Aq i :=
          Subgroup.map_subgroupOf_eq_of_le (hAqL i)
        _ ≤ ⨆ j, Aq j := le_iSup (fun j : I => Aq j) i
  have hcommLocal : ⁅RL, JL⁆ = RL := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator,
      show RL.map L.subtype = R from Subgroup.map_subgroupOf_eq_of_le hRL,
      show JL.map L.subtype = J from Subgroup.map_subgroupOf_eq_of_le hJL,
      hcommRJ]
  obtain ⟨_, E, n, D, _, _, _, _, hprod, _, hD, _, _, hKderived⟩ :=
    threeNine_local_oneSeven_residual_isThreeGroup
      hlocal U AL hAL JL RL hJgenL hcommLocal
  have hWL : W ≤ L := le_sup_left.trans le_sup_left
  have hderivedCore :
      ((commutator E).map E.subtype).map L.subtype ≤ pCore 3 X :=
    selected_product_derived_le_threeCore_promotion
      L hsolvX hLcent (by simpa [W] using hWL) E D hprod hD
  have hRderived : R ≤ ((commutator E).map E.subtype).map L.subtype := by
    have hm := Subgroup.map_mono (f := L.subtype) hKderived
    simpa [RL, Subgroup.map_subgroupOf_eq_of_le hRL] using hm
  exact hRderived.trans hderivedCore

end Stellmacher.SectionThree
