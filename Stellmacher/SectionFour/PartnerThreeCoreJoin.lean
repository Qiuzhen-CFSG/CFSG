module

public import Stellmacher.SectionFour.BaumannFactorDecomposition
public import Stellmacher.SectionFour.BaumannFixedFactorTrivial
public import Stellmacher.SectionThree.LemmaThreeThree
public import Theory.GroupTheory.SylowThreeNormal

/-!
# Normality of the partner core joined with a Sylow three-subgroup

In the critical-partner configuration of Stellmacher (4.6), every supplied
Sylow three-subgroup `T` of `Pstar` has normal join with `O₂(Pstar)`. The
original module `V = ⟨Ω₁(Z(S))^Pstar⟩` and its actual centralizer are retained.
This is the normality input for the subsequent Frattini argument.

The two-core centralizes the original module: it lies in the native Sylow,
whose central involutions lie in its normal centralizer. The original module
is nontrivial because the given Sylow has nontrivial central involutions.
The fixed factor of the module decomposition vanishes, so its generating
family of `SL₂(2)` factors is nonempty. One such factor makes three divide
`|Pstar/C(V)|`. Since the two-core lies in `C(V)`, a quotient surjection makes
three divide `|Pstar/O₂(Pstar)|` as well. Only the generating supremum of the
module decomposition is used; no product-cardinality assertion is needed.

Source (3.3), applied to the partner's unique maximal overgroup, makes the
two-residual of `Pstar/O₂(Pstar)` an odd-prime group. Its quotient is a
two-group. The divisibility by three therefore forces that prime to be three,
and normal Sylow uniqueness makes the image of the supplied `T` normal.
Pulling it back along the core quotient gives exactly `O₂(Pstar) ∨ T`.
There is no assumption that `C(V)` equals the two-core.

Source: Stellmacher, Journal of Algebra 190 (1997), proof of (4.6), journal
p.26, Sylow-three/Frattini paragraph; `refs/latex/stellmacher-n-group.tex`.
-/

open scoped Pointwise
namespace Stellmacher.SectionFour

private theorem zSubgroup_ne_bot
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (heven : Even (Nat.card G)) :
    zSubgroup S ≠ ⊥ := by
  have hSne : (S : Subgroup G) ≠ ⊥ := S.ne_bot_of_dvd_card heven.two_dvd
  let : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot (S : Subgroup G)).2 hSne
  let : Nontrivial (Subgroup.center S) := S.isPGroup'.center_nontrivial
  have hcenterP : IsPGroup 2 (Subgroup.center S) := S.isPGroup'.to_subgroup _
  obtain ⟨n, hn, hcard⟩ := hcenterP.nontrivial_iff_card.mp inferInstance
  have hdvd : 2 ∣ Nat.card (Subgroup.center S) := by
    rw [hcard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)
  have hinner := omega₁_map_subtype_ne_bot (G := S) (Subgroup.center S) 2 hdvd
  intro hz
  apply hinner
  apply (Subgroup.map_eq_bot_iff_of_injective
    (H := (omega₁ (G := Subgroup.center S) (p := 2)).map (Subgroup.center S).subtype)
    (f := (S : Subgroup G).subtype) (S : Subgroup G).subtype_injective).mp
  simpa [zSubgroup, omegaOneCenterAmbient] using hz

private theorem core_le_module_centralizer
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) :
    pCore 2 G ≤ Subgroup.centralizer (SectionTwo.vSubgroup S : Set G) := by
  have hcoreS : pCore 2 G ≤ (S : Subgroup G) :=
    (pCore_isPGroup (p := 2) (G := G)).le_sylow_of_normal S
  have hZcentCore : zSubgroup S ≤ Subgroup.centralizer (pCore 2 G : Set G) := by
    intro z hz
    obtain ⟨zS, ⟨zC, _hzC, rfl⟩, rfl⟩ := hz
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact congrArg (fun s : S ↦ (s : G))
      ((Subgroup.mem_center_iff.mp zC.property) ⟨q, hcoreS hq⟩)
  exact Subgroup.le_centralizer_iff.mp (Subgroup.normalClosure_le_normal hZcentCore)

private theorem partner_core_quotient_three_dvd
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (heven : Even (Nat.card G))
    (P Pstar E : Subgroup G) (hpair : (P, Pstar) ∈ Lambda S)
    (hPC : P ≤ cSubgroup S) (hEP : E ≤ Pstar)
    (hsolv : Group.IsSolvable Pstar) (hchar : IsCharacteristicTwoType Pstar)
    (hE : (E : Set G) = (twoResidualAmbient Pstar : Set G) *
      (twoCoreAmbient (cSubgroup S) : Set G))
    (hSyl : IsSylowSubgroupIn (twoCoreAmbient (cSubgroup S)) E) :
    3 ∣ Nat.card (Pstar ⧸ pCore 2 Pstar) := by
  obtain ⟨SP, _hsec, hSP, hV⟩ :=
    original_partner_sectionTwo_data S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl
  let B := twoCoreAmbient (cSubgroup S) ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient (elementaryAbelianMaxJ (twoCoreAmbient (cSubgroup S))) : Set G)
  let L := Subgroup.normalClosure (B.subgroupOf Pstar : Set Pstar)
  let V := Subgroup.normalClosure ((zSubgroup S).subgroupOf Pstar : Set Pstar)
  let C := Subgroup.centralizer (V : Set Pstar)
  let _ : V.Normal := Subgroup.normalClosure_normal
  let _ : C.Normal := inferInstance
  let q : Pstar →* Pstar ⧸ C := QuotientGroup.mk' C
  have hVC : SectionTwo.vSubgroup SP = V := hV
  have hQC : pCore 2 Pstar ≤ C := by
    change pCore 2 Pstar ≤ Subgroup.centralizer (V : Set Pstar)
    rw [← hVC]
    exact core_le_module_centralizer SP
  have hVne : V ≠ ⊥ := by
    intro hbot
    have hZsub : (zSubgroup S).subgroupOf Pstar = ⊥ :=
      le_bot_iff.mp (Subgroup.le_normalClosure.trans_eq hbot)
    have hZP : zSubgroup S ≤ Pstar := by
      have hSPstar : (S : Subgroup G) ≤ Pstar := hSP ▸ Subgroup.map_subtype_le _
      exact (Subgroup.map_subtype_le _).trans hSPstar
    apply zSubgroup_ne_bot S heven
    rw [← Subgroup.map_subgroupOf_eq_of_le hZP, hZsub, Subgroup.map_bot]
  have hdata := baumann_factor_module_decomposition S heven P Pstar E hpair hPC hEP
    hsolv hchar hE hSyl
  change SectionTwo.BaumannFactorModuleData V L q at hdata
  obtain ⟨n, D, Vf, _hgen, _hprod, hSL, _hVf, hVprod⟩ := hdata.factors
  have hfixed : V ⊓ Subgroup.centralizer (L : Set Pstar) = ⊥ :=
    baumann_fixed_factor_eq_bot S heven P Pstar E hpair hPC hEP hsolv hchar hE hSyl
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    subst n
    apply hVne
    apply le_bot_iff.mp
    rw [hVprod.1]
    apply iSup_le
    rintro (_ | i)
    · exact hfixed.le
    · exact Fin.elim0 i
  let i : Fin n := ⟨0, hn⟩
  have hthreeC : 3 ∣ Nat.card (Pstar ⧸ C) := by
    have hcard := SectionOne.RankOneThreeGroupAssembly.isSL2Two_card (hSL i)
    exact (show 3 ∣ Nat.card (D i) by rw [hcard]; decide).trans
      (Subgroup.card_subgroup_dvd_card (D i))
  let f : (Pstar ⧸ pCore 2 Pstar) →* (Pstar ⧸ C) :=
    QuotientGroup.map (pCore 2 Pstar) C (MonoidHom.id Pstar) (by simpa using hQC)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective C x
    exact ⟨QuotientGroup.mk' (pCore 2 Pstar) p, rfl⟩
  exact hthreeC.trans (Subgroup.card_dvd_of_surjective f hf)

private theorem partner_residual_odd_pgroup
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (heven : Even (Nat.card G)) (Pstar : Subgroup G)
    (hP : Pstar ∈ SectionThree.PSet (⊤ : Subgroup G) (S : Subgroup G))
    (hsolv : Group.IsSolvable Pstar) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧
      IsPGroup p (twoResidualAmbient (⊤ : Subgroup (Pstar ⧸ pCore 2 Pstar))) := by
  rcases hP.2 with ⟨B, hBmax, hSB, hBuniq⟩
  have hSP : (S : Subgroup G) ≤ Pstar := by
    obtain ⟨SP, hSP⟩ := hP.1.2.1
    rw [← hSP]
    exact Subgroup.map_subtype_le _
  have hSsubB : (S : Subgroup G).subgroupOf Pstar ≤ B := by
    intro s hs
    obtain ⟨b, hb, hbs⟩ := hSB hs
    have hbeq : b = s := Pstar.subtype_injective hbs
    simpa [← hbeq] using hb
  have huniq : ∀ B' : Subgroup Pstar, IsCoatom B' →
      (S : Subgroup G).subgroupOf Pstar ≤ B' → B' = B := by
    intro B' hB' hsub
    apply hBuniq B' hB'
    rw [← Subgroup.map_subgroupOf_eq_of_le hSP]
    exact Subgroup.map_mono hsub
  have hBcore : B.normalCore ≤ B ∧ B.normalCore.Normal ∧
      ∀ N : Subgroup Pstar, N.Normal → N ≤ B → N ≤ B.normalCore := by
    refine ⟨B.normalCore_le, inferInstance, ?_⟩
    intro N hN hNB
    exact (@Subgroup.normal_le_normalCore Pstar _ B N hN).2 hNB
  exact (SectionThree.lemma_three_three (S : Subgroup G)
    ⟨heven, S.ne_bot_of_dvd_card heven.two_dvd, S.isPGroup'⟩ Pstar hP
    B B.normalCore ⟨hBmax, hSsubB, huniq⟩ hBcore hsolv).part_a

public theorem partner_core_sup_sylow_three_normal
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (heven : Even (Nat.card G))
    (P Pstar E : Subgroup G) (hpair : (P, Pstar) ∈ Lambda S)
    (hPC : P ≤ cSubgroup S) (hEP : E ≤ Pstar)
    (hsolv : Group.IsSolvable Pstar) (hchar : IsCharacteristicTwoType Pstar)
    (hE : (E : Set G) = (twoResidualAmbient Pstar : Set G) *
      (twoCoreAmbient (cSubgroup S) : Set G))
    (hSyl : IsSylowSubgroupIn (twoCoreAmbient (cSubgroup S)) E)
    (T : Sylow 3 Pstar) : (pCore 2 Pstar ⊔ (T : Subgroup Pstar)).Normal := by
  have hthree := partner_core_quotient_three_dvd S heven P Pstar E hpair hPC hEP
    hsolv hchar hE hSyl
  obtain ⟨p, hp, hpodd, hRp⟩ := partner_residual_odd_pgroup S heven Pstar hpair.2.1 hsolv
  let X := Pstar ⧸ pCore 2 Pstar
  let q : Pstar →* X := QuotientGroup.mk' (pCore 2 Pstar)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  let R := BenderSuzuki.External.hktPResidual 2 X
  let _ : R.Normal := BenderSuzuki.External.hktPResidual_normal
  have hR : IsPGroup p R := by
    change IsPGroup p (twoResidualAmbient (⊤ : Subgroup X)) at hRp
    rw [SectionThree.twoResidualAmbient_top_eq_hktPResidual] at hRp
    exact hRp
  have hquot : IsPGroup 2 (X ⧸ R) := BenderSuzuki.External.hktPResidual_quotient_isPGroup
  have hp2 : p ≠ 2 := by
    intro heq
    subst p
    norm_num at hpodd
  let Tbar := T.mapSurjective hq
  have hTnormal : (Tbar : Subgroup X).Normal :=
    Subgroup.sylow_three_normal_of_odd_prime_normal_quotient_two p hp hp2 R hR hquot hthree Tbar
  have hnormal := hTnormal.comap q
  have hpreimage : (Tbar : Subgroup X).comap q =
      pCore 2 Pstar ⊔ (T : Subgroup Pstar) := by
    rw [Sylow.coe_mapSurjective, Subgroup.comap_map_eq]
    have hker : q.ker = pCore 2 Pstar := QuotientGroup.ker_mk' _
    rw [hker, sup_comm]
  rwa [hpreimage] at hnormal

end Stellmacher.SectionFour
