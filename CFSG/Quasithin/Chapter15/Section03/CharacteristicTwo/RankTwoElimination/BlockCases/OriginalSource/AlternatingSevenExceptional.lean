module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.AlternatingSeven
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.LocalGeometry
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ExceptionalSevenControl.Restriction
public import Theory.LinearAlgebra.BinaryFourPointStabilizer
public import Theory.Quasithin.CoprimeRank
public import Theory.GroupTheory.PrimeRankElementary

/-!
# Excluding the exceptional A₇ block in the original rank-two context

The faithful binary four-space has no nonzero vector fixed by a subgroup
of three-rank two: a vector stabilizer has order1344. The proved H¹
correction therefore puts every such fixed omega-center element in C(L).
In the first source choice, [V,Y₊]=V forces V=U(L), so L normalizes V.
In the second choice, the marked first plane centralizes L. Each conclusion
contradicts the original normalizer bound and the chosen component outside M.
The final theorem derives every earlier premise from the original setup.

Source: Aschbacher–Smith C.1.22–23 and 15.3.21, printed pp.129–130 and1127;
the local seed containment is 15.3.16, printed p.1126.
-/


public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open ChapterC
open Theory.LinearAlgebra
variable {L : Type*} [Group L] [Finite L]

private theorem binaryFour_point_stabilizer_rank (z : Fin 4 → ZMod 2) (hz : z ≠ 0) :
    primeRank 3 (BinaryFivePointStabilizer.stabilizer z) ≤ 1 := by
  let : Finite ((Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) :=
    Finite.of_injective (fun a : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) => (a : (Fin 4 → ZMod 2) → (Fin 4 → ZMod 2))) DFunLike.coe_injective
  have hc := BinaryFourPointStabilizer.card_stabilizer z hz
    (show Module.finrank (ZMod 2) (Fin 4 → ZMod 2) = 4 by simp)
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro E hE
  let : IsElementaryAbelian 3 E := hE
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 3 E).exists_card_eq
  have hd : Nat.card E ∣ 3 * 448 := by simpa only [hc] using E.card_subgroup_dvd_card
  have hp : Nat.Coprime (Nat.card E) 448 := by
    rw [hn]
    exact (by decide : Nat.Coprime 3 448).pow_left n
  exact Nat.le_of_dvd (by decide) (hp.dvd_mul_right.mp hd)

/-- A subgroup of three-rank two fixes no nonidentity vector of the actual
exceptional A₇ module U. This uses its faithful binary four-dimensional action. -/
theorem exceptionalSeven_fixed_vector_eq_one
    (h : IsExceptionalA7Block L) (H : Subgroup L) (hr : primeRank 3 H = 2)
    (u : blockU L) (hu : (u : L) ∈ centralizer (H : Set L)) : u = 1 := by
  let := h.1.elementary
  let : Finite ((Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) :=
    Finite.of_injective (fun a : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) => (a : (Fin 4 → ZMod 2) → (Fin 4 → ZMod 2))) DFunLike.coe_injective
  obtain ⟨f,e,hf,he⟩ := h.natural_restriction
  by_contra hune
  have hz : e (Additive.ofMul u) ≠ 0 := by
    intro hz
    apply hune
    have hu0 := e.map_eq_zero_iff.mp hz
    exact hu0
  let q := QuotientGroup.mk' (pCore 2 L)
  let ρ := Matrix.SpecialLinearGroup.toLin'.comp (f.comp (q.comp H.subtype))
  have hfix (y : H) : ρ y ∈ BinaryFivePointStabilizer.stabilizer (e (Additive.ofMul u)) := by
    change Representation.specialLinearNatural 4 (f (q y)) (e (Additive.ofMul u)) = _
    rw [←he]
    congr 1
    apply congrArg Additive.ofMul
    apply Subtype.ext
    change (y : L) * (u : L) * (y : L)⁻¹ = (u : L)
    rw [hu y y.property,mul_inv_cancel_right]
  let g := ρ.codRestrict _ hfix
  have hk : IsPGroup 2 g.ker := by
    let j : g.ker →* pCore 2 L := (H.subtype.comp g.ker.subtype).codRestrict _ (by
      intro y
      apply (QuotientGroup.eq_one_iff _).mp
      apply hf
      rw [map_one]
      apply Matrix.SpecialLinearGroup.toLin'_injective
      rw [map_one]
      exact congrArg Subtype.val (show g y.val = 1 from y.property))
    exact pCore_isPGroup.of_injective j (by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun a : pCore 2 L => (a : L)) hxy)
  obtain ⟨n,hn⟩ := hk.exists_card_eq
  have hcop : Nat.Coprime 3 (Nat.card g.ker) := by
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hb := (primeRank_le_of_coprime_ker 3 g hcop).trans
    (binaryFour_point_stabilizer_rank _ hz)
  omega

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- The omega-center elements fixed by a rank-two subgroup of an exceptional
A₇ block already centralize the block. The actual H¹ correction removes U. -/
theorem exceptionalSeven_core_fixed_centralizes
    (L : Subgroup G) (hL : IsBlock L) (hm : IsExceptionalA7Block L)
    (H : Subgroup G) (hHL : H ≤ L) (hr : primeRank 3 H = 2)
    (x : G) (hx : x ∈ pCore 2 G)
    (hxc : x ∈ centralizer (pCore 2 G : Set G))
    (hxh : x ∈ centralizer (H : Set G)) : x ∈ centralizer (L : Set G) := by
  let Q := pCore 2 G ⊓ centralizer (pCore 2 G : Set G)
  obtain ⟨u,hu⟩ := RankOne.ExceptionalSevenControl.fixed_correction L hL hm Q
    inf_le_left inf_le_right ⟨x,hx,hxc⟩
  let c : G := (u : G)⁻¹ * x
  have hch : c ∈ centralizer (H : Set G) := centralizer_le hHL hu
  have huh : (u : G) ∈ centralizer (H : Set G) := by
    have h := (centralizer (H : Set G)).mul_mem hxh
      ((centralizer (H : Set G)).inv_mem hch)
    simpa only [c,mul_inv_rev,inv_inv,mul_inv_cancel_left] using h
  obtain ⟨v,hv,hvU⟩ := u.property
  change (v : G) = (u : G) at hvU
  let w : blockU L := ⟨v,hv⟩
  have hw : (w : L) ∈ centralizer (H.subgroupOf L : Set L) := by
    intro y hy
    apply Subtype.ext
    change (y : G) * (v : G) = (v : G) * (y : G)
    rw [hvU]
    exact huh y hy
  have hrH : primeRank 3 (H.subgroupOf L) = 2 := by
    rw [primeRank_congr 3 (subgroupOfEquivOfLe hHL),hr]
  have hw1 := exceptionalSeven_fixed_vector_eq_one hm (H.subgroupOf L) hrH w hw
  have hu1 : (u : G) = 1 := by
    rw [←hvU]
    exact congrArg (fun w : blockU L => ((w : L) : G)) hw1
  simpa only [hu1,inv_one,one_mul] using hu

/-- If the whole elementary sixteen is generated by its action commutators,
it equals U of the exceptional block, and the block normalizes it. -/
theorem exceptionalSeven_commutator_normalizer
    (L : Subgroup G) (hL : IsBlock L) (hm : IsExceptionalA7Block L)
    (H V : Subgroup G) (hHL : H ≤ L) (hV : V ≤ pCore 2 G)
    (hcomm : V = ⁅V,H⁆) (hcard : Nat.card V = 16) : L ≤ normalizer (V : Set G) := by
  have hVU : V ≤ (blockU L).map L.subtype := by
    rw [hcomm]
    exact (commutator_mono hV hHL).trans
      (commutator_le_core_commutator_of_isSubnormal L (pCore 2 G)
        hL.subnormal hL.short.twoPerfect pCore_isPGroup le_normalizer_of_normal)
  have hcU : Nat.card ((blockU L).map L.subtype) = 16 := by
    rw [card_map_of_injective L.subtype_injective,hm.u_card]
  have he : V = (blockU L).map L.subtype := eq_of_le_of_card_ge hVU (by omega)
  rw [he]
  exact L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (blockU L))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction
open ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- The two actual choices of 15.3.10 both contradict an exceptional A₇ block.
The first fills U; the second centralizes the marked first plane. -/
theorem no_exceptionalSeven_block
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hrank : primeRank 3 d.Yplus = 2) (hYL : d.Yplus ≤ c.L)
    (hR : d.R ≤ normalizer (c.L : Set G)) (hm : IsExceptionalA7Block c.L)
    (hVW : d.V ≤ (starV c.L d.R).map (c.L ⊔ d.R : Subgroup G).subtype)
    (hNV : normalizer (d.V : Set G) ≤ d.M)
    (hfirst : d.Yplus = d.Y → d.V = ⁅d.V,d.Yplus⁆)
    (hN1 : OutsideStructure.SecondChoice d → normalizer (d.V₁ : Set G) ≤ d.M) : False := by
  let J := c.L ⊔ d.R
  let K := c.L.subgroupOf J
  let H := d.Yplus.subgroupOf J
  let V := d.V.subgroupOf J
  have hLJ : c.L ≤ J := le_sup_left
  have hYJ : d.Yplus ≤ J := hYL.trans hLJ
  have hVJ : d.V ≤ J := hVW.trans (map_subtype_le _)
  let hnormal : K.Normal := normal_subgroupOf_of_le_normalizer (sup_le c.L.le_normalizer hR)
  have hmK : IsExceptionalA7Block K :=
    RankOne.ExceptionalSevenControl.exceptional_subgroupOf c.L J hLJ hm
  have hbK : IsBlock K := ⟨inferInstance,hmK.1,hnormal.isSubnormal⟩
  have hHK : H ≤ K := comap_mono hYL
  have hrH : primeRank 3 H = 2 := by
    rw [primeRank_congr 3 (subgroupOfEquivOfLe hYJ),hrank]
  have hVstar : V ≤ starV c.L d.R := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hVW hx
    exact (show y = x from Subtype.ext he) ▸ hy
  have hVcore : V ≤ pCore 2 J := hVstar.trans (map_subtype_le _)
  have hVC : V ≤ centralizer (pCore 2 J : Set J) :=
    hVstar.trans (le_centralizer_iff.mp (core_le_starKernel c.L d.R))
  rcases d.choice with hchoice | hchoice
  · have hcomm : V = ⁅V,H⁆ := by
      apply Subgroup.map_injective J.subtype_injective
      rw [map_commutator,map_subgroupOf_eq_of_le hVJ,map_subgroupOf_eq_of_le hYJ]
      exact hfirst hchoice
    have hcard : Nat.card V = 16 :=
      (Nat.card_congr (subgroupOfEquivOfLe hVJ).toEquiv).trans d.action.card_vector
    have hn := exceptionalSeven_commutator_normalizer K hbK hmK H V hHK hVcore hcomm hcard
    have hnG : c.L ≤ normalizer (d.V : Set G) := by
      have h := (map_mono hn).trans (V.le_normalizer_map J.subtype)
      rw [map_subgroupOf_eq_of_le hLJ,map_subgroupOf_eq_of_le hVJ] at h
      exact h
    exact c.outside (hnG.trans hNV)
  · have hYC : d.Yplus ≤ centralizer (d.V₁ : Set G) := by
      rw [hchoice.2]
      exact (map_subtype_le _).trans inf_le_right
    have hplane : d.V₁ ≤ centralizer (c.L : Set G) := by
      intro x hx
      have hxV : x ∈ d.V := d.action.plane_le 1 hx
      let xJ : J := ⟨x,hVJ hxV⟩
      have hxJ : xJ ∈ V := hxV
      have hxcH : xJ ∈ centralizer (H : Set J) := by
        intro y hy
        apply Subtype.ext
        exact (hYC hy x hx).symm
      have hc := exceptionalSeven_core_fixed_centralizes K hbK hmK H hHK hrH
        xJ (hVcore hxJ) (hVC hxJ) hxcH
      intro l hl
      exact congrArg Subtype.val (hc ⟨l,hLJ hl⟩ hl)
    have hLN : c.L ≤ normalizer (d.V₁ : Set G) :=
      (le_centralizer_iff.mp hplane).trans (Subgroup.centralizer_le_normalizer _)
    exact c.outside (hLN.trans (hN1 hchoice))

/-- Exceptional A₇ is excluded from the full original rank-two context, using
only the earlier selection/source geometry and the actual module of the block. -/
theorem source_15_3_21_exceptionalSeven
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus)
    (htwo : OutsideStructure.RankTwoCase d I) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) (hm : IsExceptionalA7Block c.L) : False := by
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI
  obtain ⟨e⟩ := hm.2.1
  have hrI : primeRank 3 I ≤ 2 :=
    (OutsideStructure.outside_sqtk hG d hI).stronglyQuasithin 3 (by decide) (by decide)
  have hYL := yplus_le_of_alternatingSeven_quotient d c h11.theta_eq.symm hrI e
  have hrank := OutsideStructure.rankTwoCase_three_rank hG d hI htwo
  have hinput := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  have hVW := RankTwoElimination.OriginalSource.component_seed_le_starV
    d hinput htwo.2.2.2.2.1
  have hNV := InitialSource.UniformControl.source_local_eq_normalizer hG d.T hM.1
  apply no_exceptionalSeven_block d c hrank hYL hinput.normalizes hm hVW hNV.ge
    ?_ (fun hs => (h11.second_choice hs).2.1)
  intro hfirst
  obtain ⟨hne,_,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  obtain ⟨hi,_,_,_⟩ := source_lemma_15_3_7_of_orthogonal_action
    hG d.T hempty d.action hM hu hmany hne
  rw [hfirst]
  exact (d.action.commutator_eq_of_residual_image d.Y
    (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc) hi).symm

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
