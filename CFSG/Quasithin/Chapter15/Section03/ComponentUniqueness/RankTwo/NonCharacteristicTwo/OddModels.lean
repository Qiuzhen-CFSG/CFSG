module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.Definitions
public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.FermatMersenne
public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.LinearRank
public import Theory.SpecificGroups.PSL3Three.EvenLocals
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import Theory.GroupTheory.SelfCentralizingCoreInheritance
public import Theory.GroupTheory.TwoLocalCoreObstruction
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.PrimeRankInvolutionLift
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Odd-characteristic models in the rank-two component argument

The three-rank of Y₊ excludes every PSL₂(p) over an odd prime field: its
Sylow three-subgroups are cyclic. This includes p = 3, so the shared
Fermat--Mersenne predicate needs no extra lower bound.

For PSL₃(3), relative normality makes M ∩ L normal in M ∩ I. Thus its
two-core is self-centralizing, and the order-nine subgroup supplied by Y₊
ensures that this core is nontrivial. Sylow restriction and the actual
PSL₃(3) ≃ SL₃(3) comparison put M ∩ L inside a Sylow-containing maximal
two-local of SL₃(3). The checked semidihedral calculation identifies that
local as an involution centralizer GL₂(3), of order 48, contradicting the
order-nine subgroup. No additional inner-action premise is needed.

These are precisely the case (e) exclusions used in Aschbacher--Smith,
combined manuscript (1 March 2004), 15.3.42, printed p.1138, with the
actual models of 1.1.5(3e), printed pp.501--503. Field transport reuses
the ATLAS adaptation and attribution in `ExceptionalIsomorphisms.Support`.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.OddModels

private theorem prime_linear_two_rank {H : Type*} [Group H] [Finite H]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hm : ClassicalGroup.IsPSL H 2 p) :
    primeRank 3 H ≤ 1 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let f : F ≃+* ZMod p := (ZMod.ringEquivOfPrime F hp
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let E := e.trans (Atlas.fieldEquivPSL 2 f)
  let P : Sylow 3 SL(2, ZMod p) := default
  rw [primeRank_equiv 3 E]
  exact P.primeRank_quotient_le_one
    (Matrix.SU3.InnerThreeRank.sl2_sylow_three_isCyclic p ho P) _

private theorem fermatMersenne_odd {p : ℕ} (hp : IsFermatOrMersennePrime p) : Odd p := by
  apply hp.1.odd_of_ne_two
  rintro rfl
  rcases hp.2 with ⟨a, ha⟩ | ⟨a, ha⟩
  · have hlow : 2 ≤ 2 ^ (2 ^ a) := Nat.le_pow (by norm_num)
    omega
  · have hd : 2 ∣ 2 ^ a := dvd_pow_self _ (by rintro rfl; norm_num at ha)
    omega

variable {G : Type*} [Group G] [Finite G]
variable {I L M Yplus S : Subgroup G} [(L.subgroupOf I).Normal]

/-- The full Fermat--Mersenne family, including its small parameters, is excluded. -/
theorem not_psl2_fermatMersenne (d : ComponentSetup I L M Yplus S)
    (hmodel : ∃ p, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL L 2 p) : False := by
  obtain ⟨p, hp, hm⟩ := hmodel
  have hr := (primeRank_le_of_injective 3 (inclusion d.yplus_le)
    (inclusion_injective d.yplus_le)).trans
    (prime_linear_two_rank hp.1 (fermatMersenne_odd hp) hm)
  rw [d.yplus_three_rank] at hr
  omega

private theorem component_sylow (d : ComponentSetup I L M Yplus S) :
    ∃ T : Sylow 2 L, (T : Subgroup L).map L.subtype = S ⊓ L := by
  obtain ⟨P, hP⟩ := d.sylow
  obtain ⟨T, hT⟩ := P.exists_subgroupOf_eq_of_normal (L.subgroupOf I)
  let e := subgroupOfEquivOfLe d.component_le
  refine ⟨T.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change ((T : Subgroup (L.subgroupOf I)).map e.toMonoidHom).map L.subtype = _
  rw [map_map]
  change (T : Subgroup (L.subgroupOf I)).map
    (I.subtype.comp (L.subgroupOf I).subtype) = _
  rw [← map_map, hT, subgroupOf_map_subtype, map_inf _ _ _ I.subtype_injective,
    hP, map_subgroupOf_eq_of_le d.component_le]

private theorem intersection_characteristicTwo (d : ComponentSetup I L M Yplus S) :
    centralizer (pCore 2 (M ⊓ L : Subgroup G) : Set (M ⊓ L : Subgroup G)) ≤
      pCore 2 (M ⊓ L : Subgroup G) := by
  have hc : centralizer (pCore 2 (M ⊓ I : Subgroup G) : Set (M ⊓ I : Subgroup G)) ≤
      pCore 2 (M ⊓ I : Subgroup G) := by
    rw [← d.intersection_fitting]
    exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
  have hle : M ⊓ L ≤ M ⊓ I := inf_le_inf_left M d.component_le
  let f : (M ⊓ I : Subgroup G) →* I := inclusion inf_le_right
  have hn : ((M ⊓ L).subgroupOf (M ⊓ I)).Normal := by
    have he : (M ⊓ L).subgroupOf (M ⊓ I) = (L.subgroupOf I).comap f := by
      ext x
      exact and_iff_right x.property.1
    rw [he]
    infer_instance
  let := hn
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hle)).mp
    (normal_core_selfCentralizing hc ((M ⊓ L).subgroupOf (M ⊓ I)))

private theorem nine_dvd (d : ComponentSetup I L M Yplus S) : 9 ∣ Nat.card Yplus := by
  obtain ⟨E, _, hE⟩ := exists_elementaryAbelian_card_primeRank (G := Yplus) (p := 3)
  have hd := E.card_subgroup_dvd_card
  rwa [hE, d.yplus_three_rank] at hd

private theorem local_card_dvd_48 (P : Sylow 2 Matrix.PSL3Three.SL)
    (D : Subgroup Matrix.PSL3Three.SL) (hPD : (P : Subgroup _) ≤ D)
    (hc : pCore 2 D ≠ ⊥) : Nat.card D ∣ 48 := by
  obtain ⟨J, hJ, hDJ⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot D hc
  obtain ⟨z, hz, rfl⟩ := Matrix.PSL3Three.maximalTwoLocal_eq_involutionCentralizer_SL
    P hJ (hPD.trans hDJ)
  have hcard : Nat.card (centralizer ({z} : Set Matrix.PSL3Three.SL)) = 48 := by
    rw [Nat.card_congr (Matrix.SL3.involutionCentralizerEquiv (ZMod 3) z hz
      (by decide)).toEquiv, Matrix.card_GL_field]
    norm_num [Fin.prod_univ_two]
  exact hcard ▸ card_dvd_of_le hDJ

private theorem not_linear_three_equiv (d : ComponentSetup I L M Yplus S)
    (e : L ≃* Matrix.PSL3Three.SL) : False := by
  let D := M.subgroupOf L
  let K := D.map e.toMonoidHom
  let ed : D ≃* (M ⊓ L : Subgroup G) :=
    { toFun x := ⟨x, x.property, x.val.property⟩
      invFun x := ⟨⟨x, x.property.2⟩, x.property.1⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_mul' _ _ := rfl }
  have hD : centralizer (pCore 2 D : Set D) ≤ pCore 2 D :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 ed).mpr
      (intersection_characteristicTwo d)
  have hK : centralizer (pCore 2 K : Set K) ≤ pCore 2 K :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 (e.subgroupMap D)).mp hD
  have hY : Yplus ≤ M ⊓ L := le_inf
    ((d.theta_eq ▸ theta_le (M ⊓ I)).trans inf_le_left) d.yplus_le
  have h9 : 9 ∣ Nat.card K := by
    rw [card_map_of_injective e.injective, Nat.card_congr ed.toEquiv]
    exact (nine_dvd d).trans (card_dvd_of_le hY)
  have hc : pCore 2 K ≠ ⊥ := by
    intro hz
    have hct : centralizer ((⊥ : Subgroup K) : Set K) = ⊤ := by
      apply centralizer_eq_top_iff_subset.mpr
      change (⊥ : Subgroup K) ≤ center K
      exact bot_le
    rw [hz, hct] at hK
    have hcard : Nat.card K = 1 := by
      have hh : (⊤ : Subgroup K) = ⊥ := le_antisymm hK bot_le
      have h := congrArg (fun Q : Subgroup K => Nat.card Q) hh
      simpa only [card_top, card_bot] using h
    rw [hcard] at h9
    norm_num at h9
  obtain ⟨P, hP⟩ := component_sylow d
  have hPD : (P : Subgroup L) ≤ D := by
    intro x hx
    have hh : (x : G) ∈ S ⊓ L := hP ▸ mem_map_of_mem L.subtype hx
    exact d.sylow_le_M hh.1
  have hd := local_card_dvd_48 (P.mapSurjective (f := e.toMonoidHom) e.surjective)
    K (map_mono hPD) hc
  exact (by decide : ¬ 9 ∣ 48) (h9.trans hd)

/-- The actual projective matrix model PSL₃(3) is excluded. -/
theorem not_psl3_three (d : ComponentSetup I L M Yplus S)
    (hm : ClassicalGroup.IsPSL L 3 3) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let f : F ≃+* ZMod 3 := (ZMod.ringEquivOfPrime F Nat.prime_three
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  exact not_linear_three_equiv d ((e.trans (Atlas.fieldEquivPSL 3 f)).trans
    Matrix.PSL3Three.equiv.symm)

/-- Neither concrete odd-characteristic model in source 1.1.5(3e) admits
this rank-two component setup. -/
theorem not_odd_model (d : ComponentSetup I L M Yplus S)
    (hm : ClassicalGroup.IsPSL L 3 3 ∨
      ∃ p, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL L 2 p) : False := by
  rcases hm with h | h
  · exact not_psl3_three d h
  · exact not_psl2_fermatMersenne d h

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.OddModels
