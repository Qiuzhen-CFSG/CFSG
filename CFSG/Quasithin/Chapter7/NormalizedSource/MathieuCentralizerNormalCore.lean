module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuCentralizerSimpleSieve
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuCentralizerRankTwo
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.NormalElementaryBound
public import Theory.SpecificGroups.Held.SylowNormalSixteen
public import Theory.Mathieu.M24.Properties.CubicElementary
public import Theory.ElementaryAbelian.AutomorphismLinearModel
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The elementary sixteen excludes the last simple Mathieu containers

A normal elementary subgroup of a full J₂ Sylow has order at most four.
In Held, a Sylow-normalized elementary sixteen has five-free normalizer.
In M₂₄ no element of order three centralizes an elementary sixteen; but
17280 has an extra factor of three compared with GL₄(2), forcing such an
actor in the residual's conjugation kernel. These literal carrier facts
complete the simple-component exclusion after the earlier order, rank,
and parabolic inspections. Normality is always relative to the full Sylow.

Source: Aschbacher–Smith A.3.12 and 8.2.13, printed pp.47–48 and 722–723.
The actual marked-cocode application is in NonFFSourceMathieuM24ComponentIdentification.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextet

private theorem core_normalized_data {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (B : Subgroup G) (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    [IsElementaryAbelian 2 (pCore 2 B)] (hc : Nat.card (pCore 2 B) = 16) :
    let U := B.pCoreIn 2
    U ≤ (S : Subgroup G) ∧ (S : Subgroup G) ≤ normalizer (U : Set G) ∧
      IsElementaryAbelian 2 U ∧ Nat.card U = 16 ∧ B ≤ normalizer (U : Set G) := by
  let U := B.pCoreIn 2
  have hs : (S : Subgroup G) ≤ normalizer (U : Set G) :=
    hn.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  have hUS : U ≤ (S : Subgroup G) := by
    have heq : (S : Subgroup G) ⊔ U = (S : Subgroup G) :=
      S.is_maximal' (S.isPGroup'.to_sup_of_normal_right' (isPGroup_pCoreIn 2 B) hs) le_sup_left
    exact sup_eq_left.mp heq
  exact ⟨hUS,hs,
    IsElementaryAbelian.map B.subtype,(card_map_of_injective B.subtype_injective).trans hc,
    B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))⟩

theorem not_janko_two_containing {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (B : Subgroup G) (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    [IsElementaryAbelian 2 (pCore 2 B)] (hc : Nat.card (pCore 2 B) = 16)
    (e : G ≃* Sporadic.LeechRelated.J2.Carrier) : False := by
  obtain ⟨hUS,hSN,he,hcard,_⟩ := core_normalized_data S B hn hc
  let := he
  let U := (B.pCoreIn 2).map e.toMonoidHom
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hUT : U ≤ (T : Subgroup Sporadic.LeechRelated.J2.Carrier) := map_mono hUS
  have hTN : (T : Subgroup Sporadic.LeechRelated.J2.Carrier) ≤ normalizer (U : Set _) :=
    (map_mono hSN).trans (le_normalizer_map e.toMonoidHom)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map e.toMonoidHom
  have hb := Sporadic.LeechRelated.J2.sylow_normal_elementary_card_le_four T
    (U.subgroupOf T) (normal_subgroupOf_iff_le_normalizer hUT |>.mpr hTN)
    (IsElementaryAbelian.subgroupOf hUT)
  rw [Nat.card_congr (subgroupOfEquivOfLe hUT).toEquiv,
    card_map_of_injective e.injective,hcard] at hb
  omega

theorem not_held_containing {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (B : Subgroup G) (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    [IsElementaryAbelian 2 (pCore 2 B)] (hc : Nat.card (pCore 2 B) = 16)
    (hB : Nat.card B = 17280) (e : G ≃* Held.He) : False := by
  obtain ⟨hUS,hSN,he,hcard,hBN⟩ := core_normalized_data S B hn hc
  let := he
  have hnot := Held.sylow_normal_sixteen_normalizer_not_five
    (S.mapSurjective (f := e.toMonoidHom) e.surjective) ((B.pCoreIn 2).map e.toMonoidHom)
    (map_mono hUS) (IsElementaryAbelian.map e.toMonoidHom)
    ((card_map_of_injective e.injective).trans hcard)
    ((map_mono hSN).trans (le_normalizer_map e.toMonoidHom))
  rw [← map_equiv_normalizer_eq (B.pCoreIn 2) e,card_map_of_injective e.injective] at hnot
  exact hnot ((show 5 ∣ Nat.card B by rw [hB]; decide).trans (card_dvd_of_le hBN))

private theorem cubic_core_fixer {B : Type*} [Group B] [Finite B]
    [IsElementaryAbelian 2 (pCore 2 B)] (hc : Nat.card (pCore 2 B) = 16)
    (hB : Nat.card B = 17280) :
    ∃ x : B, orderOf x = 3 ∧ x ∈ centralizer (pCore 2 B : Set B) := by
  let f : B →* MulAut (pCore 2 B) := MulAut.conjNormal
  have ha : Nat.card (MulAut (pCore 2 B)) = 20160 := by
    rw [Nat.card_congr (IsElementaryAbelian.mulAutLinearEquivOfCard (p := 2) (n := 4)
      (pCore 2 B) hc).toEquiv,Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ,ZMod.card]
  have hk : 3 ∣ Nat.card f.ker := by
    by_contra hh
    have hp : Nat.Coprime 27 (Nat.card f.ker) :=
      (Nat.prime_three.coprime_iff_not_dvd.mpr hh).pow_left 3
    have hprod := f.ker.card_mul_index
    rw [index_ker] at hprod
    have h27 : 27 ∣ Nat.card f.ker * Nat.card f.range := by rw [hprod,hB]; decide
    have hd := (hp.dvd_of_dvd_mul_left h27).trans f.range.card_subgroup_dvd_card
    rw [ha] at hd
    norm_num at hd
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' 3 hk
  refine ⟨x,(orderOf_coe x).trans hx,?_⟩
  apply mem_centralizer_iff.mpr
  intro u hu
  have he := congrArg (fun a : MulAut (pCore 2 B) => ((a ⟨u,hu⟩ : pCore 2 B) : B)) x.property
  change (x : B) * u * (x : B)⁻¹ = u at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The original residual's cubic kernel on its elementary sixteen excludes M24. -/
theorem not_mathieu_twentyFour_containing {G : Type*} [Group G] [Finite G]
    (B : Subgroup G) [IsElementaryAbelian 2 (pCore 2 B)]
    (hc : Nat.card (pCore 2 B) = 16) (hB : Nat.card B = 17280)
    (e : G ≃* Sporadic.Mathieu.M24) : False := by
  obtain ⟨x,hx,hfix⟩ := cubic_core_fixer hc hB
  let U := (B.pCoreIn 2).map e.toMonoidHom
  let : IsElementaryAbelian 2 (B.pCoreIn 2) := IsElementaryAbelian.map B.subtype
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map e.toMonoidHom
  apply Sporadic.Mathieu.M24CubicElementary.not_centralizes_elementary_sixteen U
    ((card_map_of_injective e.injective).trans ((card_map_of_injective B.subtype_injective).trans hc))
    (e x) ((e.orderOf_eq x).trans ((orderOf_coe x).trans hx))
  rintro _ ⟨u,⟨v,hv,rfl⟩,rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  have hh := mem_centralizer_iff.mp hfix v hv
  have hh' : (v : G) * (x : G) = (x : G) * (v : G) := congrArg Subtype.val hh
  simpa only [map_mul, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype] using congrArg e hh'

/-- The full simple source catalogue is incompatible with the original
residual and its faithful binary degree-twelve containing action. -/
theorem not_simple_containing
    {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ ChapterA.Section03.localCComponents S)
    (hSN : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hne : B ≠ ⊤) (hcard : Nat.card B = 17280)
    [IsElementaryAbelian 2 (pCore 2 B)] (hcore : Nat.card (pCore 2 B) = 16)
    (hc : Nat.card (B ⧸ pCore 2 B) = 1080) (hr : 4 ≤ primeRank 2 G)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) W = 12)
    (hm : Chapter1.Section02.LocalModels.TheoremCModel G) : False := by
  rcases simple_containing_shortlist S B hB hne hcard hr ρ hf hd hm with hm | hm | hm | hm
  · apply not_rankTwo_containing S B hB hne hcard hc _ hm
    intro hh
    rw [hh] at hcore
    norm_num at hcore
  · exact not_mathieu_twentyFour_containing B hcore hcard hm.some
  · exact not_janko_two_containing S B hSN hcore hm.some
  · exact not_held_containing S B hSN hcore hcard hm.some

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextet
