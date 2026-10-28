module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientTitsFixedGeometry
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalHigherFieldTorus
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalHigherFieldSpan
import all CFSG.Quasithin.Chapter6.Section01.SourceHStarLeftCartanOvergroup

/-!
# Cubic movement on the original inner-Sylow fixed line

The omega-center of the original inner Sylow is the full Sylow-fixed
line in the original Hermitian module. It has order four. The actual
Cartan plus factor of order three normalizes this line and moves it:
an odd Borel element fixing a nonidentity point has fifth power one.
The cubic subgroup is its own prime-to-three residual, in the original
ambient inclusion, as required by the component-centralizer argument.

Source: Aschbacher--Smith 6.1.4, printed pp.665--666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
attribute [local instance] SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

/-- The actual inner omega-center is the fixed line of the original Sylow
intersection on the full Hermitian module. -/
theorem original_hermitian_inner_omega_eq_sylow_fixed
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian 2)) :
    omegaOneCenterAmbient
        (((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2) =
      reducedSubgroup (L ⊔ (T : Subgroup G)) ⊓
        centralizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) := by
  let B := reducedSubgroup (L ⊔ (T : Subgroup G))
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let U := (T : Subgroup G) ⊓ L
  let S := U ⊔ Q
  have hBQ : B = omegaOneCenterAmbient Q := h.reduced_enlargement_eq_omega_core
  have hBQl : B ≤ Q := fun b hb => ((mem_omegaOneCenterAmbient_iff Q b).mp (hBQ ▸ hb)).1
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hST : S ≤ (T : Subgroup G) := sup_le inf_le_left hQT
  have hBS : B ≤ S := hBQl.trans le_sup_right
  have hBCQ : B ≤ centralizer (Q : Set G) := fun b hb =>
    ((mem_omegaOneCenterAmbient_iff Q b).mp (hBQ ▸ hb)).2.2
  have hC : (T : Subgroup G) ⊓ centralizer (B : Set G) = Q :=
    full_reduced_hermitian_sylow_centralizer h hm
  apply le_antisymm
  · intro z hz
    obtain ⟨hzS,hz2,hzC⟩ := (mem_omegaOneCenterAmbient_iff S z).mp hz
    have hzQ : z ∈ Q := hC.le ⟨hST hzS,(centralizer_le hBS) hzC⟩
    have hzB : z ∈ B := by
      rw [hBQ]
      exact (mem_omegaOneCenterAmbient_iff Q z).mpr
        ⟨hzQ,hz2,(centralizer_le (show Q ≤ S from le_sup_right)) hzC⟩
    exact ⟨hzB,(centralizer_le (show U ≤ S from le_sup_left)) hzC⟩
  · have hfixed : B ⊓ centralizer (U : Set G) ≤ centralizer (S : Set G) := by
      apply le_centralizer_iff.mpr
      exact sup_le (le_centralizer_iff.mp inf_le_right)
        (le_centralizer_iff.mp (inf_le_left.trans hBCQ))
    intro b hb
    exact (mem_omegaOneCenterAmbient_iff S b).mpr
      ⟨hBS hb.1,((mem_omegaOneCenterAmbient_iff Q b).mp (hBQ ▸ hb.1)).2.1,hfixed hb⟩

/-- An actual cubic subgroup of the original Borel normalizes and moves
the four-element inner omega-center, and is its own cubic residual. -/
theorem original_hermitian_inner_cubic_movement
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian 2)) :
    let W := omegaOneCenterAmbient
      (((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    Nat.card W = 4 ∧ ∃ D : Subgroup G,
      Nat.card D = 3 ∧ D ≤ localBorel T L ∧
      D ≤ normalizer (W : Set G) ∧
      (primeToResidual 3 D).map D.subtype = D ∧ ⁅W,D⁆ ≠ ⊥ := by
  let B := reducedSubgroup (L ⊔ (T : Subgroup G))
  let W := omegaOneCenterAmbient
    (((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2)
  have hW : W = B ⊓ centralizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) :=
    original_hermitian_inner_omega_eq_sylow_fixed h hm
  obtain ⟨hcard,hfix⟩ := RankOneGeneric.hermitian_fixed_geometry 2 h.sylow_normalizes_L hm
  have hW4 : Nat.card W = 4 := by rw [hW]; norm_num at hcard ⊢; exact hcard
  let hi := h.reduced_enlargement.rankOneInput hout
  obtain ⟨A,A',c⟩ := RankOneGeneric.exists_left_cartan_pair hi
  obtain ⟨_,Dm,D,hDE,_,hD,_⟩ :=
    c.hermitian_torus_factors hi 2 hm h.omega_le_reduced_enlargement
  have hD3 : Nat.card D = 3 := by norm_num at hD ⊢; exact hD
  have hDA : D ≤ A := hDE ▸ le_sup_right
  have hDB : D ≤ localBorel T L := hDA.trans c.left_le
  have hDN : D ≤ normalizer (W : Set G) := by
    rw [hW]
    exact (le_inf ((hDB.trans inf_le_left).trans hm.normalizes)
      ((hDB.trans inf_le_right).trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  refine ⟨hW4,D,hD3,hDB,hDN,?_,?_⟩
  · apply le_antisymm (map_subtype_le _)
    intro d hd
    have hp : (⟨d,hd⟩ : D)^(3^1) = 1 := by
      simpa only [pow_one,hD3] using (pow_card_eq_one' (x := (⟨d,hd⟩ : D)))
    exact mem_map_of_mem D.subtype (mem_primeToResidual_of_pow hp)
  · intro hc
    have hW0 : W ≠ ⊥ := by intro he; rw [he] at hW4; simp at hW4
    have hD0 : D ≠ ⊥ := by intro he; rw [he] at hD3; simp at hD3
    obtain ⟨z,hz⟩ := ne_bot_iff_exists_ne_one.mp hW0
    obtain ⟨d,hd⟩ := ne_bot_iff_exists_ne_one.mp hD0
    have hz1 : (z : G) ≠ 1 := fun he => hz (Subtype.ext he)
    have hd1 : (d : G) ≠ 1 := fun he => hd (Subtype.ext he)
    have horder : orderOf (d : G) ∣ 3 := by
      simpa only [Subgroup.orderOf_coe,hD3] using (orderOf_dvd_natCard d)
    have hcomm : D ≤ centralizer (W : Set G) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)
    have hconj : (d : G)*(z : G)*(d : G)⁻¹ = (z : G) :=
      mul_inv_eq_iff_eq_mul.mpr ((hcomm d.property) z z.property).symm
    have hp := (hfix d (hDB d.property) ((by decide : Odd (3:ℕ)).of_dvd_nat horder)
      z (hW ▸ z.property) hz1).mp hconj
    have hdiv5 : orderOf (d : G) ∣ 5 := by
      simpa only [show 2^2+1 = (5:ℕ) from rfl] using orderOf_dvd_of_pow_eq_one hp
    exact hd1 (orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 3 5) horder hdiv5))

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
