module
public import CFSG.Quasithin.ChapterE.Section02.Structure.NormalBender
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.OmegaNormalizer.Models
public import Theory.SpecificGroups.PSL2.SylowPointwiseInner
public import Theory.SpecificGroups.SU3.SylowPointwiseInner.Full
public import Theory.SpecificGroups.Suzuki.BorelPointwiseRigidity
public import CFSG.Quasithin.ChapterE.Section02.Structure.NormalSourceCases
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient
public import Theory.GroupTheory.AutomorphismExtensionBorel
public import Theory.GroupTheory.SolvableOuterQuotient
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.ResidualCentralImage

/-!
# Centerlessness of the normal Bender source maximal quotient

The normal Bender row has a simple normal image `D` and identifies the
intersection of the maximal image with `D` as the Sylow normalizer.  The
pointwise Sylow rigidity of the three Bender model families then forces the
center of this maximal image to vanish.

Source: Aschbacher--Smith, E.2.2(2a), printed pp.215--216.
-/


public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Structure
variable {D : Type*} [Group D] [Finite D] [IsSimpleGroup D]

/-- All exact simple Bender models have Sylow-inner pointwise Sylow fixers. -/
theorem bender_pointwise_sylow_inner (hm : ClassificationModels.IsBenderModel D)
    (S : Sylow 2 D) (α : MulAut D) (hf : ∀ x ∈ S, α x = x) :
    ∃ x ∈ S, α = MulAut.conj x := by
  cases hm with
  | linear n hn h =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [←Nat.card_eq_fintype_card] using hF)
    exact MulAut.fixing_sylow_inner_of_equiv e Theory.PSL2.aut_fixing_sylow_inner S α hf
  | unitary n hn h =>
    obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := h
    let : IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      e.symm.isSimpleGroup
    exact MulAut.fixing_sylow_inner_of_equiv e
      (BenderSuzuki.MatrixGroups.HermitianForm.SylowPointwiseInner.fixing_sylow_eq_mem_conj
        J hn hF hconj) S α hf
  | suzuki m hm h =>
    exact BenderSuzuki.MatrixGroups.suzuki_aut_fixing_sylow_inner (by omega) h.some S α hf

/-- No nonidentity Sylow element centralizes its whole Borel. -/
theorem bender_sylow_inf_borel_centralizer_eq_bot
    (hm : ClassificationModels.IsBenderModel D) (S : Sylow 2 D) :
    (S : Subgroup D) ⊓ centralizer (normalizer (S : Set D) : Set D) = ⊥ := by
  let Q := omegaOneAmbient (S : Subgroup D)
  have hf := Chapter2.BenderFusion.OmegaNormalizerModels.of_bender_model hm S
  have hQne : Q ≠ ⊥ := by
    intro he
    have hh := hf.size
    change 2 < Nat.card Q at hh
    rw [he,card_bot] at hh
    omega
  have hN : normalizer (Q : Set D) = normalizer (S : Set D) := by
    let : (omega₁ S (p := 2)).Characteristic := omega₁_characteristic S
    exact SylowCenterAction.normalizer_eq_of_unique_maximal S Q hQne
      (omegaOneAmbient_le _) (normalizer_le_normalizer_characteristic_image
        (S : Subgroup D) (omega₁ S (p := 2)))
      (bender_sylow_facts hm S).proper (bender_sylow_facts hm S).unique_maximal
  apply eq_bot_iff.mpr
  intro x hx
  by_contra hxne
  let y : S := ⟨x,hx.1⟩
  have hyne : y ≠ 1 := fun he => hxne (congrArg Subtype.val he)
  let z : D := x ^ (orderOf y / 2)
  have hz : orderOf z = 2 := by
    have hh : orderOf (y ^ (orderOf y / 2)) = 2 :=
      orderOf_pow_orderOf_div (orderOf_pos y).ne' (S.isPGroup'.dvd_orderOf hyne)
    rw [←Subgroup.orderOf_coe] at hh
    exact hh
  have hz1 : z ≠ 1 := fun he => by simp [he] at hz
  have hzQ : z ∈ Q := (omegaOneAmbient_le_iff _ _).mp le_rfl z
    ((S : Subgroup D).pow_mem hx.1 _) (hz ▸ pow_orderOf_eq_one z)
  have hzC : z ∈ centralizer (normalizer (S : Set D) : Set D) :=
    (centralizer _).pow_mem hx.2 _
  have hle : Q ≤ zpowers z := by
    intro a ha
    by_cases ha1 : a = 1
    · rw [ha1]; exact (zpowers z).one_mem
    obtain ⟨n,hn,he⟩ := hf.transitive z hzQ hz1 a ha ha1
    rw [hN] at hn
    have hnz : n * z = z * n := mem_centralizer_iff.mp hzC n hn
    have haz : a = z := by rw [←he,hnz,mul_inv_cancel_right]
    rw [haz]
    exact mem_zpowers z
  have hh := Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)
  rw [Nat.card_zpowers,hz] at hh
  exact (not_lt_of_ge hh) hf.size

/-- The full automorphism pointwise fixer of the actual Borel is trivial. -/
theorem bender_pointwise_borel_eq_one (hm : ClassificationModels.IsBenderModel D)
    (S : Sylow 2 D) (α : MulAut D)
    (hf : ∀ x ∈ normalizer (S : Set D), α x = x) : α = 1 := by
  obtain ⟨x,hx,rfl⟩ := bender_pointwise_sylow_inner hm S α
    (fun x hx => hf x ((S : Subgroup D).le_normalizer hx))
  have hxc : x ∈ centralizer (normalizer (S : Set D) : Set D) := by
    intro n hn
    exact (mul_inv_eq_iff_eq_mul.mp (hf n hn)).symm
  have hx1 : x = 1 := by
    have hh : x ∈ (S : Subgroup D) ⊓ centralizer (normalizer (S : Set D) : Set D) := ⟨hx,hxc⟩
    simpa only [bender_sylow_inf_borel_centralizer_eq_bot hm S,mem_bot] using hh
  rw [hx1,map_one]
end CFSG.Quasithin.ChapterE.Structure

namespace CFSG.Quasithin.ChapterE.Structure
variable {H : Type*} [Group H] [Finite H]

/-- Pointwise Borel rigidity removes the center of the literal maximal subgroup. -/
theorem center_eq_bot_of_normal_bender_borel
    (S : Sylow 2 H) (D M : Subgroup H) [D.Normal] [IsSimpleGroup D]
    (hm : ClassificationModels.IsBenderModel D)
    (hM : M.subgroupOf D = normalizer ((S : Subgroup H).subgroupOf D : Set D))
    (hC : centralizer (D : Set H) = ⊥) : center M = ⊥ := by
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal D
  apply eq_bot_iff.mpr
  intro z hz
  have hα : (MulAut.conjNormal (H := D) : H →* MulAut D) (z : H) = 1 := by
    apply bender_pointwise_borel_eq_one hm R
    intro d hd
    have hdM : (d : H) ∈ M := by
      change d ∈ M.subgroupOf D
      rw [hM,←hR]
      exact hd
    have hc := congrArg Subtype.val (mem_center_iff.mp hz (⟨d,hdM⟩ : M))
    change (d : H) * (z : H) = (z : H) * d at hc
    apply Subtype.ext
    change (z : H) * d * (z : H)⁻¹ = d
    rw [←hc,mul_inv_cancel_right]
  have hz1 : (z : H) = 1 :=
    MulAut.conjNormal_injective_of_centralizer_eq_bot D hC (by
      simpa only [map_one] using hα)
  exact Subtype.ext hz1

/-- The normal Bender source row has trivial center in its original star maximal. -/
theorem source_original_star_bender_center_eq_bot (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable H)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hm : ClassificationModels.IsBenderModel
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)))) :
    center ((ChapterB.minimalParabolicMax T hP).map
      (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) = ⊥ := by
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let D := K.map q
  have hd := source_normal_simple_image T hP hs K hK hgen
  let : IsSimpleGroup D := hd.1
  let : D.Normal := hd.2.2.1
  have hb := source_original_star_bender T hP hs K hK hgen hm
  apply center_eq_bot_of_normal_bender_borel S D _ hm hb.1
  apply centralizer_eq_bot_of_simple_two_quotient D hd.2.1
  · exact isPGroup_quotient_of_sup_eq_top D (S : Subgroup (H ⧸ J)) S.isPGroup' hd.2.2.2
  · have hf := source_star_minimal_core_free T hP
    have hp := ChapterB.minimalParabolicTwoCore_le_core S hf.1
    exact le_bot_iff.mp (hp.trans hf.2.le)
end CFSG.Quasithin.ChapterE.Structure

namespace CFSG.Quasithin.ChapterE.Witnesses
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
variable {H : Type*} [Group H] [Finite H]

/-- The residual-fixed center point contradicts the normal Bender centerless row. -/
theorem source_original_star_bender_residual_exclusion
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hm : ClassificationModels.IsBenderModel
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))))
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hout : ¬V ≤ ChapterB.minimalParabolicCore T hP)
    (hres : (pResidual 2 (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H)) :
    False := by
  have hne := CFSG.Quasithin.ChapterE.Witnesses.source_star_maximal_center_ne_bot T hP V hVT hvn hout hres
  have hbot := CFSG.Quasithin.ChapterE.Structure.source_original_star_bender_center_eq_bot
    T hP hs K hK hgen hm
  exact hne hbot
end CFSG.Quasithin.ChapterE.Witnesses
