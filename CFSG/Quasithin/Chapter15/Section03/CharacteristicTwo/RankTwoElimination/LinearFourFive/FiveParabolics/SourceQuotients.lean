module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FiveParabolics.ParabolicConstruction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Preparation.LocalSetup
public import Theory.GroupTheory.PResidual.NormalSubgroup.TwoGroupKernel
public import Theory.GroupTheory.PrimeRankElementary

/-!
# The source quotients for the five-dimensional parabolic reduction

The genuine earlier alternative 15.3.11(5i) allows E₉ or an extraspecial
group of order 27. The marked PSL₅(2) component has three-part nine, which
excludes the second alternative. The normalized product Y₊S then has
order 2ᵃ·9, so its earlier Frattini denominator is exactly its two-core.
The resulting marking retains the supplied Frattini quotient map.

The image of Y₊(S∩L) under the specified component marking is solvable:
Y₊ is an extension of two- and three-groups, and S∩L is a normalizing
two-group. Adjoining that two-group and removing the marked map's
two-group kernel both preserve the three-part. We also retain the
literal section map and the actual Sylow conjugation action on E₉.

Only the stated earlier cubic alternative and Frattini marking are
inputs; none of the two-core quotient conclusions or image properties
is assumed. The final adapter uses 15.3.11(1),(6) for normalization.
Its full-alternative variant selects 15.3.11(5i) using m₃(Y₊)=2:
the S₃ quotient in (5ii) would bound every elementary three-subgroup
of Y₊ by order three.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.11(5i), printed pp.1123–1124, and 15.3.24, pp.1129–1130.
-/

@[expose] public section

open Subgroup BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FiveParabolics.SourceQuotients
variable {G : Type*} [Group G] [Finite G] (d : LocalData G) {L : Subgroup G}
variable (e : (L ⧸ pCore 2 L) ≃* Projective 5) (hYL : d.Yplus ≤ L)
variable (hcubic : OutsideStructure.CubicQuotient (d.Yplus ⧸ pCore 2 d.Yplus))

/-- The actual model excludes the order-27 alternative of 15.3.11(5i). -/
noncomputable def yplusEquiv :
    (d.Yplus ⧸ pCore 2 d.Yplus) ≃* Multiplicative (Fin 2 → ZMod 3) :=
  Classical.choice (Preparation.yplus_quotient d (Or.inr rfl) e hYL hcubic)

include e hYL hcubic in
/-- The intrinsic two-core quotient has order nine. -/
theorem yplus_quotient_card : Nat.card (d.Yplus ⧸ pCore 2 d.Yplus) = 9 := by
  rw [Nat.card_congr (yplusEquiv d e hYL hcubic).toEquiv]
  change Nat.card (Fin 2 → ZMod 3) = 9
  simp

variable (hSY : d.S ≤ normalizer (d.Yplus : Set G))
variable (shadow : ((d.Yplus ⊔ d.S : Subgroup G) ⧸
  OutsideStructure.coreFrattiniSubgroup (d.Yplus ⊔ d.S : Subgroup G)) ≃*
    (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))

/-- Transport the supplied earlier marking through the proved equality
of its Frattini denominator with the intrinsic two-core. -/
noncomputable def joinEquiv :
    ((d.Yplus ⊔ d.S : Subgroup G) ⧸ pCore 2 (d.Yplus ⊔ d.S : Subgroup G)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :=
  (QuotientGroup.quotientMulEquivOfEq
    (Preparation.coreFrattini_eq_twoCore d ⟨yplusEquiv d e hYL hcubic⟩
      hSY ⟨shadow⟩).symm).trans shadow

/-- No new quotient map is substituted for the earlier Frattini marking. -/
theorem joinEquiv_mk (x : (d.Yplus ⊔ d.S : Subgroup G)) :
    joinEquiv d e hYL hcubic hSY shadow (QuotientGroup.mk' _ x) =
      shadow (QuotientGroup.mk' _ x) := rfl

/-- The marking carries the original conjugation to conjugation in S₃×S₃. -/
theorem joinEquiv_conj (s : d.S) (x : (d.Yplus ⊔ d.S : Subgroup G)) :
    joinEquiv d e hYL hcubic hSY shadow
        (QuotientGroup.mk' _ (inclusion le_sup_right s * x * (inclusion le_sup_right s)⁻¹)) =
      shadow (QuotientGroup.mk' _ (inclusion le_sup_right s)) *
        joinEquiv d e hYL hcubic hSY shadow (QuotientGroup.mk' _ x) *
          (shadow (QuotientGroup.mk' _ (inclusion le_sup_right s)))⁻¹ := by
  simp only [map_mul, map_inv, joinEquiv_mk]

/-- The action on E₉ is the transport of actual ambient S-conjugation. -/
noncomputable def yplusAction : d.S →* MulAut (Multiplicative (Fin 2 → ZMod 3)) :=
  (MulAut.congr (yplusEquiv d e hYL hcubic)).toMonoidHom.comp
    (Preparation.sylowCoreAction d d.Yplus hSY)

/-- Equivariance on the original quotient representatives. -/
theorem yplusAction_mk (s : d.S) (y : d.Yplus) :
    yplusAction d e hYL hcubic hSY s
        (yplusEquiv d e hYL hcubic (QuotientGroup.mk' _ y)) =
      yplusEquiv d e hYL hcubic (QuotientGroup.mk' _
        (d.Yplus.normalizerMonoidHom ⟨s, hSY s.property⟩ y)) := by
  change yplusEquiv d e hYL hcubic
    (Preparation.sylowCoreAction d d.Yplus hSY s
      ((yplusEquiv d e hYL hcubic).symm
        (yplusEquiv d e hYL hcubic (QuotientGroup.mk' _ y)))) = _
  rw [MulEquiv.symm_apply_apply, Preparation.sylowCoreAction_apply]

/-- The literal base section maps to the exact image used by the parabolic consumer. -/
noncomputable def baseSectionEquiv :
    Preparation.CoreSection L (d.Yplus ⊔ (d.S ⊓ L)) ≃* baseImage d e :=
  Preparation.coreSectionEquiv (by decide) e _

omit [Finite G] in
/-- The section equivalence is the specified L/O₂(L) marking on representatives. -/
theorem baseSectionEquiv_mk (x : (d.Yplus ⊔ (d.S ⊓ L)).subgroupOf L) :
    (baseSectionEquiv d e (QuotientGroup.mk' _ x) : LinearGroup 5) =
      linearAction (by decide) e x.val := rfl

include hYL hcubic hSY in
/-- Solvability follows from the actual normalized product and its image map. -/
theorem baseImage_solvable : Group.IsSolvable (baseImage d e) := by
  have h9 := yplus_quotient_card d e hYL hcubic
  let : Group.IsSolvable (d.Yplus ⊔ (d.S ⊓ L) : Subgroup G) :=
    BinaryLinear.CubicPairGeometry.normalized_join_solvable _ _
      (d.T.isPGroup'.to_le (inf_le_left.trans inf_le_left))
      (inf_le_left.trans hSY) 2 h9
  let a : ((d.Yplus ⊔ (d.S ⊓ L)).subgroupOf L) ≃*
      (d.Yplus ⊔ (d.S ⊓ L) : Subgroup G) :=
    subgroupOfEquivOfLe (sup_le hYL inf_le_right)
  let : Group.IsSolvable ((d.Yplus ⊔ (d.S ⊓ L)).subgroupOf L) :=
    Group.isSolvable_of_isSolvable_injective (f := a.toMonoidHom) a.injective
  exact Group.isSolvable_of_surjective
    ((linearAction (by decide : 0 < 5) e).subgroupMap_surjective _)

include hYL hcubic hSY in
/-- The marked map has a two-group kernel, so the base image has three-part nine. -/
theorem baseImage_three_part : (Nat.card (baseImage d e)).factorization 3 = 2 := by
  have hm := threePart_map_of_twoGroup_kernel (linearAction (by decide) e)
    (by rw [FiveParabolics.linearAction_ker e]; exact pCore_isPGroup)
    ((d.Yplus ⊔ (d.S ⊓ L)).subgroupOf L)
  have he := Nat.card_congr (subgroupOfEquivOfLe (sup_le hYL
    (show d.S ⊓ L ≤ L from inf_le_right))).toEquiv
  rw [he, BinaryLinear.CubicPairGeometry.normalized_join_three_part d.Yplus (d.S ⊓ L)
    (d.T.isPGroup'.to_le (inf_le_left.trans inf_le_left)) (inf_le_left.trans hSY),
    BinaryLinear.CubicPairGeometry.three_part_of_core_quotient_nine _
      (yplus_quotient_card d e hYL hcubic)] at hm
  exact (Nat.pow_right_injective (by decide : 2 ≤ 3)) hm

omit [Finite G] in
/-- Earlier 15.3.11(1),(6) give normalization relative to M∩I. -/
theorem sylow_normalizes_yplus {I : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 d.S I) (hθ : theta (d.MI I) = d.Yplus) :
    d.S ≤ normalizer (d.Yplus : Set G) := by
  rw [← hθ]
  exact (le_inf (inf_le_left.trans d.sylow_le) (Chapter1.isSylowIn_iff.mp hS).2.1).trans
    ((d.MI I).le_normalizer.trans (normalizer_le_normalizer_theta _))

/-- Both genuine two-core quotients and the two base-image properties required
by the five-dimensional parabolic construction, from the permitted earlier clauses. -/
theorem source_preparation {I : Subgroup G} (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Projective 5)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hYL : d.Yplus ≤ c.L)
    (hθ : theta (d.MI I) = d.Yplus)
    (hcubic : OutsideStructure.CubicQuotient (d.Yplus ⧸ pCore 2 d.Yplus))
    (hshadow : Nonempty (((d.Yplus ⊔ d.S : Subgroup G) ⧸
      OutsideStructure.coreFrattiniSubgroup (d.Yplus ⊔ d.S : Subgroup G)) ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    Nonempty ((d.Yplus ⧸ pCore 2 d.Yplus) ≃* Multiplicative (Fin 2 → ZMod 3)) ∧
    Nonempty (((d.Yplus ⊔ d.S : Subgroup G) ⧸ pCore 2 (d.Yplus ⊔ d.S : Subgroup G)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
    Group.IsSolvable (baseImage d e) ∧ (Nat.card (baseImage d e)).factorization 3 = 2 := by
  obtain ⟨shadow⟩ := hshadow
  have hn := sylow_normalizes_yplus d hS hθ
  exact ⟨⟨yplusEquiv d e hYL hcubic⟩, ⟨joinEquiv d e hYL hcubic hn shadow⟩,
    baseImage_solvable d e hYL hcubic hn, baseImage_three_part d e hYL hcubic hn⟩

private theorem rank_le_one_of_join_quotient
    (f : ((d.Yplus ⊔ d.S : Subgroup G) ⧸ pCore 2 (d.Yplus ⊔ d.S : Subgroup G)) ≃*
      Equiv.Perm (Fin 3)) : primeRank 3 d.Yplus ≤ 1 := by
  let J := d.Yplus ⊔ d.S
  have h6 : Nat.card (J ⧸ pCore 2 J) = 6 := by
    rw [Nat.card_congr f.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := J)).exists_card_eq
  have hJ : Nat.card J = 2 ^ k * 6 := by
    rw [← (pCore 2 J).card_mul_index, index_eq_card, hk, h6]
  apply (primeRank_le_iff_elementary_card_le d.Yplus).mpr
  intro E hE
  let := hE
  obtain ⟨m, hm⟩ := (IsElementaryAbelian.isPGroup 3 E).exists_card_eq
  have hd : 3 ^ m ∣ 2 ^ k * 6 := by
    rw [← hm, ← hJ]
    exact E.card_subgroup_dvd_card.trans (card_dvd_of_le
      (show d.Yplus ≤ J from le_sup_left))
  have hc : Nat.Coprime (3 ^ m) 2 := (by decide : Nat.Coprime 3 2).pow_left m
  have hd6 : 3 ^ m ∣ 6 := (hc.pow_right k).dvd_of_dvd_mul_left hd
  have hd3 : 3 ^ m ∣ 3 := hc.dvd_of_dvd_mul_left hd6
  simpa only [hm, pow_one] using Nat.le_of_dvd (by decide : 0 < 3) hd3

/-- The actual rank hypothesis selects (5i) from the full earlier alternative;
the S₃ two-core quotient in (5ii) permits three-rank at most one. -/
theorem rankTwoCase_of_rank_two {I : Subgroup G} (hrank : primeRank 3 d.Yplus = 2)
    (hcases : OutsideStructure.RankTwoCase d I ∨ OutsideStructure.RankOneCase d I) :
    OutsideStructure.RankTwoCase d I := by
  rcases hcases with h | h
  · exact h
  · obtain ⟨f⟩ := h.2.1
    have hb := rank_le_one_of_join_quotient d f
    omega

/-- The complete quotient preparation from the full genuine 15.3.11(5)
alternative, without assuming its rank-two branch or either target quotient. -/
theorem source_preparation_of_earlier {I : Subgroup G} (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Projective 5)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hYL : d.Yplus ≤ c.L)
    (hθ : theta (d.MI I) = d.Yplus) (hrank : primeRank 3 d.Yplus = 2)
    (hcases : OutsideStructure.RankTwoCase d I ∨ OutsideStructure.RankOneCase d I) :
    Nonempty ((d.Yplus ⧸ pCore 2 d.Yplus) ≃* Multiplicative (Fin 2 → ZMod 3)) ∧
    Nonempty (((d.Yplus ⊔ d.S : Subgroup G) ⧸ pCore 2 (d.Yplus ⊔ d.S : Subgroup G)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
    Group.IsSolvable (baseImage d e) ∧ (Nat.card (baseImage d e)).factorization 3 = 2 := by
  have h := rankTwoCase_of_rank_two d hrank hcases
  exact source_preparation d c e hS hYL hθ h.1 h.2.1

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FiveParabolics.SourceQuotients

end
