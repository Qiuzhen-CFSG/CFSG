module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.POrder
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Sylow.TwoPartBound
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality
public import Theory.GroupTheory.SelfCentralizingCoreInheritance
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Three-part obstructions in Rudvalis local subgroups and two-extensions

Every two-local containing a Sylow two-subgroup of the actual Rudvalis model
has order indivisible by nine. After conjugating the Sylow subgroup to the
checked `localP`, the characteristic elementary subgroup of a defining
nontrivial two-subgroup belongs to the six-member catalogue. Its normalizer
lies in an actual conjugate of max4 or max6. Their checked orders have only
one factor of three. This uses containment, with no maximality premise.

The obstruction passes to a characteristic-two Sylow overgroup M in any
extension H of the model by a two-group. The normal intersection M ∩ K
inherits characteristic two and retains the three-part of |M|. If nine
divided |M|, that intersection would have nontrivial two-core, whose
normalizer in K is a Sylow-containing two-local with order divisible by nine.
All cores and normalizers are intrinsic to their stated ambient groups.

Source: GLS3 Table 5.3r, printed p.279, and the local inspection in
Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.41--42,
printed p.1138. The ATLAS words, attribution, and kernel-checked finite
certificates are preserved in the imported Rudvalis modules.
-/

namespace Rudvalis.SylowOvergroups
open Subgroup RadicalCoverage.LocalCover

private theorem localP_odd_index : ¬ 2 ∣ localP.index := by
  intro h
  apply RadicalCoverage.SylowCertificate.not_two_pow_fifteen_dvd_card_model
  rw [← localP.card_mul_index, IntrinsicSylow.localP_card]
  exact Nat.mul_dvd_mul_left 16384 h

private noncomputable def fixedSylow : Sylow 2 Model :=
  IntrinsicSylow.localP_isPGroup.toSylow localP_odd_index

private theorem fixed_twoLocal_not_nine (M : Subgroup Model) (hM : IsTwoLocal M)
    (hPM : localP ≤ M) : ¬ 9 ∣ Nat.card M := by
  obtain ⟨U, hU, hp, rfl⟩ := hM
  have hUP : U ≤ localP := by
    exact sup_eq_left.mp (fixedSylow.is_maximal'
      (fixedSylow.isPGroup'.to_sup_of_normal_right' hp hPM) le_sup_left)
  obtain ⟨E, hE, hEU, he, hNE⟩ :=
    exists_nontrivial_elementary_with_normalizer_le U hp hU
  obtain ⟨i, hi⟩ := elementaryCatalogue E hE (hEU.trans hUP) (hPM.trans hNE) he
  rw [hi] at hNE
  have hcover := elementaryNormalizerCover_of_bounds max4NormalizerBounds max6NormalizerBounds i
  intro hd
  rcases hcover with ⟨g, hg⟩ | ⟨g, hg⟩
  · apply not_nine_dvd_max4_card
    have h := hd.trans (card_dvd_of_le (hNE.trans hg))
    rwa [card_map_of_injective (MulAut.conj g).injective] at h
  · apply not_nine_dvd_max6_card
    have h := hd.trans (card_dvd_of_le (hNE.trans hg))
    rwa [card_map_of_injective (MulAut.conj g).injective] at h

/-- Every Sylow-containing two-local of the preserved degree-4060 carrier
has order indivisible by nine, without any maximality assumption. -/
public theorem not_nine_dvd_card_twoLocal (P : Sylow 2 Model) (M : Subgroup Model)
    (hM : IsTwoLocal M) (hPM : (P : Subgroup Model) ≤ M) : ¬ 9 ∣ Nat.card M := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Model P fixedSylow
  have hle : localP ≤ M.map (MulAut.conj g).toMonoidHom := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hPM
    change ((g • P : Sylow 2 Model) : Subgroup Model) ≤ _ at hh
    rw [hg] at hh
    exact hh
  have hn := fixed_twoLocal_not_nine _ (Theory.Quasithin.isTwoLocal_map (MulAut.conj g) hM) hle
  rwa [card_map_of_injective (MulAut.conj g).injective] at hn

section
variable {H : Type*} [Group H] [Finite H]

-- The two versions of the actual intersection, with their inherited group structures.
private def intersectionEquiv (K M : Subgroup H) : K.subgroupOf M ≃* M.subgroupOf K where
  toFun x := ⟨⟨x, x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x, x.property⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem not_nine_dvd_card_of_normal_two_quotient (K : Subgroup H) [K.Normal]
    (hquot : IsPGroup 2 (H ⧸ K))
    (hlocal : ∀ (P : Sylow 2 K) (N : Subgroup K), IsTwoLocal N →
      (P : Subgroup K) ≤ N → ¬ 9 ∣ Nat.card N)
    (P : Sylow 2 H) (M : Subgroup H) (hPM : (P : Subgroup H) ≤ M)
    (hchar : centralizer (pCore 2 M : Set M) ≤ pCore 2 M) : ¬ 9 ∣ Nat.card M := by
  let A := M.subgroupOf K
  let B := K.subgroupOf M
  have hcop : Nat.Coprime 9 B.index := by
    obtain ⟨n, hn⟩ := hquot.exists_card_eq
    have hi : B.index ∣ 2 ^ n := hn ▸ K.relIndex_dvd_index_of_normal M
    exact ((by decide : Nat.Coprime 9 2).pow_right n).of_dvd_right hi
  intro hd
  have hB : 9 ∣ Nat.card B := hcop.dvd_of_dvd_mul_right (B.card_mul_index.symm ▸ hd)
  have hA : 9 ∣ Nat.card A := (Nat.card_congr (intersectionEquiv K M).toEquiv) ▸ hB
  have hcharA : centralizer (pCore 2 A : Set A) ≤ pCore 2 A :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 (intersectionEquiv K M)).mp
      (normal_core_selfCentralizing hchar B)
  have hcore : pCore 2 A ≠ ⊥ := by
    intro he
    rw [he, show centralizer ((⊥ : Subgroup A) : Set A) = ⊤ from
      centralizer_eq_top_iff_subset.mpr (show (⊥ : Subgroup A) ≤ center A from bot_le)] at hcharA
    have htriv : Nat.card A = 1 := by
      simpa using congrArg (fun V : Subgroup A => Nat.card V) (le_bot_iff.mp hcharA)
    rw [htriv] at hA
    norm_num at hA
  let U := (pCore 2 A).map A.subtype
  have hUne : U ≠ ⊥ := fun he => hcore ((map_eq_bot_iff_of_injective _ A.subtype_injective).mp he)
  have hAN : A ≤ normalizer (U : Set K) := by
    exact A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
  obtain ⟨T, hT⟩ := P.exists_subgroupOf_eq_of_normal K
  have hTN : (T : Subgroup K) ≤ normalizer (U : Set K) := by
    rw [hT]
    exact (comap_mono hPM).trans hAN
  exact hlocal T _ ⟨U, hUne, pCore_isPGroup.map A.subtype, rfl⟩ hTN
    (hA.trans (card_dvd_of_le hAN))

end

/-- A characteristic-two subgroup containing an ambient Sylow subgroup still
has order indivisible by nine in any extension of the actual Rudvalis carrier
by a two-group. Normality is only that of the displayed subgroup K in H. -/
public theorem not_nine_dvd_card_twoExtension
    {H : Type*} [Group H] [Finite H] (K : Subgroup H) [K.Normal]
    (e : K ≃* Model) (hquot : IsPGroup 2 (H ⧸ K))
    (P : Sylow 2 H) (M : Subgroup H) (hPM : (P : Subgroup H) ≤ M)
    (hchar : centralizer (pCore 2 M : Set M) ≤ pCore 2 M) : ¬ 9 ∣ Nat.card M := by
  apply not_nine_dvd_card_of_normal_two_quotient K hquot _ P M hPM hchar
  intro T N hN hTN
  have hn := not_nine_dvd_card_twoLocal
    (T.mapSurjective e.surjective) (N.map e.toMonoidHom)
    (Theory.Quasithin.isTwoLocal_map e hN)
    (show (T : Subgroup K).map e.toMonoidHom ≤ N.map e.toMonoidHom from map_mono hTN)
  rwa [card_map_of_injective e.injective] at hn

end Rudvalis.SylowOvergroups
