module

public import ABG.ChapterII.Section3.SylowCenter
public import ABG.ChapterII.Section3.CentralSylowQQuotient
public import ABG.ChapterII.Section3.PSL2PreimageCoverData
public import ABG.ChapterII.Section3.SL2LiftCharacteristic
public import GorensteinWalter.IndexTwoPSL2Core
public import GorensteinWalter.SL2ProjectiveCover
public import GorensteinWalter.NormalSL2ProjectiveImage
public import GorensteinWalter.CyclicCentralSL2Cover
public import Theory.GroupTheory.NormalCenterQuotient
public import Theory.GroupTheory.PGroup.NoPrimeIndexImage

/-!
# The unique normal SL2 subgroup of a core-free Q-group

A finite Q-group with semidihedral or wreathed Sylow two-subgroups and trivial
odd core has a unique normal SL2 subgroup over an odd finite field. The field
order is unique as well. Both Sylow alternatives, the enlarged Q-group
predicate, and the field orders three and nine are retained.

The Z-star-based Sylow-center theorem makes the Sylow center globally central.
Its quotient has dihedral Sylow subgroups and the required index-two data,
so the Gorenstein--Walter theorem supplies a unique normal PSL2 subgroup.
The actual inverse image is a nonsplit cyclic central two-cover; the proved
all-field cover theorem supplies its normal SL2 supplement. The no-index-two
property makes this supplement characteristic in the inverse image, hence
normal in the original group.

For uniqueness, any normal SL2 subgroup has center of order two. The normal
center quotient-image theorem identifies its image with the corresponding
PSL2 group. Uniqueness in the quotient fixes that image and the field order.
The no-index-two equal-image theorem then identifies the original subgroups.
This assembles Alperin--Brauer--Gorenstein, II.3 Proposition 2, article pages
22--23 (`page-023.tex` and `page-024.tex` in the repository source).
-/

namespace ABG
open GorensteinWalter BenderSuzuki.MatrixGroups
universe u

private theorem odd_card_of_odd_prime_power {q : ℕ} (hq : IsOddPrimePower q) : Odd q := by
  obtain ⟨p, n, _, hp, _, rfl⟩ := hq
  exact hp.pow

private theorem field_two_ne_zero (F : Type*) [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) : (2 : F) ≠ 0 := by
  exact two_ne_zero_of_odd_card F (odd_card_of_odd_prime_power hF)


public theorem qGroup_exists_unique_normal_SL2 {G : Type u} [Group G] [Finite G]
    (hQ : IsQGroup G) (S : Sylow 2 G)
    (hS : Stellmacher.IsSemidihedralGroup S ∨ IsWreathedGroup S)
    (hcore : pPrimeCore 2 G = ⊥) :
    ∃ (F : Type u) (instF : Field F) (_ : Finite F),
      let : Field F := instF
      IsOddPrimePower (Nat.card F) ∧
      ∃ L : Subgroup G, L.Normal ∧ Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 2) F) ∧
        ∀ (E : Type u) (instE : Field E) (_ : Finite E),
          let : Field E := instE
          IsOddPrimePower (Nat.card E) →
          ∀ M : Subgroup G, M.Normal → Nonempty (M ≃* Matrix.SpecialLinearGroup (Fin 2) E) →
            M = L ∧ Nat.card E = Nat.card F := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcentral : subgroupCenter (S : Subgroup G) ≤ Subgroup.center G := by
    have hc := qGroup_eq_oddCore_mul_sylowCenterCentralizer hQ S
    rw [hcore, bot_sup_eq] at hc
    exact Subgroup.centralizer_eq_top_iff_subset.mp hc
  obtain ⟨N, hNnormal, hN, hNcyclic, hNne, hdih, hquotcore, J, hJN, hJi, hJno⟩ :=
    qGroup_central_sylow_quotient_data hQ S hS hcentral hcore
  let : N.Normal := hNnormal
  have hNc : N ≤ Subgroup.center G := hN ▸ hcentral
  have hNtwo : IsPGroup 2 N := by
    rw [hN]
    exact S.isPGroup'.to_le (Subgroup.map_subtype_le _)
  obtain ⟨F, iF, fF, hF, Lbar, hLbarN, ⟨eLbar⟩, hLbarNo, hLbarUnique⟩ :=
    exists_unique_normal_psl2_of_index_two hdih hquotcore J hJN hJi hJno
  let : Field F := iF
  let : Finite F := fF
  let : Lbar.Normal := hLbarN
  let H := Lbar.comap (QuotientGroup.mk' N)
  let Z := N.subgroupOf H
  obtain ⟨hHN, hNH, hZcyc, hZne, hZc, hZtwo, ⟨eH⟩, hHns⟩ :=
    psl2_preimage_central_cover_data S hS N hN hNc hNcyclic hNne F hF Lbar eLbar
  let : H.Normal := hHN
  obtain ⟨L0, hL0N, ⟨eL0⟩, hgen, _hinter⟩ :=
    Matrix.ProjectiveSpecialLinearGroup.exists_sl2_of_nonsplit_cyclic_two_central_extension
      F hF Z hZne hZcyc hZtwo hZc eH hHns
  let : L0.Normal := hL0N
  let : L0.Characteristic := sl2_central_lift_characteristic Z L0 hZc hZtwo hgen
    (field_two_ne_zero F hF) eL0
  let L := L0.map H.subtype
  have hLN : L.Normal := ConjAct.normal_of_characteristic_of_normal
  let : L.Normal := hLN
  let eL : L ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (Subgroup.equivMapOfInjective L0 H.subtype H.subtype_injective).symm.trans eL0
  have hLimage : L.map (QuotientGroup.mk' N) = Lbar := by
    have hambient : N ⊔ L = H := by
      have h := congrArg (fun U : Subgroup H => U.map H.subtype) hgen
      have hmapN : Z.map H.subtype = N := Subgroup.map_subgroupOf_eq_of_le hNH
      simpa only [Subgroup.map_sup, hmapN,
        ← MonoidHom.range_eq_map, H.range_subtype] using h
    have h := congrArg (fun U : Subgroup G => U.map (QuotientGroup.mk' N)) hambient
    simpa only [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
      H, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N)] using h
  refine ⟨F, iF, fF, hF, L, hLN, ⟨eL⟩, ?_⟩
  intro E iE fE
  let : Field E := iE
  let : Finite E := fE
  dsimp only
  intro hE M hMN heM
  let : M.Normal := hMN
  obtain ⟨eM⟩ := heM
  have heMbar := normal_sl2_projective_image S N M hNc hN.symm.le E hE eM
  have hMbarN : (M.map (QuotientGroup.mk' N)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective N)
  obtain ⟨hMimage, hEF⟩ := hLbarUnique E iE fE hE _ hMbarN heMbar
  refine ⟨?_, hEF⟩
  have hqker : (QuotientGroup.mk' N).ker = N := QuotientGroup.ker_mk' N
  apply Subgroup.eq_of_map_eq_of_no_normal_index_prime (QuotientGroup.mk' N)
    (IsPGroup.of_equiv hNtwo (MulEquiv.subgroupCongr hqker).symm) M L
    (sl2_no_normal_index_two (field_two_ne_zero E hE) eM)
    (sl2_no_normal_index_two (field_two_ne_zero F hF) eL)
  exact hMimage.trans hLimage.symm

end ABG
