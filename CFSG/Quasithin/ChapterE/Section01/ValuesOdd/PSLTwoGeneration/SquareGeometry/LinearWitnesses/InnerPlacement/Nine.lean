module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.Structure
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.LocalModels
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.SymmetricNormalizers
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.FourNormalizers.Geometry
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.NaturalFixed
public import Glauberman.DicksonClassification
public import GorensteinWalter.LinearThreeEquiv
public import GorensteinWalter.LinearRingEquiv

/-!
# Paired S₄ placement in PSL₂ over a field of order nine

The actual PSL₂(F) ≃ A₆ comparison transports four-group normalizers to S₄.
Dickson's classification at field order nine shows that every proper Sylow
two overgroup is the Sylow subgroup itself or S₄; maximality excludes the
first case. Thus a maximal overgroup M is the normalizer of one of the two
four-groups in the dihedral Sylow subgroup of order eight.

The weak-closure normalizer hypothesis forces this particular four-group B
to belong to the elementary family. Otherwise the weak closure would be
the other four-group, whose distinct S₄ normalizer cannot lie in M. The
paired normalizer then escapes M and contains B nonnormally. The imported
order-eight overlap theorem supplies the literal Sylow intersection.
The argument keeps both inner fusion classes; it does not identify them by
inner conjugacy.

Source: Aschbacher--Smith, A.2.3(2), E.1.2 and E.1.14(6), printed pp.33,
209--210 and 214; the last cites Aschbacher (1982), Lemma 4.10. The actual
exceptional comparison is the attributed ATLAS port in
`Theory.AtlasPort.ExceptionalIsomorphisms.Order360`, adapted from Gerald
Höhn and the ATLAS contributors, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917. See `LICENSES/ATLAS.txt` and
`LICENSES/ATLAS-CITATION.cff` for its license and attribution.
-/

public section

open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.InnerPlacement.Nine
open PrimeGeometry.Inner.SymmetricNormalizers
variable {F : Type*} [Field F] [Finite F]

omit [Field F] [Finite F] in
private theorem odd_card (hF : Nat.card F = 9) : IsOddPrimePower (Nat.card F) :=
  ⟨3, 2, Nat.prime_three, by decide, by decide, by simpa using hF⟩

/-- Every Sylow two-subgroup has order eight. -/
theorem sylow_card (hF : Nat.card F = 9) (T : Sylow 2 (PSL2 F)) : Nat.card T = 8 := by
  rw [T.card_eq_multiplicity, Atlas.Comparisons.Exceptional.psl2Card9_card hF]
  decide +kernel

/-- The ambient normalizer of each four-group is an actual S₄. -/
theorem normalizer_equiv (hF : Nat.card F = 9)
    (A : Subgroup (PSL2 F)) (hA : IsKleinFour A) :
    Nonempty (normalizer (A : Set (PSL2 F)) ≃* Equiv.Perm (Fin 4)) := by
  let e := Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 hF
  let A' := A.map e.toMonoidHom
  let : IsKleinFour A' := isKleinFour_map_of_injective A hA e.toMonoidHom e.injective
  obtain ⟨eA⟩ := AlternatingSix.ShadowLocal.FourNormalizers.normalizer_equiv_symmetric
    (fun σ hσ => ⟨AlternatingSix.ShadowLocal.swapFixedEquiv σ hσ⟩) A'
  exact ⟨((normalizer (A : Set (PSL2 F))).equivMapOfInjective e.toMonoidHom e.injective).trans
    ((MulEquiv.subgroupCongr (map_equiv_normalizer_eq A e)).trans eA)⟩

private theorem complement_card {G : Type*} [Group G] (N C : Subgroup G)
    (hN : N.Normal) (hd : Disjoint N C) (hj : N ⊔ C = ⊤) :
    Nat.card N * Nat.card C = Nat.card G := by
  let := hN
  apply Subgroup.IsComplement'.card_mul_card
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hd
  rw [← Subgroup.normal_mul N C, hj]
  rfl

/-- Dickson at q = 9, retaining the actual PGL₂(3) subfield alternative. -/
theorem proper_overgroup_models (hF : Nat.card F = 9)
    (T : Sylow 2 (PSL2 F)) (M : Subgroup (PSL2 F))
    (hTM : (T : Subgroup (PSL2 F)) ≤ M) (hM : M ≠ ⊤) :
    M = (T : Subgroup (PSL2 F)) ∨ Nonempty (M ≃* Equiv.Perm (Fin 4)) := by
  have h8 : 8 ∣ Nat.card M := sylow_card hF T ▸ card_dvd_of_le hTM
  obtain ⟨n, hn, ⟨eT⟩⟩ := psl2_odd_hasDihedralSylowTwo_model F (odd_card hF) T
  obtain ⟨A, hAT, hA⟩ := exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
    (T : Subgroup (PSL2 F)) hn eT
  have hAM := hAT.trans hTM
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification
      (p := 3) (f := 2) (by simpa using hF) M with
    helem | hcyc | hdih | h4 | hs | h5 | hsemi | hpsl | hpgl
  · exact (no_kleinFour_of_pGroup_subgroup M A
      (IsElementaryAbelian.isPGroup 3 M) (by decide) hAM hA).elim
  · exact (no_kleinFour_subgroup_of_isCyclic M A hA hAM hcyc.choose_spec.2.2).elim
  · obtain ⟨z, hz, hc, _⟩ := hdih
    have hz4 : z = 4 := by
      rw [hF] at hz
      norm_num at hz
      rw [hc] at h8
      rcases hz with hz | hz
      · have hb := Nat.le_of_dvd (by decide : 0 < 4) hz
        have hpos : 0 < 2 * z := hc ▸ Nat.card_pos (α := M)
        have hlo := Nat.le_of_dvd hpos h8
        omega
      · have hh := (Nat.dvd_prime Nat.prime_five).mp hz
        rcases hh with rfl | rfl <;> norm_num at h8
    left
    exact (eq_of_le_of_card_ge hTM (by rw [hc, hz4, sylow_card hF T])).symm
  · obtain ⟨_, ⟨eM⟩⟩ := h4
    rw [Nat.card_congr eM.toEquiv, alternatingGroup.card_of_card_eq_four (by simp)] at h8
    norm_num at h8
  · exact Or.inr hs.2
  · obtain ⟨_, ⟨eM⟩⟩ := h5
    rw [Nat.card_congr eM.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at h8
    norm_num at h8
  · obtain ⟨m, t, _, ht, N, C, hN, _, hn, _, hc, hd, hj⟩ := hsemi
    have he := complement_card N C hN hd hj
    rw [hn, hc] at he
    rw [← he] at h8
    have hcop : Nat.Coprime 8 (3 ^ m) := (show Nat.Coprime 8 3 by decide).pow_right m
    have h8t : 8 ∣ t := hcop.dvd_of_dvd_mul_left h8
    norm_num at ht
    have : 8 ∣ 4 := h8t.trans ht
    norm_num at this
  · obtain ⟨m, hm, hmd, ⟨eM⟩⟩ := hpsl
    have hm12 : m = 1 ∨ m = 2 := (Nat.dvd_prime Nat.prime_two).mp hmd
    rcases hm12 with rfl | rfl
    · have hk : Nat.card (GaloisField 3 1) = 3 := by
        rw [GaloisField.card 3 1 (by decide)]; norm_num
      have hko : IsOddPrimePower (Nat.card (GaloisField 3 1)) :=
        ⟨3, 1, Nat.prime_three, by decide, by decide, by simpa using hk⟩
      rw [Nat.card_congr eM.toEquiv, psl2_card_formula _ hko, hk] at h8
      norm_num at h8
    · exact (hM (Subgroup.eq_top_of_card_eq M (by
        rw [Nat.card_congr eM.toEquiv,
          Atlas.Comparisons.Exceptional.psl2Card9_card hF,
          Atlas.Comparisons.Exceptional.psl2Card9_card (by
            rw [GaloisField.card 3 2 (by decide)]; norm_num)]))).elim
  · obtain ⟨m, hm, hmd, ⟨eM⟩⟩ := hpgl
    have hm1 : m = 1 := by
      have := Nat.le_of_dvd (by decide : 0 < 2) hmd
      omega
    subst m
    let : Fintype (GaloisField 3 1) := Fintype.ofFinite _
    have hk : Fintype.card (GaloisField 3 1) = 3 := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 3 1 (by decide)]; norm_num
    let ek := ZMod.ringEquivOfPrime (GaloisField 3 1) Nat.prime_three hk
    exact Or.inr ⟨eM.trans ((pgl2RingEquiv ek).symm.trans pgl2_three_equiv_perm)⟩

private theorem normalizer_card (hF : Nat.card F = 9)
    (A : Subgroup (PSL2 F)) (hA : IsKleinFour A) :
    Nat.card (normalizer (A : Set (PSL2 F))) = 24 := by
  obtain ⟨eA⟩ := normalizer_equiv hF A hA
  rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
  norm_num

/-- Every maximal proper Sylow overgroup is S₄. -/
theorem maximal_overgroup_equiv (hF : Nat.card F = 9)
    (T : Sylow 2 (PSL2 F)) (M : Subgroup (PSL2 F))
    (hM : IsCoatom M) (hTM : (T : Subgroup (PSL2 F)) ≤ M) :
    Nonempty (M ≃* Equiv.Perm (Fin 4)) := by
  rcases proper_overgroup_models hF T M hTM hM.1 with rfl | h
  · obtain ⟨n, hn, ⟨eT⟩⟩ := psl2_odd_hasDihedralSylowTwo_model F (odd_card hF) T
    obtain ⟨A, hAT, hA⟩ := exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
      (T : Subgroup (PSL2 F)) hn eT
    let := hA
    have hTN := normalizes_four_of_card_eight A (T : Subgroup (PSL2 F)) hAT (sylow_card hF T)
    have hN : normalizer (A : Set (PSL2 F)) ≠ ⊤ := by
      intro h
      have hc := normalizer_card hF A hA
      rw [h, Nat.card_congr (topEquiv (G := PSL2 F)).toEquiv,
        Atlas.Comparisons.Exceptional.psl2Card9_card hF] at hc
      omega
    have he : normalizer (A : Set (PSL2 F)) = (T : Subgroup (PSL2 F)) := by
      by_contra hne
      exact hN (hM.2 _ (lt_of_le_of_ne hTN (fun h => hne h.symm)))
    have hc := normalizer_card hF A hA
    rw [he, sylow_card hF T] at hc
    omega
  · exact h

private theorem normalizer_le_eq (hF : Nat.card F = 9)
    (A B : Subgroup (PSL2 F)) (hA : IsKleinFour A) (hB : IsKleinFour B)
    (hAB : normalizer (A : Set (PSL2 F)) ≤ normalizer (B : Set (PSL2 F))) :
    A = B := by
  have he : normalizer (A : Set (PSL2 F)) = normalizer (B : Set (PSL2 F)) :=
    eq_of_le_of_card_ge hAB (by rw [normalizer_card hF A hA, normalizer_card hF B hB])
  let N := normalizer (B : Set (PSL2 F))
  have hAN : A ≤ N := le_normalizer.trans hAB
  have hBN : B ≤ N := le_normalizer
  let := hA
  let := hB
  let : IsKleinFour (A.subgroupOf N) := klein_subgroupOf A N hAN
  let : IsKleinFour (B.subgroupOf N) := klein_subgroupOf B N hBN
  let : (A.subgroupOf N).Normal :=
    (normal_subgroupOf_iff_le_normalizer hAN).mpr he.symm.le
  obtain ⟨eN⟩ := normalizer_equiv hF B hB
  have hf := (normal_four_eq_core eN (A.subgroupOf N)).trans
    (normal_four_eq_core eN (B.subgroupOf N)).symm
  have hf' := congrArg (fun K : Subgroup N => K.map N.subtype) hf
  simpa only [map_subgroupOf_eq_of_le hAN, map_subgroupOf_eq_of_le hBN] using hf'

/-- The complete order-nine placement, with no extra geometric premises. -/
theorem concreteLocalGeometryAt (hF : Nat.card F = 9) (T : Sylow 2 (PSL2 F)) :
    PrimeGeometry.ConcreteLocalGeometryAt T := by
  intro Ω hΩ hlarge M hM hTM hNM
  obtain ⟨eM⟩ := maximal_overgroup_equiv hF T M hM hTM
  obtain ⟨B, hBT, hB, hMB⟩ := exists_four_normalizer_eq_symmetric_overgroup
    (odd_card hF) (MulEquiv.refl (PSL2 F)) T M hTM eM
  have hBΩ : B ∈ Ω := by
    by_contra hnot
    obtain ⟨A, hAΩ, hAT, hA⟩ := PrimeGeometry.Inner.exists_four_group_actor
      (odd_card hF) (MulEquiv.refl (PSL2 F)) T Ω hΩ hlarge M hM.1 hNM
    have hne : A ≠ B := fun h => hnot (h ▸ hAΩ)
    have hW : weakClosure (T : Subgroup (PSL2 F)) Ω = A := by
      apply le_antisymm
      · apply sSup_le
        intro C hC
        by_cases hbot : C = ⊥
        · exact hbot ▸ bot_le
        let : IsElementaryAbelian 2 C := hΩ.1 C hC.1
        have hfour := large_actor_isKleinFour (odd_card hF)
          (Or.inl ⟨MulEquiv.refl (PSL2 F)⟩) C (hlarge C hC.1 hC.2 hbot)
        rcases four_groups_exhaust_of_sylow_card_eight
          (odd_card hF) (MulEquiv.refl (PSL2 F)) T (sylow_card hF T)
          A B hA hB hAT hBT hne C hfour hC.2 with rfl | rfl
        · exact le_rfl
        · exact (hnot hC.1).elim
      · exact le_sSup ⟨hAΩ, hAT⟩
    have hnorm : normalizer (A : Set (PSL2 F)) ≤ normalizer (B : Set (PSL2 F)) := by
      simpa only [hW, hMB] using hNM
    exact hne (normalizer_le_eq hF A B hA hB hnorm)
  let := hB
  obtain ⟨C, hCT, hC, hCB, h8, hnorm, hnon⟩ := paired_four_of_normalizers T
    (by rw [sylow_card hF T]) (fun A _ hA => normalizer_equiv hF A hA) B hBT
  have hescape : ¬ normalizer (C : Set (PSL2 F)) ≤ M := by
    intro h
    rw [hMB] at h
    exact hCB (normalizer_le_eq hF C B hC hB h)
  obtain ⟨eC⟩ := normalizer_equiv hF C hC
  exact ⟨B, hBΩ, hBT, hB, PrimeGeometry.Inner.local_witness_of_symmetric_four
    T B (B ⊔ C) (normalizer (C : Set (PSL2 F))) M
    (le_sup_left.trans hnorm) (sup_le hBT hCT) hnorm h8 eC hnon hescape⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.InnerPlacement.Nine
