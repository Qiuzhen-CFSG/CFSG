module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.DistinguishedSource
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2SylowFixedCenter
public import CFSG.Quasithin.ChapterI.Section06To08.TIConjugates

/-!
# The two original central factors in the nontrivial-center branch

The 2.4.4 normalizer calculation separates Z from its outside conjugate.
Their TI intersection is trivial. The natural Sylow-fixed bound gives the
opposite order inequality, so their direct product fills Z(R).

Source: Aschbacher–Smith, 2.4.16(2), printed p.533.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_distinguished_normalizer_in_sylow
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype) ≠ ⊥) :
    (T : Subgroup G) ⊓ normalizer (distinguishedZ d : Set G) =
      (d.S : Subgroup d.H).map d.H.subtype := by
  let L := d.block.map d.H.subtype
  have hb := source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique
  have hRS : Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ≤
      (d.S : Subgroup d.H).map d.H.subtype := sSup_le fun _ h => h.1
  have hZS := (hb.2.2.1.trans inf_le_left).trans hRS
  have hZn : distinguishedZ d ≠ ⊥ := by
    rw [distinguishedZ_of_center_ne_bot d hz]
    exact (map_eq_bot_iff_of_injective _ L.subtype_injective).not.mpr hz
  let : d.block.Normal := hsingle ▸ d.L0_normal
  have hHL : d.H ≤ normalizer (L : Set G) := by
    have hh := d.block.le_normalizer_map d.H.subtype
    rwa [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
  have hHZ : d.H ≤ normalizer (distinguishedZ d : Set G) := by
    rw [distinguishedZ_of_center_ne_bot d hz]
    exact hHL.trans (normalizer_le_normalizer_characteristic_image L (center L))
  exact lemma_2_4_4 d.mem_gammaEvenZero.1 d.full_pair d.S le_rfl T hST.le
    (distinguishedZ d) hZn hZS (normal_subgroupOf_of_le_normalizer hHZ)

/-- In the nontrivial-center branch, the two distinct conjugates of the
original Z are disjoint and generate the whole center of R. -/
theorem source_distinguished_center_pair
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    (x : G) (hxT : x ∈ T) (hxS : x ∉ (d.S : Subgroup d.H).map d.H.subtype) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let Z := distinguishedZ d
    Disjoint Z (Z.map (MulAut.conj x⁻¹).toMonoidHom) ∧
      Z ⊔ Z.map (MulAut.conj x⁻¹).toMonoidHom = R ⊓ centralizer (R : Set G) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let Z := distinguishedZ d
  let A := R ⊓ centralizer (R : Set G)
  let U := sourceModule L
  let e := MulAut.conj x⁻¹
  have hb := source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique
  have hZA : Z ≤ A := hb.2.2.1
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hTR := (d.lemma_2_4_8_1 hG T hST hsingle hK).2.2
  have hTA : (T : Subgroup G) ≤ normalizer (A : Set G) :=
    (le_inf hTR (hTR.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hAe : A.map e.toMonoidHom = A :=
    mem_normalizer_iff_map_conj_eq.mp (hTA (T.inv_mem hxT))
  have hZxA : Z.map e.toMonoidHom ≤ A := (map_mono hZA).trans_eq hAe
  have hTI := (source_distinguished_TI_of_center_ne_bot d hG T hST hsingle hL hM hTM hunique hz).1
  have hd : Disjoint Z (Z.map e.toMonoidHom) := by
    rcases hTI.eq_or_disjoint_conjugate x⁻¹ with he | hd
    · have hn : x⁻¹ ∈ normalizer (Z : Set G) := mem_normalizer_iff_map_conj_eq.mpr he
      have hm : x⁻¹ ∈ S := by
        change x⁻¹ ∈ (d.S : Subgroup d.H).map d.H.subtype
        rw [← source_distinguished_normalizer_in_sylow d hG T hST hsingle hL hM hTM hunique hz]
        exact ⟨T.inv_mem hxT,hn⟩
      exact False.elim (hxS (by simpa only [inv_inv] using S.inv_mem hm))
    · exact hd.symm
  have hp := source_absorbed_center_pair d hG T hST hsingle hL hM hTM hunique x hxT hxS
  have hAU : A ≤ U := hp.ge.trans inf_le_left
  let : IsElementaryAbelian 2 U := by
    let := hK.2.1.elementary
    exact IsElementaryAbelian.map L.subtype
  let : IsElementaryAbelian 2 A :=
    IsElementaryAbelian.of_injective (inclusion hAU) (inclusion_injective hAU)
  have hnorm : Z.map e.toMonoidHom ≤ normalizer (Z : Set G) :=
    (hZxA.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)).trans
      ((centralizer_le hZA).trans (Subgroup.centralizer_le_normalizer _))
  have hprod : Nat.card (Z ⊔ Z.map e.toMonoidHom : Subgroup G) = 2^n * 2^n := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint Z _ hnorm hd,
      card_map_of_injective e.injective,hb.2.1]
  have hbound : Nat.card A ≤ 2^n * 2^n := by
    have hRL : R ≤ L := (source_core_absorption d hG T hST hsingle hL hM hTM hunique).1
    have hAL := (show A ≤ R from inf_le_left).trans hRL
    obtain ⟨P,hP⟩ := (source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique).2.2.1
    change (P : Subgroup L).map L.subtype = R at hP
    have hEU : A.subgroupOf L ≤ ChapterC.blockU L := by
      intro a ha
      obtain ⟨b,hb,he⟩ := hAU ha
      exact (Subtype.ext he : b=a) ▸ hb
    have hEP : A.subgroupOf L ≤ centralizer (P : Set L) := by
      intro a ha p hp
      exact Subtype.ext ((mem_centralizer_iff.mp ha.2) p
        (by rw [← hP]; exact mem_map_of_mem L.subtype hp))
    have hZE : center L ≤ A.subgroupOf L := by
      intro z hz'
      apply hZA
      change (z : G) ∈ distinguishedZ d
      rw [distinguishedZ_of_center_ne_bot d hz]
      exact mem_map_of_mem L.subtype hz'
    have hc := hK.card_le_of_sylow_fixed P (A.subgroupOf L) hEU hEP hZE
    rw [Nat.card_congr (subgroupOfEquivOfLe hAL).toEquiv] at hc
    have hcZ : Nat.card (center L) = 2^n := by
      rw [← card_map_of_injective L.subtype_injective]
      exact (distinguishedZ_of_center_ne_bot d hz) ▸ hb.2.1
    rwa [hcZ] at hc
  exact ⟨hd,eq_of_le_of_card_ge (sup_le hZA hZxA) (hprod ▸ hbound)⟩
end CFSG.Quasithin.Chapter2.LinearShadows.Single
