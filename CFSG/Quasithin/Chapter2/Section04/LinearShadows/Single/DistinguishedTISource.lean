module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CoreIntersectionSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.OutsideFixedSource
public import Theory.GroupTheory.ElementaryThompsonFrattini

/-!
# TI in the centerless single-block branch

First Z(R) lies in Z(O₂(M)). If R is not in O₂(M), the torus interval
calculation identifies Ω₁(R ∩ O₂(M)) with Z(R). An extra involution in
Ω₁Z(O₂(M)) would have its commutator with R both inside and strictly
above Z(R), a contradiction. Thus M normalizes Z(R). Maximality and the
regular torus orbit then give its full normalizer and the TI property.

Source: Aschbacher–Smith, 2.4.18, printed p.534. The earlier identity
C_S(Z)=R remains explicit here and is discharged in DistinguishedGeometrySource.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- In the centerless case, the characteristic-two core and the strict
outside commutator force Z(R) to be normal in M. The sole earlier input
is the exact centralizer identity from 2.4.17. -/
theorem source_centerless_distinguished_normalizer_contains
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype) = ⊥)
    (hCS : ((d.S : Subgroup d.H).map d.H.subtype) ⊓ centralizer (distinguishedZ d : Set G) =
      Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)) :
    M ≤ normalizer (distinguishedZ d : Set G) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let Z := distinguishedZ d
  let P := twoCore M
  let C := P ⊓ centralizer (P : Set G)
  let W := omegaOneAmbient C
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hRT : R ≤ (T : Subgroup G) := (sSup_le fun _ h => h.1).trans hST.le
  have hTR := (d.lemma_2_4_8_1 hG T hST hsingle hK).2.2
  have hPT : P ≤ (T : Subgroup G) := by
    change twoCore M ≤ (T : Subgroup G)
    simpa only [twoCore_eq_pCoreIn,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM]
      using pCoreIn_le_sylow M (T.subtype hTM)
  have hMP : M ≤ normalizer (P : Set G) := le_normalizer_twoCore M
  by_cases hRP : R ≤ P
  · have hJT : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) = R :=
      (d.single_natural_global_source hG T hST hsingle hK).2.1.symm
    have hJP : Stellmacher.elementaryAbelianMaxJ P = R :=
      (Stellmacher.elementaryAbelianMaxJ_eq_of_intermediate (T : Subgroup G) P
        (hJT ▸ hRP) hPT).trans hJT
    have hMR : M ≤ normalizer (R : Set G) := hJP ▸
      (hMP.trans (Stellmacher.normalizer_le_normalizer_elementaryAbelianMaxJ P))
    rw [distinguishedZ_of_centerless d hz]
    exact (le_inf hMR (hMR.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hb := source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique
  let : IsElementaryAbelian 2 Z := hb.1
  have hZC : Z ≤ C :=
    (source_centerless_distinguished_core_center d hG T hST hsingle hL hM hTM hunique hz).1
  have hZP : Z ≤ P := hZC.trans inf_le_left
  have hMC : M ≤ normalizer (C : Set G) :=
    (le_inf hMP (hMP.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  let : (omega₁ C (p := 2)).Characteristic := omega₁_characteristic C
  have hMW : M ≤ normalizer (W : Set G) := hMC.trans
    (normalizer_le_normalizer_characteristic_image C (omega₁ C (p := 2)))
  let : IsMulCommutative C := le_centralizer_iff_isMulCommutative.mp
    ((show C ≤ centralizer (P : Set G) from inf_le_right).trans (centralizer_le inf_le_left))
  let : IsElementaryAbelian 2 (omega₁ C (p := 2)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative C
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map C.subtype
  have hWP : W ≤ P := (omegaOneAmbient_le C).trans inf_le_left
  have hZW : Z ≤ W := by
    rw [← omegaOneAmbient_eq_self Z]
    exact omegaOneAmbient_mono hZC
  have hWRZ : W ⊓ R ≤ Z := by
    intro a ha
    change a ∈ distinguishedZ d
    rw [← source_centerless_core_intersection_omega d hG T hST hsingle hL hM hTM hunique hz hRP]
    exact (omegaOneAmbient_le_iff _ _).mp le_rfl a ⟨ha.2,hWP ha.1⟩
      (elemPow_eq_one_of_isElementaryAbelian a ha.1)
  have hWZ : W ≤ Z := by
    by_contra hnot
    obtain ⟨t,htW,htZ⟩ := SetLike.not_le_iff_exists.mp hnot
    have htT : t ∈ T := hPT (hWP htW)
    have htR : t ∉ R := fun htR => htZ (hWRZ ⟨htW,htR⟩)
    have htC : t ∈ centralizer (Z : Set G) :=
      centralizer_le hZP (omegaOneAmbient_le C htW).2
    have htS : t ∉ S := by
      intro htS
      apply htR
      change t ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
      rw [← hCS]
      exact ⟨htS,htC⟩
    have ht2 : t^2=1 := elemPow_eq_one_of_isElementaryAbelian t htW
    have hout := source_outside_involution_center_fixed d hG T hST hsingle hL hM hTM hunique
      t htT htS ht2 (by simpa only [Z,distinguishedZ_of_centerless d hz] using htC)
    have hcomW : ⁅R,zpowers t⁆ ≤ W :=
      (commutator_mono le_rfl (zpowers_le.mpr htW)).trans
        (le_normalizer_iff_commutator_le_right.mp (hRT.trans (hTM.trans hMW)))
    have hcomR : ⁅R,zpowers t⁆ ≤ R :=
      le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr (hTR htT))
    have hcomZ : ⁅R,zpowers t⁆ ≤ Z := (le_inf hcomW hcomR).trans hWRZ
    change ⁅R,zpowers t⁆ ≤ distinguishedZ d at hcomZ
    rw [distinguishedZ_of_centerless d hz] at hcomZ
    exact (not_le_of_gt hout.2) hcomZ
  change M ≤ normalizer (Z : Set G)
  exact (le_antisymm hWZ hZW) ▸ hMW

/-- Original 2.4.18, centerless branch. All centralizer and normality
premises are constructed; only the original 2.4.17 identity is retained. -/
theorem source_centerless_distinguished_TI
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype) = ⊥)
    (hCS : ((d.S : Subgroup d.H).map d.H.subtype) ⊓ centralizer (distinguishedZ d : Set G) =
      Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)) :
    ChapterI.Section06To08.IsTISubgroup (distinguishedZ d) ∧
      normalizer (distinguishedZ d : Set G) = M := by
  let Z := distinguishedZ d
  have hb := source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique
  let : IsElementaryAbelian 2 Z := hb.1
  have hZn : Z ≠ ⊥ := by
    intro he
    have hc : Nat.card Z=2^n := hb.2.1
    rw [he,card_bot] at hc
    have hh : 1<2^n := Nat.one_lt_pow (by have hn := hL.1; omega) (by decide)
    omega
  have hMN := source_centerless_distinguished_normalizer_contains d hG T hST hsingle hL hM hTM hunique hz hCS
  have hn : normalizer (Z : Set G) = M := le_antisymm
    (hM.2 ⟨Z,hZn,IsElementaryAbelian.isPGroup 2 Z,rfl⟩ hMN) hMN
  refine ⟨?_,hn⟩
  have hc := (source_centerless_distinguished_core_center d hG T hST hsingle hL hM hTM hunique hz).2
  apply ChapterI.Section06To08.lemma_I_6_1_1 Z M hn.symm hc
  intro z w hzZ hwZ hconj
  by_cases hz1 : z=1
  · obtain ⟨a,ha⟩ := hconj
    have hw1 : w=1 := by simpa only [hz1,mul_one,mul_inv_cancel] using ha.symm
    exact ⟨1,by simp only [OneMemClass.coe_one,inv_one,mul_one,hz1,hw1]⟩
  have hw1 : w≠1 := by
    rintro rfl
    obtain ⟨a,ha⟩ := hconj
    exact hz1 ((MulAut.conj a).injective (ha.trans (map_one _).symm))
  obtain ⟨D,B,hDM,hDB,_,hcard,_,hodd,_,_,hBR,_,_,_,_,_,_,_,_,_,_,_,_⟩ :=
    source_fixed_free_torus d hG T hST hsingle hL hM hTM hunique
  have hr := source_centerless_torus_regular d hG T hST hsingle hL hM hTM hunique hz
    D (hDM.trans inf_le_right) (hodd.of_dvd_nat (card_dvd_of_le hDB)) hcard (hDB.trans hBR)
  have hZeq := distinguishedZ_of_centerless d hz
  obtain ⟨a,ha,_⟩ := hr.2 z (hZeq.le hzZ) hz1 w (hZeq.le hwZ) hw1
  exact ⟨⟨a,(hDM.trans inf_le_left) a.property⟩,ha⟩
end CFSG.Quasithin.Chapter2.LinearShadows.Single
