module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.DistinguishedSource
public import CFSG.Quasithin.ChapterI.Section06To08.TIConjugates
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterPairSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.OutsideFixedSource

/-!
# The upper bound in the original weak closure

The index-two source geometry makes the mutual normalizer nontrivial,
so the elementary TI-pair theorem forces commutation. The outside fixed
calculation then traps a nontrivial intersection in Z, and TI finishes.
The final application retains precisely 2.4.18 and C_S(Z)=R from 2.4.17.
Source: Aschbacher–Smith, 2.4.19, printed p.534.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The containment half of original 2.4.19. Its explicit inputs are exactly
the TI result 2.4.18 and the centralizer alternative 2.4.17(1). -/
theorem source_distinguished_conjugate_le_thompson
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hTI : ChapterI.Section06To08.IsTISubgroup (distinguishedZ d))
    (hindex :
      (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)).relIndex
        ((T : Subgroup G) ⊓ centralizer (distinguishedZ d : Set G)) ≤ 2)
    (hfixed :
      let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
      ∀ t ∈ T, t ∉ R → t^2=1 → t ∈ centralizer (distinguishedZ d : Set G) →
        R ⊓ centralizer ({t} : Set G) ≤ distinguishedZ d)
    (g : G) (hg : (distinguishedZ d).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G)) :
    (distinguishedZ d).map (MulAut.conj g).toMonoidHom ≤
      Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let Z := distinguishedZ d
  let E := Z.map (MulAut.conj g).toMonoidHom
  have hb := source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique
  let : IsElementaryAbelian 2 Z := hb.1
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hRS : R ≤ S := sSup_le fun _ h => h.1
  have hZR : Z ≤ R := hb.2.2.1.trans inf_le_left
  have hZT : Z ≤ (T : Subgroup G) := hZR.trans (hRS.trans hST.le)
  have hq : 2 < Nat.card Z := by
    rw [hb.2.1]
    have hn := hL.1
    have h4 : 2^2 ≤ 2^n := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hiS : S.relIndex (T : Subgroup G) = 2 := (d.lemma_2_4_8_1 hG T hST hsingle hK).1
  have hiN : (normalizer (Z : Set G)).relIndex (T : Subgroup G) ≤ 2 := by
    have hh := relIndex_le_of_le_left (L := (T : Subgroup G)) hb.2.2.2
      (show S.relIndex (T : Subgroup G) ≠ 0 by rw [hiS]; decide)
    exact hh.trans_eq hiS
  have hEC : E ≤ centralizer (Z : Set G) :=
    hTI.conjugate_le_centralizer_of_index Z (T : Subgroup G) T.isPGroup' hZT
      (hiN.trans_lt hq) g hg
  have hEinside : E ≤ (T : Subgroup G) ⊓ centralizer (Z : Set G) := le_inf hg hEC
  have hcard : Nat.card E = Nat.card Z := card_map_of_injective (MulAut.conj g).injective
  by_contra hnot
  obtain ⟨t,htE,htR⟩ := SetLike.not_le_iff_exists.mp hnot
  have ht2 : t^2=1 := elemPow_eq_one_of_isElementaryAbelian t htE
  have hER : E ⊓ R ≠ ⊥ := by
    intro hh
    have hhidx := relIndex_le_of_le_right (H := R) hEinside
      (show R.relIndex ((T : Subgroup G) ⊓ centralizer (Z : Set G)) ≠ 0 from index_ne_zero_of_finite)
    rw [← inf_relIndex_right,inf_comm,hh,relIndex_bot_left,hcard] at hhidx
    exact (not_lt_of_ge (hhidx.trans hindex)) hq
  have hERZ : E ⊓ R ≤ Z := by
    intro a ha
    apply hfixed t (hg htE) htR ht2 (hEC htE)
    exact ⟨ha.2,mem_centralizer_singleton_iff.mpr
      (show a*t=t*a from congrArg Subtype.val (mul_comm (⟨a,ha.1⟩ : E) (⟨t,htE⟩ : E)))⟩
  rcases hTI.eq_or_disjoint_conjugate g with he | hd
  · apply hnot
    change (distinguishedZ d).map (MulAut.conj g).toMonoidHom ≤ R
    rw [he]
    exact hZR
  · apply hER
    apply eq_bot_iff.mpr
    intro a ha
    exact hd.le_bot ⟨ha.1,hERZ ha⟩

/-- The actual 2.4.19 containment, with only the earlier TI theorem and
C_S(Z)=R retained. The rest of 2.4.17 is reconstructed from the source index
and the proved outside-involution calculation. -/
theorem source_distinguished_conjugate_le_of_sylow_centralizer
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hTI : ChapterI.Section06To08.IsTISubgroup (distinguishedZ d))
    (hCS : ((d.S : Subgroup d.H).map d.H.subtype) ⊓ centralizer (distinguishedZ d : Set G) =
      Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))
    (g : G) (hg : (distinguishedZ d).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G)) :
    (distinguishedZ d).map (MulAut.conj g).toMonoidHom ≤
      Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let Z := distinguishedZ d
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hiS : S.relIndex (T : Subgroup G) = 2 := (d.lemma_2_4_8_1 hG T hST hsingle hK).1
  apply source_distinguished_conjugate_le_thompson d hG T hST hsingle hL hM hTM hunique hTI ?_ ?_ g hg
  · have hi := relIndex_le_of_le_right (H := S)
      (show (T : Subgroup G) ⊓ centralizer (Z : Set G) ≤ (T : Subgroup G) from inf_le_left)
      (show S.relIndex (T : Subgroup G) ≠ 0 by rw [hiS]; decide)
    have he : S ⊓ ((T : Subgroup G) ⊓ centralizer (Z : Set G)) = R := by
      rw [← inf_assoc,inf_eq_left.mpr hST.le]
      exact hCS
    rw [← inf_relIndex_right,he] at hi
    simpa only [hiS] using hi
  · dsimp only
    intro t htT htR ht2 htZ
    have htS : t ∉ S := by
      intro htS
      apply htR
      rw [← hCS]
      exact ⟨htS,htZ⟩
    by_cases hz : center (d.block.map d.H.subtype) = ⊥
    · rw [distinguishedZ_of_centerless d hz] at htZ ⊢
      exact (source_outside_involution_center_fixed d hG T hST hsingle hL hM hTM hunique
        t htT htS ht2 htZ).1.le
    · have hn := source_distinguished_normalizer_in_sylow d hG T hST hsingle hL hM hTM hunique hz
      have ht : t ∈ S := by
        change t ∈ (d.S : Subgroup d.H).map d.H.subtype
        rw [← hn]
        exact ⟨htT,Subgroup.centralizer_le_normalizer _ htZ⟩
      exact False.elim (htS ht)
end CFSG.Quasithin.Chapter2.LinearShadows.Single
