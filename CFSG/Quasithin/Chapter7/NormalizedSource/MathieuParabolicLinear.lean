module
public import CFSG.Quasithin.ChapterE.Section02.Structure.LinearThree.Placement
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.RootScalars
public import CFSG.Quasithin.ChapterE.Section02.Structure.NormalSimpleImage
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The linear-three field bound in the M24 parabolic sieve

The nonzero elementary subgroup in the original maximal-core quotient
lies in the marked highest-root group. The actual Borel normalizes it;
its scalar transitivity therefore fills that root group. Its cardinality
bounds the field order. Mapping the original four-element image from
X/O₂(X) to X/core(M) now bounds the field exponent by two, without any
asserted equality of generation parameters across a quotient.

The consumer is `MathieuParabolicSieve.normal_component_bender` and its
literal chosen-module application in `NonFFSourceMathieuM24Sieve`.
Source: Aschbacher--Smith E.2.2/E.2.7, pp.215--219, and 8.2.9, p.720,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSieve
open ChapterB ChapterE
open Matrix.PSL3.LinearThree Matrix.PSL3.LinearThree.RootScalars
open Matrix.PSL3Even.MinimalParabolicWitness Matrix.PSL3Even.UnipotentGeometry
variable {X : Type*} [Group X] [Finite X]
set_option backward.isDefEq.respectTransparency false

/-- An elementary subgroup normalized by the actual maximal Borel fills
its long-root group. In particular the field order is bounded by its size. -/
theorem linear_three_field_le_card
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (K : Subgroup X) [K.Normal] [IsSimpleGroup K] (e : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (S : Sylow 2 X) (hgen : K ⊔ (S : Subgroup X) = ⊤)
    (hP : IsMinimalParabolicOver S ⊤) (hcore : minimalParabolicCore S hP = ⊥)
    (W : Subgroup X) [IsElementaryAbelian 2 W]
    (hWS : W ≤ S) (hne : W ≠ ⊥)
    (hMW : minimalParabolicMax S hP ≤ normalizer (W : Set X)) :
    2^n ≤ Nat.card W := by
  have hSW := (minimalParabolicMax_spec S hP).2.trans hMW
  obtain ⟨g,hU,hB,hplace⟩ := Structure.LinearThree.exists_longRoot_placement
    F hn hF K e S hgen hP hcore W hWS hSW
  let f := modelEmbedding F K (e.trans (MulAut.conj g))
  have hf := modelEmbedding_injective F K (e.trans (MulAut.conj g))
  let P := unipotentSylow F hn hF
  have hz : (center P).map (P : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)).subtype =
      projectiveCenter F := (projectiveCenter_eq_mapped_center F).symm
  have hex : ∃ w : X, w ∈ W ∧ w ≠ 1 := by
    by_contra! he
    exact hne (eq_bot_iff.mpr he)
  obtain ⟨w,hw,hwn⟩ := hex
  obtain ⟨z,hzroot,hzw⟩ := hplace hw
  have hzn : z ≠ 1 := by intro he; exact hwn (hzw.symm.trans (he ▸ f.map_one))
  have hroot : (projectiveCenter F).map f ≤ W := by
    rintro _ ⟨y,hy,rfl⟩
    by_cases hy1 : y = 1
    · simpa only [hy1,map_one] using W.one_mem
    obtain ⟨b,hb,hby⟩ := sylow_center_nonidentity_transitive F hn hF (MulEquiv.refl _) P
      z (hz.symm ▸ hzroot) hzn y (hz.symm ▸ hy) hy1
    have hbB : b ∈ borel F := by
      change b ∈ normalizer (unipotent F : Set _) at hb
      rwa [normalizer_unipotent F hn hF] at hb
    have hbM : f b ∈ minimalParabolicMax S hP := by
      change b ∈ (minimalParabolicMax S hP).comap f
      rw [hB]
      exact hbB
    have hh := (mem_normalizer_iff.mp (hMW hbM) w).mp hw
    rw [←hzw] at hh
    change f b * f z * (f b)⁻¹ ∈ W at hh
    rw [←map_inv,←map_mul,←map_mul,hby] at hh
    exact hh
  have heq : W = (projectiveCenter F).map f := le_antisymm hplace hroot
  have hc : Nat.card (projectiveCenter F) = Nat.card F := by
    rw [←root_range F]
    exact (Nat.card_congr (MonoidHom.ofInjective (root_injective F)).toEquiv).symm
  rw [heq,card_map_of_injective hf,hc,hF]

/-- The original elementary image of size at most four bounds the linear
field exponent, through the literal maximal-core quotient. -/
theorem source_linear_three_degree_le_two
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (hs : ¬Group.IsSolvable X)
    (K : Subgroup X) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (S : Subgroup X) = ⊤) {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL (K.map (QuotientGroup.mk' (minimalParabolicCore S hP))) 3 (2^n))
    (W : Subgroup X) [IsElementaryAbelian 2 W] (hWS : W ≤ S)
    (hout : ¬W ≤ minimalParabolicCore S hP)
    (hMW : minimalParabolicMax S hP ≤ normalizer (W : Set X))
    (hcard : Nat.card (W.map (QuotientGroup.mk' (pCore 2 X))) ≤ 4) : n ≤ 2 := by
  let J := minimalParabolicCore S hP
  let q := QuotientGroup.mk' J
  let R := S.mapSurjective (QuotientGroup.mk'_surjective J)
  let A := W.map q
  let D := K.map q
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map q
  have hi := Structure.source_normal_simple_image S hP hs K hK hgen
  have hmin := (Structure.source_star_minimal_core_free S hP).1
  have hcore := (Structure.source_star_minimal_core_free S hP).2
  have hmax : minimalParabolicMax R hmin = (minimalParabolicMax S hP).map q :=
    (minimalParabolicMax_map_core S hP q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk'])).symm
  have hAM : minimalParabolicMax R hmin ≤ normalizer (A : Set (X ⧸ J)) := by
    rw [hmax]
    exact (map_mono hMW).trans (le_normalizer_map q)
  have hAn : A ≠ ⊥ := by
    intro he
    exact hout (by simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff W).mp he)
  let f : (X ⧸ pCore 2 X) →* (X ⧸ J) := QuotientGroup.map _ _ (MonoidHom.id X)
    (by simpa using minimalParabolicTwoCore_le_core S hP)
  have hmap : (W.map (QuotientGroup.mk' (pCore 2 X))).map f = A := by
    rw [map_map]; rfl
  have hsmall : Nat.card A ≤ 4 := by
    rw [←hmap]
    exact (Nat.le_of_dvd Nat.card_pos (card_dvd_of_surjective
      (f.subgroupMap _) (f.subgroupMap_surjective _))).trans hcard
  obtain ⟨F,hF,hfin,hsize,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hsize)
  let : D.Normal := hi.2.2.1
  let : IsSimpleGroup D := hi.1
  have hpow := (linear_three_field_le_card F hn hsize D e R hi.2.2.2 hmin hcore
    A (map_mono hWS) hAn hAM).trans hsmall
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSieve
