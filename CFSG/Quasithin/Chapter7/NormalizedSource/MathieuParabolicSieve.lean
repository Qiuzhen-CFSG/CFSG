module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuParabolicLinear
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import CFSG.Quasithin.ChapterE.Section02.Structure.OriginalNormal
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.OddFamilies
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.PairedMarked
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.OddTwo
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.OddThree
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Classical.Generation
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.NumericalBinarySix
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.NumericalPairedPrime
public import CFSG.Quasithin.ChapterE.Section02.Structure.PairedCore
public import Theory.SpecificGroups.Classical.PairedOddRank
public import Theory.SpecificGroups.Suzuki.LinearSeparation
public import CFSG.Quasithin.ChapterA.Section02.OddCenterCovers
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The non-Bender rows of the original M24 quotient sieve

For the actual minimal parabolic X with n(X)>1, cubic rank at most one,
and a maximal-invariant elementary image of size at most four, the full
E.2.2 catalogue supplies a normal Bender component. The odd rows have
proved generation bounds at one through the full solvable core. The
linear-three field bound and cubic witnesses exclude the other normal
rows. Exchanged binary-linear factors have cubic rank two; exchanged
Suzuki factors are three-free after the proved paired-core identification.

The final transport identifies the full residual in X/O₂(X), its center
as the image of the original maximal core, and its central quotient with
the actual star component. The concrete application, including all rank,
normalization and cardinal premises, is `NonFFSourceMathieuM24Sieve`.
The remaining Bender field restriction and central-cover elimination stay
with qt-d-1222-nonff-mathieu; no full 8.2.9 conclusion is asserted here.
Source: Aschbacher--Smith E.2.2, pp.215--216, and 8.2.9, p.720,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSieve
open ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open BenderSuzuki.MatrixGroups
variable {X : Type*} [Group X] [Finite X]
set_option backward.isDefEq.respectTransparency false

private theorem star_three_rank_le_one
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (h3 : primeRank 3 X ≤ 1) : primeRank 3 (X ⧸ minimalParabolicCore S hP) ≤ 1 := by
  let P : Sylow 3 X := Classical.choice inferInstance
  exact P.primeRank_quotient_le_one (P.isCyclic_of_odd_of_primeRank_le_one (by decide) h3) _

/-- All normal-component rows other than Bender are excluded on the
original parameter and the actual four-element elementary image. -/
private theorem normal_component_bender
    (hX : IsSQTK KnownSimple.IsKnownSimple X)
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (hs : ¬Group.IsSolvable X)
    (K : Subgroup X) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (S : Subgroup X) = ⊤) (hparam : 1 < generationParameter X)
    (h3 : primeRank 3 X ≤ 1)
    (W : Subgroup X) [IsElementaryAbelian 2 W] (hWS : W ≤ S)
    (hout : ¬W ≤ minimalParabolicCore S hP)
    (hMW : minimalParabolicMax S hP ≤ normalizer (W : Set X))
    (hcard : Nat.card (W.map (QuotientGroup.mk' (pCore 2 X))) ≤ 4) :
    ClassificationModels.IsBenderModel
      (K.map (QuotientGroup.mk' (minimalParabolicCore S hP))) := by
  have hr : primeRank 3 (K.map (QuotientGroup.mk' (minimalParabolicCore S hP))) ≤ 1 :=
    (primeRank_subgroup_le 3 _).trans (star_three_rank_le_one S hP h3)
  rcases source_normal_geometric_cases ChapterA.Section02.theoremA_knownSimple
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hX S hP hs K hK hgen with
    h2 | hodd3 | hb | hl | hsp | hbi
  · obtain ⟨p,d,hp,hp3,hd,hd2,hmod,F,hF,hfin,hsize,e,_⟩ := h2
    have ho : Odd p := hp.odd_of_ne_two (by omega)
    have hlarge : 5 < p^d := by
      rcases (show d=1 ∨ d=2 by omega) with hd | hd
      · subst d; simp only [pow_one] at hmod ⊢; omega
      · subst d; nlinarith
    have hu := Structure.NumericalBounds.normal_odd_two_upper
      ChapterA.Section02.theoremA_knownSimple hX S hP hs K hK hgen ho.pow hlarge
      ⟨F,hF,hfin,hsize,⟨e⟩⟩
    omega
  · obtain ⟨p,hp,ho,_,hu | hl⟩ := hodd3
    · have hh := Structure.NumericalBounds.normal_odd_three_upper
        ChapterA.Section02.theoremA_knownSimple hX S hP hs K hK hgen hp ho (.inr hu.2)
      omega
    · obtain ⟨_,F,hF,hfin,hsize,e,_⟩ := hl
      have hh := Structure.NumericalBounds.normal_odd_three_upper
        ChapterA.Section02.theoremA_knownSimple hX S hP hs K hK hgen hp ho
        (.inl ⟨F,hF,hfin,hsize,⟨e⟩⟩)
      omega
  · exact hb
  · obtain ⟨n,hn,hm⟩ := hl
    have hn2 := source_linear_three_degree_le_two S hP hs K hK hgen (by omega) hm
      W hWS hout hMW hcard
    rcases (show n=1 ∨ n=2 by omega) with rfl | rfl
    · have he := Structure.NumericalBounds.normal_classical_isEGenerated
        ChapterA.Section02.theoremA_knownSimple hX S hP hs K hK hgen
        (.inr (.inr ⟨by decide,hm⟩))
      have hh := generationParameter_le (by decide) he
      omega
    · have hh := ChapterA.Section02.OddCenterCovers.linear_threeRank_eq_two (by decide) hm
      change primeRank 3 (K.map (QuotientGroup.mk' (minimalParabolicCore S hP))) = 2 at hh
      omega
  · obtain ⟨n,_,F,hF,hfin,hsize,⟨e⟩⟩ := hsp
    have hh := Theory.SpecificGroups.Classical.PairedOddRank.psp_binary_three_rank hsize
    rw [←primeRank_equiv 3 e] at hh
    change 2 ≤ primeRank 3 (K.map (QuotientGroup.mk' (minimalParabolicCore S hP))) at hh
    omega
  · have hh := normal_binary_six_parameter_le S hP hs K hK hgen hbi
    omega

/-- The exchanged binary-linear row has two independent cubic directions;
the exchanged Suzuki row is three-free in the full original core quotient. -/
private theorem not_exchanged_bender
    (hX : IsSQTK KnownSimple.IsKnownSimple X)
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (hs : ¬Group.IsSolvable X)
    (K : Subgroup X) (hK : K.IsCComponent) (hqs : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (S : Subgroup X) = ⊤) (hn : ¬K.Normal)
    (h3 : primeRank 3 X ≤ 1) (hdiv : 3 ∣ Nat.card (X ⧸ pCore 2 X))
    {n : ℕ} (hm : ExchangedModel (minimalParabolicMax S hP) K n) : False := by
  let J := minimalParabolicCore S hP
  let q := QuotientGroup.mk' J
  let R := S.mapSurjective (QuotientGroup.mk'_surjective J)
  let B := K.map q
  let : Group.IsSolvable J := minimalParabolic_core_solvable S hP
  have hi := Structure.source_component_simple_image S hP hs K hK hgen
  have hnB : ¬B.Normal := fun hh => hn (cComponent_normal_of_quotient_normal hK J hh)
  obtain ⟨t,_,_,_,hres,⟨e,_⟩,_,_⟩ := Structure.source_pair_coordinates
    (Structure.source_star_sqtk ChapterA.Section02.theoremA_knownSimple hX S hP hs).stronglyQuasithin
    R (Structure.source_star_minimal_core_free S hP).1
    (fun hh => hs ((Group.isSolvable_iff_subgroup_quotient J).mpr ⟨inferInstance,hh⟩))
    (Structure.source_star_minimal_core_free S hP).2 hi.2.1 (hK.map_quotient J) hi.2.2.2 hnB
  let C := B.map (MulAut.conj (t : X ⧸ J)).toMonoidHom
  rcases hm with ⟨F,hF,hfin,hchar,_,hsize,b,_⟩ | ⟨m,hm,_,b,_⟩
  · have hd : 3 ∣ Nat.card B := by
      change 3 ∣ Nat.card (sourceImage (minimalParabolicMax S hP) K)
      rw [Nat.card_congr b.toEquiv]
      exact three_dvd_card_psl2_char_two F
    have hpos : 1 ≤ primeRank 3 B := Nat.one_le_iff_ne_zero.mpr
      (fun he => (PrimeRank.eq_zero_iff_not_dvd_card.mp he) hd)
    have hc : primeRank 3 B = primeRank 3 C :=
      primeRank_equiv 3 ((MulAut.conj (t : X ⧸ J)).subgroupMap B)
    have hr : 2 ≤ primeRank 3 (B ⊔ C : Subgroup (X ⧸ J)) := by
      rw [←primeRank_equiv 3 e,primeRank_prod_eq_add]
      change 2 ≤ primeRank 3 B + primeRank 3 C
      omega
    have hu := (primeRank_subgroup_le 3 (B ⊔ C)).trans (star_three_rank_le_one S hP h3)
    omega
  · have hB3 : ¬3 ∣ Nat.card B := by
      change ¬3 ∣ Nat.card (sourceImage (minimalParabolicMax S hP) K)
      rw [Nat.card_congr b.toEquiv]
      exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m (by omega)
    have hCcard : Nat.card C = Nat.card B :=
      card_map_of_injective (MulAut.conj (t : X ⧸ J)).injective
    have hR3 : ¬3 ∣ Nat.card (pResidual 2 (X ⧸ J)) := by
      rw [hres,←Nat.card_congr e.toEquiv,Nat.card_prod]
      change ¬3 ∣ Nat.card B * Nat.card C
      rw [hCcard]
      exact fun hh => (Nat.prime_three.dvd_mul.mp hh).elim hB3 hB3
    have hJ : J = pCore 2 X := Structure.PairedCore.source
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple) hX S hP hs hK hqs hgen hn
    have hd : 3 ∣ Nat.card (X ⧸ J) := hJ ▸ hdiv
    obtain ⟨k,hk⟩ := (isPGroup_quotient_pResidual (G := X ⧸ J) 2).exists_card_eq
    have hi3 : ¬3 ∣ (pResidual 2 (X ⧸ J)).index := by
      rw [index_eq_card,hk]
      exact Nat.prime_three.coprime_iff_not_dvd.mp ((by decide : Nat.Coprime 3 2).pow_right k)
    rw [←(pResidual 2 (X ⧸ J)).card_mul_index] at hd
    exact (Nat.prime_three.dvd_mul.mp hd).elim hR3 hi3

/-- The genuine full E.2.2 list reduces to a normal Bender component,
without comparing generation parameters across a quotient. -/
theorem source_normal_bender_component
    (hX : IsSQTK KnownSimple.IsKnownSimple X)
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (hparam : 1 < generationParameter X) (h3 : primeRank 3 X ≤ 1)
    (hdiv : 3 ∣ Nat.card (X ⧸ pCore 2 X))
    (W : Subgroup X) [IsElementaryAbelian 2 W] (hWS : W ≤ S)
    (hout : ¬W ≤ minimalParabolicCore S hP)
    (hMW : minimalParabolicMax S hP ≤ normalizer (W : Set X))
    (hcard : Nat.card (W.map (QuotientGroup.mk' (pCore 2 X))) ≤ 4) :
    ∃ K : Subgroup X, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      K.Normal ∧ K ⊔ (S : Subgroup X) = ⊤ ∧
      ClassificationModels.IsBenderModel (K.map (QuotientGroup.mk' (minimalParabolicCore S hP))) := by
  have hs : ¬Group.IsSolvable X := by
    intro hh
    let := hh
    have hb := generationParameter_le_one_of_solvable (G := X)
    omega
  obtain ⟨K,hK,hqs,hgen,_⟩ := Structure.source_original_component hX S hP hs
  have hn : K.Normal := by
    by_contra hn
    rcases source_exchanged_marked_cases ChapterA.Section02.theoremA_knownSimple
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hX S hP hs K hK hgen hn with
      ⟨n,_,hm⟩ | ⟨p,hp,_,h7,hm⟩
    · exact not_exchanged_bender hX S hP hs K hK hqs hgen hn h3 hdiv hm
    · let : Fact p.Prime := ⟨hp⟩
      have hb := paired_prime_parameter_le_one ChapterA.Section02.theoremA_knownSimple
        hX S hP hs K hK hgen hn (by omega) hm
      omega
  let := hn
  exact ⟨K,hK,hqs,hn,hgen,normal_component_bender hX S hP hs K hK hgen
    hparam h3 W hWS hout hMW hcard⟩

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSieve

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSieve
open ChapterB ChapterE
variable {X : Type*} [Group X] [Finite X]
set_option backward.isDefEq.respectTransparency false

/-- The simple star marking is the central quotient of the full residual
in X/O₂(X); the full original maximal-core image is its center. -/
theorem residual_center_quotient_of_normal_component
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (hs : ¬Group.IsSolvable X)
    (K : Subgroup X) (hK : K.IsCComponent) [K.Normal]
    (hqs : IsQuasisimple (K ⧸ pCore 2 K)) (hgen : K ⊔ (S : Subgroup X) = ⊤) :
    let Q := pResidual 2 (X ⧸ pCore 2 X)
    IsQuasisimple Q ∧
      (minimalParabolicCore S hP).map (QuotientGroup.mk' (pCore 2 X)) =
        (center Q).map Q.subtype ∧
      Nonempty ((Q ⧸ center Q) ≃*
        K.map (QuotientGroup.mk' (minimalParabolicCore S hP))) := by
  let J := minimalParabolicCore S hP
  let q := QuotientGroup.mk' (pCore 2 X)
  let A := K.map q
  let B := K.map (QuotientGroup.mk' J)
  let R := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))
  let := hqs
  have hA : IsQuasisimple A := IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK)
  have hcomp : IsComponent (X ⧸ pCore 2 X) A :=
    ⟨hK.subnormal.map (QuotientGroup.mk'_surjective _),hA⟩
  have hgenA : A ⊔ (R : Subgroup (X ⧸ pCore 2 X)) = ⊤ := by
    change K.map q ⊔ (S : Subgroup X).map q = ⊤
    rw [←Subgroup.map_sup,hgen,map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  have hres : pResidual 2 (X ⧸ pCore 2 X) = A :=
    (Structure.residual_eq_layer R hcomp hgenA).trans
      (Structure.layer_eq_normal_component R hcomp hgenA)
  have hZ : J.map q = (center A).map A.subtype :=
    (Structure.source_original_normal_clauses S hP hs K hK hqs hgen).2
  let f : (X ⧸ pCore 2 X) →* (X ⧸ J) := QuotientGroup.map _ _ (MonoidHom.id X)
    (by simpa using minimalParabolicTwoCore_le_core S hP)
  have hfker : f.ker = J.map q := by simp only [f,QuotientGroup.ker_map,comap_id]; rfl
  have hAB : A.map f = B := by rw [map_map]; rfl
  let r : A →* B := (MulEquiv.subgroupCongr hAB).toMonoidHom.comp (f.subgroupMap A)
  have hr : Function.Surjective r := (MulEquiv.subgroupCongr hAB).surjective.comp
    (f.subgroupMap_surjective A)
  have hker : r.ker = center A := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulEquiv.subgroupCongr hAB).injective,
      ker_subgroupMap,hfker,hZ]
    exact comap_map_eq_self_of_injective A.subtype_injective (center A)
  have e : A ⧸ center A ≃* B :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective r hr)
  dsimp only
  rw [hres]
  exact ⟨hA,hZ,⟨e⟩⟩

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSieve
