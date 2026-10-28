module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.HigherDegree
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.Source
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.LinearThree.Source
public import CFSG.Quasithin.ChapterE.Section02.Structure.NormalSimpleImage
public import Theory.SpecificGroups.Alternating.FiveBorelCentralFactor
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.OddLinearTwo.Original
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.OddDegreeThree.Original
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source
public import CFSG.Quasithin.ChapterE.Section02.Structure.Original
public import CFSG.Quasithin.ChapterE.Section02.Structure.ComponentModels.OriginalImage
public import Theory.SpecificGroups.Classical.PairedOddRank
public import CFSG.Quasithin.ChapterE.Section02.Structure.PairedComponents
public import Theory.SpecificGroups.PSL2.PrimeCubicRank
public import Theory.SpecificGroups.PrimeToFifteen.Suzuki
public import Theory.SpecificGroups.Suzuki.LinearSeparation
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Theory.GroupTheory.OddPrimeRankOneSylow
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Noncyclic elementary images in the actual E.2.2 model cases

The normal odd-characteristic rows bound the original star image by two.
Normal Bender and binary linear-three rows construct a marked pair of
strict degree. Symplectic rows contradict cubic rank one. Exchanged linear
components have cubic rank two, and exchanged Suzuki components have
five-rank two, so neither occurs under the two original odd-rank bounds.

This isolates the model analysis from the full source catalogue. The
HigherDegreeSource consumer supplies precisely that catalogue on the
original C-component and discharges the retained model-case input.
Every constructed witness lifts to the original elementary subgroup.

Source: Aschbacher--Smith E.2.2 and E.2.7--9, printed pp.215--222;
application to 8.2.9, printed p.720, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

open ChapterB Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open Theory.GroupTheory

private theorem quotient_rank_le_one {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hr : primeRank p H ≤ 1) (J : Subgroup H) [J.Normal] :
    primeRank p (H ⧸ J) ≤ 1 := by
  let P : Sylow p H := Classical.choice inferInstance
  exact P.primeRank_quotient_le_one (P.isCyclic_of_odd_of_primeRank_le_one ho hr) J

private theorem exchanged_rank_contradiction
    (hA : ChapterA.Section02.TheoremA κ H)
    (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤) (hs : ¬Group.IsSolvable H)
    (K : Subgroup H) (hK : K.IsCComponent) (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hn : ¬K.Normal) {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hr : primeRank p H ≤ 1)
    (hpos : 1 ≤ primeRank p (K.map (QuotientGroup.mk' (minimalParabolicCore T hP)))) :
    False := by
  let J := minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let R := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let B := K.map q
  let : Group.IsSolvable J := minimalParabolic_core_solvable T hP
  have hi := Structure.source_component_simple_image T hP hs K hK hgen
  have hB : B.IsCComponent := hK.map_quotient J
  have hnot : ¬B.Normal := fun hh => hn (cComponent_normal_of_quotient_normal hK J hh)
  obtain ⟨t,_,_,_,_,⟨e,_⟩,_,_⟩ := Structure.source_pair_coordinates
    (Structure.source_star_sqtk hA hH T hP hs).stronglyQuasithin
    R (Structure.source_star_minimal_core_free T hP).1
    (fun hh => hs ((Group.isSolvable_iff_subgroup_quotient J).mpr ⟨inferInstance,hh⟩))
    (Structure.source_star_minimal_core_free T hP).2 hi.2.1 hB hi.2.2.2 hnot
  let D := B.map (MulAut.conj (t : H ⧸ J)).toMonoidHom
  change 1 ≤ primeRank p B at hpos
  have he : primeRank p B = primeRank p D :=
    primeRank_equiv p ((MulAut.conj (t : H ⧸ J)).subgroupMap B)
  have hlow : 2 ≤ primeRank p (B ⊔ D : Subgroup (H ⧸ J)) := by
    rw [←primeRank_equiv p e,primeRank_prod_eq_add]
    change 2 ≤ primeRank p B + primeRank p D
    omega
  have hu := (primeRank_subgroup_le p (B ⊔ D)).trans (quotient_rank_le_one ho hr J)
  omega

/-- Every noncyclic star image in this low-odd-rank source configuration
constructs an original marked pair whose degree is greater than one. -/
theorem source_large_image_degree_of_models
    (hA : ChapterA.Section02.TheoremA κ H)
    (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤) (hs : ¬Group.IsSolvable H)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVM : V ≤ (minimalParabolicMax T hP).pCoreIn 2)
    (hMV : minimalParabolicMax T hP ≤ normalizer (V : Set H))
    (hcard : 4 ≤ Nat.card (V.map (QuotientGroup.mk' (minimalParabolicCore T hP))))
    (h3 : primeRank 3 H ≤ 1) (h5 : primeRank 5 H ≤ 1)
    (K : Subgroup H) (hK : K.IsCComponent) (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hmodels : let M := minimalParabolicMax T hP
      let D := sourceImage M K
      (K.Normal ∧
        (SingleOddLinearModel M K (T : Subgroup H) ∨
         SingleOddRankThreeModel M K (T : Subgroup H) ∨
         ClassificationModels.IsBenderModel D ∨
         (∃ n : ℕ, 1 ≤ n ∧ ClassicalGroup.IsPSL D 3 (2^n)) ∨
         (∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSp D 2 (2^n)) ∨
         Nonempty (D ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))))) ∨
      (¬K.Normal ∧ ((∃ n : ℕ, 1 < n ∧ ExchangedModel M K n) ∨
        ∃ p : ℕ, p.Prime ∧ Odd p ∧ 7 ≤ p ∧ ClassicalGroup.IsPSL D 2 p))) :
    ∃ (n : ℕ) (w : OriginalWitness T (minimalParabolicMax T hP) V n), 1 < w.degree := by
  let J := minimalParabolicCore T hP
  let M := minimalParabolicMax T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let W := V.map q
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
  have hmin : IsMinimalParabolicOver S ⊤ := (Structure.source_star_minimal_core_free T hP).1
  have hcore : minimalParabolicCore S hmin = ⊥ := (Structure.source_star_minimal_core_free T hP).2
  have hO : pCore 2 (H ⧸ J) = ⊥ :=
    bot_unique ((minimalParabolicTwoCore_le_core S hmin).trans hcore.le)
  have hmax : minimalParabolicMax S hmin = M.map q :=
    (minimalParabolicMax_map_core T hP q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk'])).symm
  have hWS : W ≤ (S : Subgroup (H ⧸ J)) := map_mono hVT
  have hNW : minimalParabolicMax S hmin ≤ normalizer (W : Set (H ⧸ J)) := by
    rw [hmax]
    exact (map_mono hMV).trans (le_normalizer_map q)
  have hSW : (S : Subgroup (H ⧸ J)) ≤ normalizer (W : Set (H ⧸ J)) :=
    (minimalParabolicMax_spec S hmin).2.trans hNW
  have hWn : (W.subgroupOf (S : Subgroup (H ⧸ J))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hWS).mpr hSW
  have hWcore : W ≤ (minimalParabolicMax S hmin).pCoreIn 2 := by
    rw [hmax]
    exact (map_mono hVM).trans
      (Theory.SpecificGroups.Alternating.FiveBorelCentralFactor.core_image_le q M)
  change 4 ≤ Nat.card W at hcard
  have hWr : 1 < primeRank 2 W := by
    by_contra hr
    have htE : IsElementaryAbelian 2 (⊤ : Subgroup W) := {
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
        apply Subtype.ext
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 W) x.val) }
    have hc := (primeRank_le_iff_elementary_card_le W).mp (Nat.le_of_not_gt hr)
      (⊤ : Subgroup W) htE
    rw [card_top,pow_one] at hc
    omega
  have hlift {n : ℕ} (w : OriginalWitness S (minimalParabolicMax S hmin) W n)
      (hw : 1 < w.degree) :
      ∃ (n : ℕ) (w : OriginalWitness T (minimalParabolicMax T hP) V n), 1 < w.degree := by
    have hex : ∃ w : OriginalWitness S (minimalParabolicMax S hmin) W n,
        1 < w.degree := ⟨w,hw⟩
    rw [hmax] at hex
    obtain ⟨w,hw⟩ := hex
    obtain ⟨w',he⟩ := lift_original_witness_degree T hP V hVT hvn hVM w
    exact ⟨n,w',he.symm ▸ hw⟩
  rcases hmodels with ⟨hnorm,hmodels⟩ | ⟨hnorm,hmodels⟩
  · let := hnorm
    let D := K.map q
    have hi := Structure.source_normal_simple_image T hP hs K hK hgen
    let : D.Normal := hi.2.2.1
    let : IsSimpleGroup D := hi.1
    rcases hmodels with h2 | hthree | hb | hl | hsp | hbi
    · obtain ⟨p,d,hp,hp3,hd,hd2,hmod,F,hF,hfin,hsize,e,_⟩ := h2
      let : Fact p.Prime := ⟨hp⟩
      have ho : Odd p := hp.odd_of_ne_two (by omega)
      have hlarge : 5 < p^d := by
        rcases (show d=1 ∨ d=2 by omega) with hd | hd
        · subst d; simp only [pow_one] at hmod ⊢; omega
        · subst d; nlinarith
      have hnine : p^d ≠ 9 := by
        intro he
        rcases (show d=1 ∨ d=2 by omega) with hd | hd
        · subst d; simp only [pow_one] at he; rw [he] at hp; norm_num at hp
        · subst d; nlinarith
      have hc : Nat.card W ≤ 2 := Structure.odd_linear_source_elementary_card_le_two
        (Structure.source_star_sqtk hA hH T hP hs)
        S hmin hcore D hi.2.2.2 hO ho hsize (by simpa only [hsize] using hlarge)
        (by simpa only [hsize] using hnine) e W inferInstance hWcore hWS hSW
      omega
    · obtain ⟨p,hp,ho,_,hu | hl⟩ := hthree
      · have hc := Structure.OddDegreeThree.unitary_elementary_card_le_two
          S hmin D hi.2.2.2 hO hp ho hu.2 W hWcore
        omega
      · obtain ⟨_,F,hF,hfin,hsize,e,_⟩ := hl
        have hc := Structure.OddDegreeThree.linear_normal_elementary_card_le_two
          S hmin D hi.2.2.2 hO hp ho ⟨F,hF,hfin,hsize,⟨e⟩⟩ W
          (hWS.trans (minimalParabolicMax_spec S hmin).2) hNW
        omega
    · have hm : ∃ n, ModelAt D n := by
        cases hb with
        | linear n hn hm => exact ⟨n,.linear hn hm⟩
        | unitary n hn hm => exact ⟨n,.unitary hn hm⟩
        | suzuki m hm he => exact ⟨2*m+1,.suzuki (by omega) he⟩
      obtain ⟨n,hm⟩ := hm
      obtain ⟨w,hw⟩ := coreFree_source_at_large_degree S hmin D hi.2.2.2 hO hm
        W hWS hWn hWcore hWr
      exact hlift w hw
    · obtain ⟨n,hn,F,hF,hfin,hsize,⟨e⟩⟩ := hl
      let : Fintype F := Fintype.ofFinite F
      let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
        (by simpa only [Nat.card_eq_fintype_card] using hsize)
      obtain ⟨w⟩ := LinearThree.exists_witness F (by omega) hsize D e S hi.2.2.2
        hmin hcore W hWS hSW hcard
      apply hlift (OriginalWitness.of_linear w)
      rw [OriginalWitness.of_linear_degree]
      exact w.degree_gt_one
    · obtain ⟨n,hn,F,hF,hfin,hsize,⟨e⟩⟩ := hsp
      have hr := Theory.SpecificGroups.Classical.PairedOddRank.psp_binary_three_rank hsize
      rw [←primeRank_equiv 3 e] at hr
      change 2 ≤ primeRank 3 D at hr
      have hu := (primeRank_subgroup_le 3 D).trans
        (quotient_rank_le_one (by decide) h3 J)
      omega
    · obtain ⟨e⟩ := hbi
      have hr := Theory.SpecificGroups.Classical.PairedOddRank.derived_psp_binary_three_rank
      rw [←primeRank_equiv 3 e] at hr
      change 2 ≤ primeRank 3 D at hr
      have hu := (primeRank_subgroup_le 3 D).trans
        (quotient_rank_le_one (by decide) h3 J)
      omega
  · rcases hmodels with ⟨n,hn,hm⟩ | ⟨p,hp,ho,_,F,hF,hfin,hsize,⟨e⟩⟩
    · rcases hm with ⟨F,hF,hfin,hchar,hn,hsize,e,_⟩ | ⟨m,hm,_,e,_⟩
      · have hdiv : 3 ∣ Nat.card (K.map q) := by
          change 3 ∣ Nat.card (sourceImage (minimalParabolicMax T hP) K)
          rw [Nat.card_congr e.toEquiv]
          exact three_dvd_card_psl2_char_two F
        have hpos : 1 ≤ primeRank 3 (K.map q) := by
          apply Nat.one_le_iff_ne_zero.mpr
          exact fun hz => PrimeRank.eq_zero_iff_not_dvd_card.mp hz hdiv
        exact (exchanged_rank_contradiction hA hH T hP hs K hK hgen hnorm
          (by decide) h3 hpos).elim
      · have hdiv : 5 ∣ Nat.card (K.map q) := by
          change 5 ∣ Nat.card (sourceImage (minimalParabolicMax T hP) K)
          rw [Nat.card_congr e.toEquiv]
          exact suzukiMatrixGroup_five_dvd m (by omega)
        let : Fact (Nat.Prime 5) := ⟨by decide⟩
        have hpos : 1 ≤ primeRank 5 (K.map q) := by
          apply Nat.one_le_iff_ne_zero.mpr
          exact fun hz => PrimeRank.eq_zero_iff_not_dvd_card.mp hz hdiv
        exact (exchanged_rank_contradiction hA hH T hP hs K hK hgen hnorm
          (by decide) h5 hpos).elim
    · exact (exchanged_rank_contradiction hA hH T hP hs K hK hgen hnorm (by decide) h3
        (Theory.PSL2.prime_model_three_rank_pos hp ho hsize e)).elim

end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
