module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.DegreeLift
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.Source
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.LinearThree.Source
public import CFSG.Quasithin.ChapterE.Section02.Structure.NormalSimpleImage
public import Theory.SpecificGroups.Alternating.FiveBorelCentralFactor
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Higher-degree witnesses from a noncyclic original star image

In a normal Bender or binary linear-three source family, a noncyclic image
of the original elementary subgroup constructs a pair of degree greater
than one. The actual maximal-core lift preserves this strict bound and
all original subgroup and quotient markings.

Source: Aschbacher--Smith E.2.7--9, printed pp.218--222.
-/

public noncomputable section
open Subgroup Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

theorem coreFree_source_at_large_degree (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (K : Subgroup H) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hcore : pCore 2 H = ⊥)
    {n : ℕ} (hm : ModelAt K n)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hrank : 1 < primeRank 2 V) :
    ∃ w : OriginalWitness T (ChapterB.minimalParabolicMax T hP) V n, 1 < w.degree := by
  cases hm with
  | linear hn hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    let es := e.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm
    obtain ⟨_,_,⟨w⟩⟩ := source_linear T hP K hgen hcore hn hF es V hVT hVcore hrank
    exact ⟨OriginalWitness.of_linear w, (OriginalWitness.of_linear_degree w).symm ▸ w.degree_gt_one⟩
  | unitary hn hm =>
    obtain ⟨_,_,⟨w⟩⟩ := source_unitary_of_isPSU T hP K hgen hcore hn hm V hVT hvn hrank
    exact ⟨OriginalWitness.of_linear w, (OriginalWitness.of_linear_degree w).symm ▸ w.degree_gt_one⟩
  | suzuki hm he =>
    obtain ⟨e⟩ := he
    obtain ⟨_,⟨w⟩⟩ := source_suzuki T hP K hgen hcore hm e V hVT hrank
    refine ⟨OriginalWitness.of_suzuki w, ?_⟩
    rw [OriginalWitness.of_suzuki_degree]
    have := w.positive
    omega



open ChapterB

/-- The original Sylow subgroup meets the maximal core in exactly O₂(H),
so its subgroups have equal image orders in the two literal quotients. -/
theorem twoCore_image_card_eq_star (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) (V : Subgroup H) (hVT : V ≤ T) :
    Nat.card (V.map (QuotientGroup.mk' (pCore 2 H))) =
      Nat.card (V.map (QuotientGroup.mk' (minimalParabolicCore T hP))) := by
  rw [←relIndex_ker,←relIndex_ker,QuotientGroup.ker_mk',QuotientGroup.ker_mk']
  rw [←inf_relIndex_left (H := V) (K := pCore 2 H),
    ←inf_relIndex_left (H := V) (K := minimalParabolicCore T hP)]
  congr 1
  apply le_antisymm
  · exact inf_le_inf_left V (minimalParabolicTwoCore_le_core T hP)
  · exact le_inf inf_le_left ((le_inf (inf_le_left.trans hVT) inf_le_right).trans
      (minimalParabolic_sylow_inf_core T hP).le)

/-- A noncyclic image on a normal Bender source yields a strict-degree
witness on the full original V. -/
theorem source_at_large_degree (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) (V : Subgroup H)
    [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVM : V ≤ (minimalParabolicMax T hP).pCoreIn 2)
    (D : Subgroup (H ⧸ minimalParabolicCore T hP)) [D.Normal]
    (hgen : D ⊔ ((T : Subgroup H).map
      (QuotientGroup.mk' (minimalParabolicCore T hP))) = ⊤)
    {n : ℕ} (hm : ModelAt D n)
    (hcard : 4 ≤ Nat.card (V.map (QuotientGroup.mk' (minimalParabolicCore T hP)))) :
    ∃ w : OriginalWitness T (minimalParabolicMax T hP) V n, 1 < w.degree := by
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
  have hSW : (S : Subgroup (H ⧸ J)) ≤ normalizer (W : Set (H ⧸ J)) :=
    (map_mono ((normal_subgroupOf_iff_le_normalizer hVT).mp hvn)).trans (le_normalizer_map q)
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
  have hex := coreFree_source_at_large_degree S hmin D hgen hO hm W hWS hWn hWcore hWr
  rw [hmax] at hex
  obtain ⟨w,hw⟩ := hex
  obtain ⟨w',he⟩ := lift_original_witness_degree T hP V hVT hvn hVM w
  exact ⟨w',he.symm ▸ hw⟩

/-- The genuine long-root construction also preserves strict degree through
the maximal core of an original binary PSL₃ source. -/
theorem linear_three_source_large_degree (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) (V : Subgroup H)
    [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVM : V ≤ (minimalParabolicMax T hP).pCoreIn 2)
    (D : Subgroup (H ⧸ minimalParabolicCore T hP)) [D.Normal] [IsSimpleGroup D]
    (hgen : D ⊔ ((T : Subgroup H).map
      (QuotientGroup.mk' (minimalParabolicCore T hP))) = ⊤)
    {n : ℕ} (hn : 0 < n) (hm : ClassicalGroup.IsPSL D 3 (2^n))
    (hcard : 4 ≤ Nat.card (V.map (QuotientGroup.mk' (minimalParabolicCore T hP)))) :
    ∃ w : OriginalWitness T (minimalParabolicMax T hP) V n, 1 < w.degree := by
  let J := minimalParabolicCore T hP
  let M := minimalParabolicMax T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let W := V.map q
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
  have hmin : IsMinimalParabolicOver S ⊤ := (Structure.source_star_minimal_core_free T hP).1
  have hcore : minimalParabolicCore S hmin = ⊥ := (Structure.source_star_minimal_core_free T hP).2
  have hmax : minimalParabolicMax S hmin = M.map q :=
    (minimalParabolicMax_map_core T hP q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk'])).symm
  have hWS : W ≤ (S : Subgroup (H ⧸ J)) := map_mono hVT
  have hSW : (S : Subgroup (H ⧸ J)) ≤ normalizer (W : Set (H ⧸ J)) :=
    (map_mono ((normal_subgroupOf_iff_le_normalizer hVT).mp hvn)).trans (le_normalizer_map q)
  obtain ⟨F,hF,hfin,hsize,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hsize)
  obtain ⟨w⟩ := LinearThree.exists_witness F hn hsize D e S hgen hmin hcore W hWS hSW hcard
  have hex : ∃ wo : OriginalWitness S (minimalParabolicMax S hmin) W n, 1 < wo.degree := by
    refine ⟨OriginalWitness.of_linear w, ?_⟩
    rw [OriginalWitness.of_linear_degree]
    exact w.degree_gt_one
  rw [hmax] at hex
  obtain ⟨wo,hw⟩ := hex
  obtain ⟨w',he⟩ := lift_original_witness_degree T hP V hVT hvn hVM wo
  exact ⟨w',he.symm ▸ hw⟩

end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
