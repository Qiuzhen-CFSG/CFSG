module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.MarkedLift
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.UnitaryThree
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.Involution.Source
public import Theory.GroupTheory.PrimeRankElementary
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Full original E.2.9 for the normal Bender source family

The original elementary V outside J has nontrivial image in H/J. An image
of order two uses the genuine involution/dihedral construction. Every larger
elementary image has rank greater than one; the actual normal Bender model
places it in the model Sylow center and constructs its marked pair. The
proved source lift returns a pair on the original V,H,T and maximal subgroup,
retaining its actual quotient model, exact Borel image and degree divisor.

No rank, placement or pair conclusion remains a premise. The independent
E.2.2 model selection remains with the source classification assembly.
Source: Aschbacher–Smith E.2.7–9, printed pp.218–222.
-/

public section
noncomputable section
open Subgroup Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
variable {H : Type*} [Group H] [Finite H]

/-- Construct the genuine model witness in a core-free normal Bender extension. -/
theorem coreFree_source_at (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (K : Subgroup H) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hcore : pCore 2 H = ⊥)
    {n : ℕ} (hm : ModelAt K n)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hrank : 1 < primeRank 2 V) :
    Nonempty (OriginalWitness T (ChapterB.minimalParabolicMax T hP) V n) := by
  cases hm with
  | linear hn hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    let es := e.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm
    obtain ⟨_,_,⟨w⟩⟩ := source_linear T hP K hgen hcore hn hF es V hVT hVcore hrank
    exact ⟨OriginalWitness.of_linear w⟩
  | unitary hn hm =>
    obtain ⟨_,_,⟨w⟩⟩ := source_unitary_of_isPSU T hP K hgen hcore hn hm V hVT hvn hrank
    exact ⟨OriginalWitness.of_linear w⟩
  | suzuki hm he =>
    obtain ⟨e⟩ := he
    obtain ⟨_,⟨w⟩⟩ := source_suzuki T hP K hgen hcore hm e V hVT hrank
    exact ⟨OriginalWitness.of_suzuki w⟩

omit [Finite H] in
private theorem map_core_le {A : Type*} [Group A] (f : H →* A) (M : Subgroup H) :
    (M.pCoreIn 2).map f ≤ (M.map f).pCoreIn 2 := by
  have hc : (pCore 2 M).map (f.subgroupMap M) ≤ pCore 2 (M.map f) :=
    le_sSup ⟨Normal.map inferInstance _ (f.subgroupMap_surjective M),pCore_isPGroup.map _⟩
  calc
    _ = ((pCore 2 M).map (f.subgroupMap M)).map (M.map f).subtype := by
      rw [pCoreIn,Subgroup.map_map,Subgroup.map_map]
      rfl
    _ ≤ _ := map_mono hc

/-- Full original normal-Bender E.2.9 at a marked source field exponent.
The order-two image and higher-rank image are both constructed internally. -/
theorem source_at (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (V : Subgroup H)
    [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (D : Subgroup (H ⧸ ChapterB.minimalParabolicCore T hP)) [D.Normal]
    (hgen : D ⊔ ((T : Subgroup H).map
      (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) = ⊤)
    {n : ℕ} (hm : ModelAt D n) :
    Nonempty (OriginalWitness T (ChapterB.minimalParabolicMax T hP) V n) := by
  classical
  let M := ChapterB.minimalParabolicMax T hP
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let B := M.map q
  let W := V.map q
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
  by_cases hcard : Nat.card W = 2
  · obtain ⟨w⟩ := Involution.source_star_order_two T hP V hVT hvn hVcore hcard
    exact ⟨OriginalWitness.of_dihedral w⟩
  have hne : W ≠ ⊥ := by
    intro hh
    have hle := (map_eq_bot_iff V).mp hh
    exact hout (by simpa only [q,QuotientGroup.ker_mk'] using hle)
  have hWr : 1 < primeRank 2 W := by
    by_contra h
    have htE : IsElementaryAbelian 2 (⊤ : Subgroup W) := {
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
        apply Subtype.ext
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 W) x.val) }
    have ht := (primeRank_le_iff_elementary_card_le W).mp (Nat.le_of_not_gt h)
      (⊤ : Subgroup W) htE
    rw [card_top,pow_one] at ht
    have hgt := (one_lt_card_iff_ne_bot W).mpr hne
    omega
  have hk : q.ker ≤ J := by rw [QuotientGroup.ker_mk']
  let hPs := ChapterB.minimalParabolic_surjective_core T hP q (QuotientGroup.mk'_surjective J) hk
  have hJs : ChapterB.minimalParabolicCore S hPs = ⊥ := by
    rw [←ChapterB.minimalParabolicCore_map_core T hP q (QuotientGroup.mk'_surjective J) hk]
    exact QuotientGroup.map_mk'_self J
  have hQs : pCore 2 (H ⧸ J) = ⊥ :=
    bot_unique (hJs ▸ ChapterB.minimalParabolicTwoCore_le_core S hPs)
  have hB : ChapterB.minimalParabolicMax S hPs = B :=
    (ChapterB.minimalParabolicMax_map_core T hP q (QuotientGroup.mk'_surjective J) hk).symm
  have hWS : W ≤ (S : Subgroup (H ⧸ J)) := map_mono hVT
  have hWn : (W.subgroupOf (S : Subgroup (H ⧸ J))).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer hWS).mpr
    have ht := (normal_subgroupOf_iff_le_normalizer hVT).mp hvn
    exact (map_mono ht).trans (le_normalizer_map (H := V) q)
  have hWcore : W ≤ (ChapterB.minimalParabolicMax S hPs).pCoreIn 2 := by
    rw [hB]
    exact (map_mono hVcore).trans (map_core_le q M)
  obtain ⟨w⟩ := coreFree_source_at S hPs D hgen hQs hm W hWS hWn hWcore hWr
  rw [hB] at w
  exact lift_original_witness T hP V hVT hvn hVcore w

/-- Full original normal-Bender source construction from the actual model list.
The chosen ambient exponent and its witness divisor are retained together. -/
theorem source (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (V : Subgroup H)
    [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (D : Subgroup (H ⧸ ChapterB.minimalParabolicCore T hP)) [D.Normal]
    (hgen : D ⊔ ((T : Subgroup H).map
      (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) = ⊤)
    (hm : ClassificationModels.IsBenderModel D) :
    ∃ n : ℕ, ModelAt D n ∧
      Nonempty (OriginalWitness T (ChapterB.minimalParabolicMax T hP) V n) := by
  cases hm with
  | linear n hn e =>
    have hmodel := ModelAt.linear hn e
    exact ⟨n,hmodel,source_at T hP V hVT hvn hVcore hout D hgen hmodel⟩
  | unitary n hn e =>
    have hmodel := ModelAt.unitary hn e
    exact ⟨n,hmodel,source_at T hP V hVT hvn hVcore hout D hgen hmodel⟩
  | suzuki m hm e =>
    have hmodel := ModelAt.suzuki (by omega : 0<m) e
    exact ⟨2*m+1,hmodel,source_at T hP V hVT hvn hVcore hout D hgen hmodel⟩


/-- Apply the full source witness directly to an original normal supplement;
its star image and generating identity are constructed with the literal map. -/
theorem source_of_normal_supplement (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (V : Subgroup H)
    [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (K : Subgroup H) [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hm : ClassificationModels.IsBenderModel
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)))) :
    ∃ n : ℕ, ModelAt (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) n ∧
      Nonempty (OriginalWitness T (ChapterB.minimalParabolicMax T hP) V n) := by
  let q := QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)
  have hg : K.map q ⊔ (T : Subgroup H).map q = ⊤ := by
    rw [←Subgroup.map_sup,hgen,map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  exact source T hP V hVT hvn hVcore hout (K.map q) hg hm

end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
