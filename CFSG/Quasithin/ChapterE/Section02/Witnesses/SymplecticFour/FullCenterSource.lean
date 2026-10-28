module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SymplecticFour.FullCenter
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.QuotientLift.Source
public import CFSG.Quasithin.ChapterE.Section02.Structure.NormalSimpleImage
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.Alternating.FiveBorelCentralFactor
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# The original full-center symplectic witness and cubic bound

The original normal component and Sylow pass through the entire maximal
core J. If the image of V has at least the cardinality of the central root
plane, the actual marked Sp4 geometry makes it that plane and constructs
its opposite pair. The pair lifts through J with the same V, prescribed
Sylow and quotient-center marking, yielding the strict cubic bound.
No TI, pair-recognition or internal-conjugator premise is assumed. Smaller
images still require the independent E.2.7 subgroup recognition argument.

Source: Aschbacher–Smith E.2.7–9 and E.2.15, printed pp.219–222,228.
-/
public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
universe u
variable {H : Type u} [Group H] [Finite H]

theorem source_full_center_quotient
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) ≃*
      ClassicalGroup.PSp 2 F)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hcard : (2^n)^2 ≤ Nat.card (V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)))) :
    Nonempty (NativeWitness
      (T.mapSurjective (QuotientGroup.mk'_surjective (ChapterB.minimalParabolicCore T hP)))
      ((ChapterB.minimalParabolicMax T hP).map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)))
      (V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) F) := by
  let J := ChapterB.minimalParabolicCore T hP
  let M := ChapterB.minimalParabolicMax T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let W := V.map q
  let L := K.map q
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
  obtain ⟨hLs,hLa,hLn,hLT⟩ := Structure.source_normal_simple_image T hP hs K hK hgen
  let : IsSimpleGroup L := hLs
  let : L.Normal := hLn
  have hmin : ChapterB.IsMinimalParabolicOver S ⊤ := (Structure.source_star_minimal_core_free T hP).1
  have hcore : ChapterB.minimalParabolicCore S hmin=⊥ := (Structure.source_star_minimal_core_free T hP).2
  have hmax : ChapterB.minimalParabolicMax S hmin=M.map q :=
    (ChapterB.minimalParabolicMax_map_core T hP q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk'])).symm
  have hWS : W ≤ (S : Subgroup (H ⧸ J)) := map_mono hVT
  let : (W.subgroupOf (S : Subgroup (H ⧸ J))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hWS).mpr
      ((map_mono ((normal_subgroupOf_iff_le_normalizer hVT).mp hvn)).trans (le_normalizer_map q))
  have hWcore : W ≤ (ChapterB.minimalParabolicMax S hmin).pCoreIn 2 := by
    rw [hmax]
    exact (map_mono hVM).trans (Theory.SpecificGroups.Alternating.FiveBorelCentralFactor.core_image_le q M)
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (show (2:ℕ)^1 < 2^n from Nat.pow_lt_pow_right (by decide) hn)
  have hr : 1 < Group.rank W := by
    by_contra! h
    let : CommGroup W := IsMulCommutative.instCommGroup
    have hd := card_dvd_exponent_pow_rank' W
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 W))
    have hc : Nat.card W ≤ 2 := (Nat.le_of_dvd (by positivity) hd).trans
      (by simpa using (pow_le_pow_right' (by decide : 1 ≤ 2) h))
    have hh : (Nat.card F)^2 ≤ Nat.card W := by simpa only [hF] using hcard
    nlinarith
  let e' : L ≃* commutator (Sp F) :=
    (e.trans EvenProjective.equiv.symm).trans (derivedEquivFull_of_card_gt_two hq).symm
  obtain ⟨w,_⟩ := source_pair_of_full_card hF hn S hmin hcore L e' hLT W hWS hWcore hr
    (by simpa only [hF] using hcard)
  rw [hmax] at w
  exact ⟨w⟩

theorem source_full_center_cubicRatio_lt_two
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSp
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 (2^n))
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H)
    (hcard : (2^n)^2 ≤ Nat.card (V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)))) :
    cubicRatio (DihedralCubic.canonicalAction (normalizer (V : Set H)) V le_rfl) < 2 := by
  obtain ⟨F,hF,hfin,hFcard,⟨e⟩⟩ := hm
  let : CharP F 2 := EvenProjective.charTwo_of_card hFcard
  obtain ⟨w⟩ := source_full_center_quotient T hP hs K hK hgen hn hFcard e V hVT hvn hVM hcard
  exact QuotientLift.cubicRatio_lt_two_symplectic_of_quotient_pair hP hVT hvn hVM hout hfit
    w.pair n (by omega) hFcard w.quotientModel (unipotentSylow hFcard (by omega))
    (w.quotient_center hFcard (by omega))
end CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour
