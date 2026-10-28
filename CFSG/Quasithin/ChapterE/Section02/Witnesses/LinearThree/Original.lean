module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.LinearThree.Source
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.MarkedLift
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.Involution.Source
public import CFSG.Quasithin.ChapterE.Section02.Structure.NormalSimpleImage
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# The original binary PSL3 source witness through the full core

The actual component and Sylow images give the core-free linear-three
configuration. A star image of order two has a dihedral pair; every larger
image lies in the genuine long root and supplies its marked SL2 pair.
The full-core lift restores the original V and internal conjugator while
preserving the precise Sylow, Borel, quotient model and field divisor.
Source: Aschbacher–Smith E.2.7–9, printed pp.219–222.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Witnesses.LinearThree
open BenderPlacement
universe u
variable {H : Type u} [Group H] [Finite H]
theorem source_original
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 (2^n))
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬V ≤ ChapterB.minimalParabolicCore T hP) :
    Nonempty (OriginalWitness T (ChapterB.minimalParabolicMax T hP) V n) := by
  let J := ChapterB.minimalParabolicCore T hP
  let M := ChapterB.minimalParabolicMax T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let W := V.map q
  let D := K.map q
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
  have hi := Structure.source_normal_simple_image T hP hs K hK hgen
  have hmin : ChapterB.IsMinimalParabolicOver S ⊤ := (Structure.source_star_minimal_core_free T hP).1
  have hcore : ChapterB.minimalParabolicCore S hmin=⊥ := (Structure.source_star_minimal_core_free T hP).2
  have hmax : ChapterB.minimalParabolicMax S hmin=M.map q :=
    (ChapterB.minimalParabolicMax_map_core T hP q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk'])).symm
  have hWS : W ≤ (S : Subgroup (H ⧸ J)) := map_mono hVT
  have hSW : (S : Subgroup (H ⧸ J)) ≤ normalizer (W : Set (H ⧸ J)) :=
    (map_mono ((normal_subgroupOf_iff_le_normalizer hVT).mp hvn)).trans (le_normalizer_map q)
  have hne : W ≠ ⊥ := by
    intro hh
    have hle := (map_eq_bot_iff V).mp hh
    exact hout (by simpa only [q,QuotientGroup.ker_mk'] using hle)
  by_cases hc : 4 ≤ Nat.card W
  · obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    let : D.Normal := hi.2.2.1
    let : IsSimpleGroup D := hi.1
    obtain ⟨w⟩ := exists_witness F hn hcard D e S hi.2.2.2 hmin hcore W hWS hSW hc
    have wo := OriginalWitness.of_linear w
    rw [hmax] at wo
    exact lift_original_witness T hP V hVT hvn hVM wo
  · have htwo : Nat.card W=2 := by
      have hpos := (one_lt_card_iff_ne_bot W).mpr hne
      obtain ⟨r,hr⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_card_eq
      have hlt : r < 2 := by
        by_contra! h
        have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) h
        norm_num at hh
        omega
      interval_cases r
      · have hh : Nat.card W = 1 := by simpa using hr
        omega
      · simpa using hr
    obtain ⟨w⟩ := Involution.source_star_order_two T hP V hVT hvn hVM htwo
    exact ⟨OriginalWitness.of_dihedral w⟩
end CFSG.Quasithin.ChapterE.Witnesses.LinearThree
