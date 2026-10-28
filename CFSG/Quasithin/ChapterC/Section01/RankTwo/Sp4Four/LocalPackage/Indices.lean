module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.LocalPackage
public import Theory.Representation.NormalElementaryQuotient.FixedIndex
public import Theory.Representation.SymplecticFourOrthogonalCover.MovingIndex
public import Theory.GroupTheory.SmallMoverFamily

/-!
# Actual subgroup indices for the Sp4(4) small-mover family

Apply the universal central-cover index theorem to the literal quotient
conjugation action on an elementary subgroup V. Its centralizer index is
the natural moving index of the image under the original quotient map.
Kernel saturation then identifies the maximum-order family with exactly
the maximum-order admissible images in the arbitrary radical image.

Source: MS93 (1.5)(ii) and (5.0), printed pp.843 and 912. The cover projection
is an explicit earlier-source input, supplied by natural moved-section
recognition and its fully moved central-extension construction; this module
does not assume the source (5.1) or any local generator conclusion.
-/

public section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.LocalPackage
open Representation.SymplecticFourOrthogonalCover
variable {K G : Type*} [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) K] [Group G]
variable (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V] [Finite V]
variable (q : G →* L (K := K)) (hq : Function.Surjective q)
  (hker : q.ker = centralizer (V : Set G))
variable (p : (NormalElementaryQuotient.representation V q hq hker).IntertwiningMap
  (binaryNatural (K := K))) (hp : IsCover p)
include hp
theorem centralizer_index_eq_natural (E : Subgroup G) :
    (centralizer (E : Set G)).relIndex V =
      2 ^ fixedCodim (binaryNatural (K := K)) (E.map q) := by
  rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim V q hq hker,
    fixedCodim_of_binaryCover p hp]

theorem smallMover_iff_natural (T E : Subgroup G) (n : ℕ) :
    Subgroup.SmallMover.Admissible V q.ker T n E ↔ E ≤ T ∧
      2 ^ fixedCodim (binaryNatural (K := K)) (E.map q) ≤ Nat.card (E.map q) ∧
      2 ^ fixedCodim (binaryNatural (K := K)) (E.map q) ≤ n := by
  unfold Subgroup.SmallMover.Admissible
  rw [centralizer_index_eq_natural V q hq hker p hp,relIndex_ker]

theorem maximalMover_iff_natural [Finite G] (T E : Subgroup G) (n : ℕ)
    (hkT : q.ker ≤ T) :
    E ∈ Subgroup.SmallMover.Maximal V q.ker T n ↔
      q.ker ≤ E ∧ E ≤ T ∧
      2 ^ fixedCodim (binaryNatural (K := K)) (E.map q) ≤ Nat.card (E.map q) ∧
      2 ^ fixedCodim (binaryNatural (K := K)) (E.map q) ≤ n ∧
      ∀ A : Subgroup (L (K := K)), A ≤ T.map q →
        2 ^ fixedCodim (binaryNatural (K := K)) A ≤ Nat.card A →
        2 ^ fixedCodim (binaryNatural (K := K)) A ≤ n → Nat.card A ≤ Nat.card (E.map q) := by
  have hc : V ≤ centralizer (q.ker : Set G) := by
    rw [hker]
    exact le_centralizer_iff.mpr le_rfl
  rw [Subgroup.SmallMover.maximal_iff_image_maximal q V T n hkT hc E,
    smallMover_iff_natural V q hq hker p hp]
  constructor
  · rintro ⟨⟨hET,hmove,hbound⟩,hkerE,hmax⟩
    refine ⟨hkerE,hET,hmove,hbound,?_⟩
    intro A hAT hAm hAb
    have hpre : A.comap q ≤ T := by
      exact (comap_mono hAT).trans_eq (comap_map_eq_self hkT)
    have him : (A.comap q).map q = A := map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr hq]; exact le_top)
    have h := hmax (A.comap q) ((smallMover_iff_natural V q hq hker p hp T _ n).mpr
      ⟨hpre,by simpa only [him] using hAm,by simpa only [him] using hAb⟩)
    simpa only [him] using h
  · rintro ⟨hkerE,hET,hmove,hbound,hmax⟩
    refine ⟨⟨hET,hmove,hbound⟩,hkerE,?_⟩
    intro F hF
    obtain ⟨hFT,hFm,hFb⟩ := (smallMover_iff_natural V q hq hker p hp T F n).mp hF
    exact hmax (F.map q) (map_mono hFT) hFm hFb
/-- A nontrivial actual quotient image moves the original module with index at least four. -/
theorem centralizer_index_ge_four (hK : Nat.card K = 4)
    (E : Subgroup G) (hne : E.map q ≠ ⊥) :
    4 ≤ (centralizer (E : Set G)).relIndex V := by
  rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim V q hq hker]
  exact cover_moving_index_ge_four hK p hp (E.map q) hne

/-- The exceptional source index-two seed cannot occur over a field of order four. -/
theorem centralizer_index_ne_two (hK : Nat.card K = 4) (E : Subgroup G) :
    (centralizer (E : Set G)).relIndex V ≠ 2 := by
  intro he
  by_cases hz : E.map q = ⊥
  · rw [centralizer_index_eq_natural V q hq hker p hp,hz] at he
    have hzero := (fixedCodim_eq_zero_iff (binaryNatural (K := K)) ⊥).mpr
      (fixedSpace_bot (binaryNatural (K := K)))
    rw [hzero] at he
    norm_num at he
  · have h := centralizer_index_ge_four V q hq hker p hp hK E hz
    omega

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.LocalPackage
