module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SymplecticFour.FullCenterSource
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.WeakAction

/-!
# The endpoint image sizes in the nonbinary symplectic source bound

An image of order two supplies a dihedral pair, while the full central root
plane supplies a symplectic pair. Both pairs act on the original V, and their
cubic actors lie in the original Sylow, hence in every prescribed normalizing
overgroup U. No TI or maximal-subgroup normalization is used.

The final source reduction leaves precisely the strict interval between these
endpoint sizes. Recognition of those smaller central-plane pairs is the separate
E.2.7 obligation; this module does not assert the full E.2.13 symplectic row.

Source: Aschbacher--Smith E.2.7--9 and E.2.13, printed pp.219--225.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
open ChapterB
variable {H : Type*} [Group H] [Finite H]

/-- Full-center source bound for the literal action of the prescribed U. -/
theorem source_full_center_cubicRatio_lt_two_ambient
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSp
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 (2^n))
    (V U : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hcard : (2^n)^2 ≤ Nat.card (V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))))
    (hfit : generalizedFitting H = pCore 2 H)
    (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H)) :
    cubicRatio (DihedralCubic.canonicalAction U V hU) < 2 := by
  obtain ⟨F,hF,hfin,hFcard,⟨e⟩⟩ := hm
  let : CharP F 2 := EvenProjective.charTwo_of_card hFcard
  obtain ⟨w⟩ := source_full_center_quotient T hP hs K hK hgen hn hFcard e V hVT hvn hVM hcard
  let M := ChapterB.minimalParabolicMax T hP
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  have hTV := (normal_subgroupOf_iff_le_normalizer hVT).mp hvn
  have hNV := minimalParabolic_normalizer_le T hP V (IsElementaryAbelian.isPGroup 2 V) hTV hout
  obtain ⟨w',r,_,hr,ξ,hξ⟩ := QuotientLift.lift_pair T hP V hVT hvn hVM w.pair
  have hrV : (V.subgroupOf w'.subgroup).map r = (V.map q).subgroupOf w.pair.subgroup := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      change (r x : H ⧸ J) ∈ V.map q
      rw [hr]
      exact mem_map_of_mem q hx
    · intro hy
      obtain ⟨x,hx,hxy⟩ := hy
      let z : w'.subgroup := ⟨x,w'.le hx⟩
      refine ⟨z,hx,Subtype.ext ?_⟩
      rw [hr]
      exact hxy
  have hξmap : (ξ.trans w.quotientModel).toMonoidHom.comp (QuotientGroup.mk' _) =
      (w.quotientModel.toMonoidHom.comp (QuotientGroup.mk' _)).comp r := by
    apply MonoidHom.ext
    intro x
    change w.quotientModel (ξ (QuotientGroup.mk' _ x)) = w.quotientModel (QuotientGroup.mk' _ (r x))
    rw [hξ]
  have hVS : (V.subgroupOf w'.subgroup).map ((ξ.trans w.quotientModel).toMonoidHom.comp
      (QuotientGroup.mk' _)) ≤
      (center (unipotentSylow hFcard (by omega : 1 ≤ n))).map
        (unipotentSylow hFcard (by omega : 1 ≤ n) : Subgroup (Sp F)).subtype := by
    rw [hξmap,←map_map,hrV]
    exact w.quotient_center hFcard (by omega)
  have hproper := w'.proper_of_quotient_card_ne_one hNV (by
    rw [Nat.card_congr (ξ.trans w.quotientModel).toEquiv]
    have hd : 2 ∣ Nat.card (Sp F) := by
      rw [card_sp,hFcard]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
        ((dvd_pow_self 2 (by omega : n ≠ 0)).trans (dvd_pow_self _ (by decide : 4 ≠ 0))) _) _
    intro he
    rw [he] at hd
    norm_num at hd)
  let := DihedralCubic.centralizer_normal U V hU
  exact (DihedralCubic.ambient_cubic_actor_strict_symplectic_four_of_positive_exponent
    w'.le hU (w'.hypotheses hVT hTV hVM hNV)
    (w'.sylow_eq.le.trans (inf_le_left.trans hTU)) hproper (w'.fitting hTV hfit)
    n (by omega) hFcard (ξ.trans w.quotientModel) (unipotentSylow hFcard (by omega)) hVS
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)).2.2.2.2.2

/-- The order-two endpoint needs no model classification or TI premise. -/
theorem source_order_two_cubicRatio_le_two
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (V U : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hcard : Nat.card (V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) = 2)
    (hfit : generalizedFitting H = pCore 2 H)
    (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H)) :
    cubicRatio (DihedralCubic.canonicalAction U V hU) ≤ 2 := by
  obtain ⟨w⟩ := Involution.source_star_order_two T hP V hVT hvn hVM hcard
  have hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP := by
    intro h
    have he : V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)) = ⊥ :=
      (map_eq_bot_iff V).mpr (by simpa only [QuotientGroup.ker_mk'] using h)
    rw [he,Subgroup.card_bot] at hcard
    omega
  exact BenderPlacement.original_witness_cubicRatio_le_two hP hVT hvn hVM hout hfit
    (BenderPlacement.OriginalWitness.of_dihedral (n := 1) w) hTU hU

/-- The actual no-TI symplectic source is reduced to proper noncyclic images.
The remaining disjunct is an outstanding recognition case, not a cubic bound. -/
theorem source_cubicRatio_le_two_or_middle_image
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSp
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 (2^n))
    (V U : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H)
    (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H)) :
    cubicRatio (DihedralCubic.canonicalAction U V hU) ≤ 2 ∨
      (2 < Nat.card (V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) ∧
      Nat.card (V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) < (2^n)^2) := by
  by_cases hsmall : Nat.card (V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) = 2
  · exact Or.inl (source_order_two_cubicRatio_le_two T hP V U hVT hvn hVM hsmall hfit hTU hU)
  by_cases hlarge : (2^n)^2 ≤ Nat.card (V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)))
  · exact Or.inl (source_full_center_cubicRatio_lt_two_ambient T hP hs K hK hgen hn hm
      V U hVT hVM hout hvn hlarge hfit hTU hU).le
  have hne : V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)) ≠ ⊥ := by
    intro he
    exact hout (by simpa only [QuotientGroup.ker_mk'] using (map_eq_bot_iff V).mp he)
  have hc := (one_lt_card_iff_ne_bot _).mpr hne
  exact Or.inr ⟨by omega,by omega⟩

end CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour
