module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.QuotientLift
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.SymplecticStrict
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.SylowKernelCore

/-!
# Original source geometry and strict bounds for lifted pairs

Restrict the original Sylow subgroup and local two-core to a generated
pair. This proves all E.2.10 hypotheses, while normalization by the ambient
two-core gives generalized-Fitting inheritance. A nontrivial prescribed
quotient ensures properness. The symplectic application then proves the
strict cubic bound on the literal ambient normalizer action on V.

This applies to the actual output of `lift_pair`; only construction of the
original model pair in H/J remains independent. Source: E.2.9(2), E.2.11(1)
and E.2.15, printed pp.221–224,228.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.QuotientLift
variable {H : Type*} [Group H] [Finite H]
  {T : Sylow 2 H} {M V : Subgroup H}

omit [Finite H] in
theorem Pair.hypotheses [IsElementaryAbelian 2 V] (w : Pair T M V)
    (hVT : V ≤ (T : Subgroup H))
    (hTV : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hcore : V ≤ M.pCoreIn 2) (hn : normalizer (V : Set H) ≤ M) :
    TwoConjugate.Hypotheses w.sylow (V.subgroupOf w.subgroup)
      (M.subgroupOf w.subgroup) w.conjugator := by
  have hVS : V.subgroupOf w.subgroup ≤ (w.sylow : Subgroup w.subgroup) := by
    apply (map_le_map_iff_of_injective w.subgroup.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le w.le,w.sylow_eq]
    exact le_inf hVT w.le
  have hST : (w.sylow : Subgroup w.subgroup).map w.subgroup.subtype ≤
      (T : Subgroup H) := w.sylow_eq.le.trans inf_le_left
  have hSN : (w.sylow : Subgroup w.subgroup) ≤
      normalizer (V.subgroupOf w.subgroup : Set w.subgroup) := by
    rw [← subgroupOf_normalizer_eq w.le]
    exact map_le_iff_le_comap.mp (hST.trans hTV)
  have hlocal : V.subgroupOf w.subgroup ≤ (M.subgroupOf w.subgroup).pCoreIn 2 := by
    apply (map_le_map_iff_of_injective w.subgroup.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le w.le,
      map_pCoreIn_of_injective 2 _ _ w.subgroup.subtype_injective,subgroupOf_map_subtype]
    exact (le_inf (le_inf (hcore.trans (pCoreIn_le 2 M)) w.le) hcore).trans
      (inf_pCoreIn_le_of_le 2 inf_le_left)
  refine ⟨IsElementaryAbelian.subgroupOf w.le,hVS,
    (normal_subgroupOf_iff_le_normalizer hVS).mpr hSN,?_,hlocal,w.core_two_closed,w.generate⟩
  rw [← subgroupOf_normalizer_eq w.le]
  exact fun _ hx => hn hx

theorem Pair.fitting (w : Pair T M V)
    (hTV : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hfit : generalizedFitting H = pCore 2 H) :
    generalizedFitting w.subgroup = pCore 2 w.subgroup :=
  Solvable.two_conjugate_fitting T V w.subgroup hTV w.le w.conjugator w.generate hfit

omit [Finite H] in
theorem Pair.proper_of_quotient_card_ne_one (w : Pair T M V)
    (hn : normalizer (V : Set H) ≤ M)
    (hc : Nat.card (w.subgroup ⧸ (M.subgroupOf w.subgroup).normalCore) ≠ 1) :
    V.subgroupOf w.subgroup ≠ ⊤ := by
  intro he
  have hM : M.subgroupOf w.subgroup = ⊤ := by
    apply top_unique
    have hh : normalizer (V.subgroupOf w.subgroup : Set w.subgroup) ≤ M.subgroupOf w.subgroup := by
      rw [← subgroupOf_normalizer_eq w.le]
      exact fun _ hx => hn hx
    simpa only [he,normalizer_eq_top] using hh
  apply hc
  rw [hM,normalCore_eq_self]
  simp

theorem Pair.cubicRatio_lt_two_symplectic
    {F : Type*} [Field F] [Finite F] [CharP F 2] [IsElementaryAbelian 2 V]
    (w : Pair T M V) (hVT : V ≤ (T : Subgroup H))
    (hTV : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hcore : V ≤ M.pCoreIn 2) (hn : normalizer (V : Set H) ≤ M)
    (hfit : generalizedFitting H = pCore 2 H)
    (m : ℕ) (hm : 0 < m) (hcard : Nat.card F = 2^m)
    (ξ : (w.subgroup ⧸ (M.subgroupOf w.subgroup).normalCore) ≃*
      Theory.SpecificGroups.SymplecticFour.Sp F)
    (S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F))
    (hVS : (V.subgroupOf w.subgroup).map (ξ.toMonoidHom.comp
        (QuotientGroup.mk' (M.subgroupOf w.subgroup).normalCore)) ≤
      (center S).map (S : Subgroup _).subtype) :
    cubicRatio (DihedralCubic.canonicalAction (normalizer (V : Set H)) V le_rfl) < 2 := by
  have hg := w.hypotheses hVT hTV hcore hn
  have hproper := w.proper_of_quotient_card_ne_one hn (by
    rw [Nat.card_congr ξ.toEquiv]
    have hd : 2 ∣ Nat.card (Theory.SpecificGroups.SymplecticFour.Sp F) := by
      rw [Theory.SpecificGroups.SymplecticFour.card_sp,hcard]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
        ((dvd_pow_self 2 (by omega : m ≠ 0)).trans (dvd_pow_self _ (by decide : 4 ≠ 0))) _) _
    intro he
    rw [he] at hd
    norm_num at hd)
  let := DihedralCubic.centralizer_normal (normalizer (V : Set H)) V le_rfl
  have hh := DihedralCubic.ambient_cubic_actor_strict_symplectic_four_of_positive_exponent
    w.le le_rfl hg (w.sylow_eq.le.trans (inf_le_left.trans hTV)) hproper (w.fitting hTV hfit)
    m hm hcard ξ S hVS (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _)
  exact hh.2.2.2.2.2
/-- The actual symplectic E.2.15 conclusion after lifting a source pair
from H/J. The independently constructed quotient pair and its original
Sylow-center marking are the only witness inputs. -/
theorem cubicRatio_lt_two_symplectic_of_quotient_pair
    {F : Type*} [Field F] [Finite F] [CharP F 2] [IsElementaryAbelian 2 V]
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hVT : V ≤ (T : Subgroup H))
    (hn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H)
    (w : Pair (T.mapSurjective (QuotientGroup.mk'_surjective (ChapterB.minimalParabolicCore T hP)))
      ((ChapterB.minimalParabolicMax T hP).map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)))
      (V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))))
    (m : ℕ) (hm : 0 < m) (hcard : Nat.card F = 2^m)
    (ξ : (w.subgroup ⧸ (((ChapterB.minimalParabolicMax T hP).map
      (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))).subgroupOf w.subgroup).normalCore) ≃*
      Theory.SpecificGroups.SymplecticFour.Sp F)
    (S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F))
    (hVS : ((V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))).subgroupOf w.subgroup).map
      (ξ.toMonoidHom.comp (QuotientGroup.mk' _)) ≤ (center S).map (S : Subgroup _).subtype) :
    cubicRatio (DihedralCubic.canonicalAction (normalizer (V : Set H)) V le_rfl) < 2 := by
  let M := ChapterB.minimalParabolicMax T hP
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  obtain ⟨w',r,_,hr,e,he⟩ := lift_pair T hP V hVT hn hcore w
  have hTV := (normal_subgroupOf_iff_le_normalizer hVT).mp hn
  have hNV := minimalParabolic_normalizer_le T hP V
    (IsElementaryAbelian.isPGroup 2 V) hTV hout
  have hrV : (V.subgroupOf w'.subgroup).map r = (V.map q).subgroupOf w.subgroup := by
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
  have hemap : (e.trans ξ).toMonoidHom.comp (QuotientGroup.mk' _) =
      (ξ.toMonoidHom.comp (QuotientGroup.mk' _)).comp r := by
    apply MonoidHom.ext
    intro x
    change ξ (e (QuotientGroup.mk' _ x)) = ξ (QuotientGroup.mk' _ (r x))
    rw [he]
  apply w'.cubicRatio_lt_two_symplectic hVT hTV hcore hNV hfit m hm hcard (e.trans ξ) S
  rw [hemap,← map_map,hrV]
  exact hVS

end CFSG.Quasithin.ChapterE.Witnesses.QuotientLift
