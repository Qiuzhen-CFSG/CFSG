module

public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.CoreQuotient
public import Theory.GroupTheory.PerfectSmallNormalizerLift
public import Theory.GroupTheory.PResidual.PrimeToPerfect
public import Mathlib.GroupTheory.Nilpotent

/-!
# Normalization and the original centralizer R in Section 12.6

The small-index argument proves all three conclusions of Lemma 12.6.5
from the preceding local inputs: perfection of L_v, L_v≤K, containment of
O₂(KS) in the original R, and |R:R_v|≤4. The source T-normalization of L
puts R_v in N_G(L_v). The quotient action defining R then lifts through
the actual two-core of KS, giving R≤N_G(L_v). Comparing core quotients
gives R=C_S(L_v/O₂(L_v)) and [L_v,R]≤O₂(L_v).

Perfection and the three local containment/index inputs still require the
preceding A₆ and component analysis; they are not source hypotheses.
Separately, the canonical K_v=O^{3′}(G_v^∞) is two-perfect directly from
its residual construction. Its component membership is not asserted here.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
notation and Lemmas 12.6.3--5, printed pp.823--824.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G]

/-- The original quotient-defined R lies in the chosen local two-subgroup. -/
theorem R_le_S (L K S : Subgroup G) (v : G) : R L K S v ≤ S := inf_le_left

/-- The quotient definition of R already normalizes the image of L_v. -/
theorem R_star_le_normalizer (L K S : Subgroup G) (v : G) :
    starImage (K ⊔ S) (R L K S v) ≤
      normalizer (starImage (K ⊔ S) (Lv L v) : Set (Star (K ⊔ S))) := by
  rintro _ ⟨r, hr, rfl⟩
  obtain ⟨y, hy, he⟩ := hr.2
  have hry : y = r := Subtype.ext he
  subst y
  exact coreQuotientCentralizer_le_normalizer _ hy

/-- T-normalization places R_v in the relative normalizer M_v of L_v. -/
theorem Rv_le_normalizer_Lv (T : Sylow 2 G) (L : Subgroup G)
    (hT : (T : Subgroup G) ≤ M L) (v : G) :
    Rv T L v ≤ normalizer (Lv L v : Set G) := by
  apply (show Rv T L v ≤ Mv L v from ?_).trans (Mv_le_normalizer_Lv L v)
  apply le_inf _ (Rv_le_Gv T L v)
  exact ((pCoreIn_le 2 _).trans inf_le_left).trans (sup_le L.le_normalizer hT)

variable [Finite G]

/-- The literal canonical K_v is two-perfect, before any component recognition. -/
theorem Kv_isPPerfect (v : G) : IsPPerfect 2 (Kv v) := by
  let B := primeToResidual 3 (solvableResidual (Gv v))
  let e := B.equivMapOfInjective (solvableResidual (Gv v)).subtype
    (solvableResidual (Gv v)).subtype_injective
  let e' := (B.map (solvableResidual (Gv v)).subtype).equivMapOfInjective
    (Gv v).subtype (Gv v).subtype_injective
  exact (isPPerfect_primeToResidual (G := solvableResidual (Gv v)) 3 2 (by decide)).of_surjective
    (e.trans e').toMonoidHom (e.trans e').surjective

/-- The normalization conclusion of 12.6.5 from its preceding local inputs. -/
theorem R_le_normalizer_Lv (T : Sylow 2 G) (L K S : Subgroup G) (v : G)
    [Group.IsPerfect (Lv L v)]
    (hT : (T : Subgroup G) ≤ M L)
    (hLK : Lv L v ≤ K)
    (hcore : (K ⊔ S).pCoreIn 2 ≤ R L K S v)
    (hindex : (Rv T L v).relIndex (R L K S v) ≤ 4) :
    R L K S v ≤ normalizer (Lv L v : Set G) := by
  let H := K ⊔ S
  let A := (Lv L v).subgroupOf H
  let B := (R L K S v).subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  have hLH : Lv L v ≤ H := hLK.trans le_sup_left
  have hRH : R L K S v ≤ H := (R_le_S L K S v).trans le_sup_right
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hLH).symm.toMonoidHom)
    (subgroupOfEquivOfLe hLH).symm.surjective
  have hqker : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let : Group.IsNilpotent q.ker := hqker.isNilpotent
  have hkB : q.ker ≤ B := by
    intro x hx
    exact hcore (mem_map_of_mem H.subtype ((QuotientGroup.ker_mk' _).le hx))
  have hi : (normalizer (A : Set H)).relIndex B ≤ 4 := by
    dsimp only [A, B]
    rw [← subgroupOf_normalizer_eq hLH, relIndex_subgroupOf hRH]
    exact (relIndex_le_of_le_left (Rv_le_normalizer_Lv T L hT v)
      index_ne_zero_of_finite).trans hindex
  have hh := le_normalizer_of_perfect_image_of_small_kernel q A B hkB hi
    (R_star_le_normalizer L K S v)
  intro r hr
  have hr' := hh (show (⟨r, hRH hr⟩ : H) ∈ B from hr)
  change (⟨r, hRH hr⟩ : H) ∈ normalizer ((Lv L v).subgroupOf H : Set H) at hr'
  rw [← subgroupOf_normalizer_eq hLH] at hr'
  exact hr'

/-- Only after normalization is the original R identified with C_S(L_v/O₂(L_v)). -/
theorem R_eq_S_inf_coreQuotientCentralizer (T : Sylow 2 G)
    (L K S : Subgroup G) (v : G) [Group.IsPerfect (Lv L v)]
    (hT : (T : Subgroup G) ≤ M L)
    (hLK : Lv L v ≤ K)
    (hcore : (K ⊔ S).pCoreIn 2 ≤ R L K S v)
    (hindex : (Rv T L v).relIndex (R L K S v) ≤ 4) :
    R L K S v = S ⊓ coreQuotientCentralizer (Lv L v) := by
  let H := K ⊔ S
  let A := (Lv L v).subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  have hLH : Lv L v ≤ H := hLK.trans le_sup_left
  have hqker : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hcompare (r : H) (hn : (r : G) ∈ normalizer (Lv L v : Set G)) :
      q r ∈ coreQuotientCentralizer (A.map q) ↔
        (r : G) ∈ coreQuotientCentralizer (Lv L v) := by
    have hrA : r ∈ normalizer (A : Set H) := by
      dsimp only [A]
      rw [← subgroupOf_normalizer_eq hLH]
      exact hn
    have h := (mem_coreQuotientCentralizer_iff_map q A hqker hrA).symm.trans
      (mem_coreQuotientCentralizer_iff_map H.subtype A
        (IsPGroup.ker_isPGroup_of_injective H.subtype_injective) hrA)
    simpa only [A, map_subgroupOf_eq_of_le hLH, subtype_apply] using h
  have hnorm := R_le_normalizer_Lv T L K S v hT hLK hcore hindex
  ext r
  constructor
  · intro hr
    refine ⟨hr.1, ?_⟩
    obtain ⟨y, hy, he⟩ := hr.2
    change (y : G) = r at he
    have hn : (y : G) ∈ normalizer (Lv L v : Set G) := he.symm ▸ hnorm hr
    exact he ▸ (hcompare y hn).mp hy
  · intro hr
    let rH : H := ⟨r, (show S ≤ H from le_sup_right) hr.1⟩
    refine ⟨hr.1, rH, ?_, rfl⟩
    exact (hcompare rH (coreQuotientCentralizer_le_normalizer _ hr.2)).mpr hr.2

/-- The commutator conclusion of 12.6.5 on the original ambient subgroups. -/
theorem commutator_Lv_R_le_core (T : Sylow 2 G)
    (L K S : Subgroup G) (v : G) [Group.IsPerfect (Lv L v)]
    (hT : (T : Subgroup G) ≤ M L)
    (hLK : Lv L v ≤ K)
    (hcore : (K ⊔ S).pCoreIn 2 ≤ R L K S v)
    (hindex : (Rv T L v).relIndex (R L K S v) ≤ 4) :
    ⁅Lv L v, R L K S v⁆ ≤ (Lv L v).pCoreIn 2 := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro r hr a ha
  have hr' := (R_eq_S_inf_coreQuotientCentralizer T L K S v hT hLK hcore hindex).le hr
  exact (mem_coreQuotientCentralizer_iff (Lv L v) r).mp hr'.2 |>.2 a ha

end CFSG.Quasithin.Chapter12.Section06
