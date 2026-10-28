module

public import Theory.GroupTheory.SolvableResidual.TwoSupplement
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.ThreeSubgroups

/-!
# Perfect subgroups and central action kernels modulo a two-core

A proper normal subgroup of a finite perfect group with quasisimple two-core
quotient is central modulo the two-core. The three-subgroups lemma therefore
bounds the commutator with an external centralizer. This bound descends to a
perfect subgroup R normalized by the two-core of the larger group K: R is the
solvable residual of R O₂(K), so normalizing that product already normalizes R.
The intersection with O₂(K) then lies in O₂(R).

All normalizers and intersections use their displayed ambient group; no
subgroup is assumed normal in a larger simple group. The quotient arguments
use the actual quotient maps.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), Proposition 8.2.8(2), printed p.718
(PDF p.735). The application is `localResidual_centralizer_commutator` in
`CFSG.Quasithin.Chapter8.Section02.Normalizer.GroupDeductions`.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

/-- A proper normal subgroup has central image in the quasisimple two-core quotient. The
quotient map is the literal map modulo O₂(G). -/
theorem normal_kernel_commutator_le_twoCore [Finite G] [Group.IsPerfect G]
    [Theory.GroupTheory.IsQuasisimple (G ⧸ pCore 2 G)]
    (C : Subgroup G) [C.Normal] (hC : C ≠ ⊤) : ⁅C, ⊤⁆ ≤ pCore 2 G := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hcentral : C.map q ≤ center (G ⧸ pCore 2 G) := by
    rcases Theory.GroupTheory.IsQuasisimple.normal_le_center_or_eq_top (C.map q) with hc | ht
    · exact hc
    · have hsup : C ⊔ pCore 2 G = ⊤ := by
        have hm := congrArg (Subgroup.comap q) ht
        simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hm
      have hp := isPGroup_quotient_of_sup_eq_top C (pCore 2 G) pCore_isPGroup hsup
      let : Group.IsNilpotent (G ⧸ C) := hp.isNilpotent
      exact (hC (top_unique (by simpa only [solvableResidual_eq_top] using
        solvableResidual_le_of_solvable_quotient C))).elim
  have hb : (⁅C, ⊤⁆ : Subgroup G).map q = ⊥ := by
    rw [map_commutator]
    apply le_bot_iff.mp
    exact (commutator_mono hcentral le_top).trans
      (commutator_eq_bot_iff_le_centralizer.mpr (center_le_centralizer _)).le
  have hk := (Subgroup.map_eq_bot_iff _).mp hb
  simpa only [q, QuotientGroup.ker_mk'] using hk

/-- A perfect normal subgroup of N_G(U) commutes with C_G(U) modulo its two-core when its
action kernel is central modulo that core. -/
theorem perfect_core_commutator (K U : Subgroup G) [Group.IsPerfect K]
    (hKN : K ≤ normalizer (U : Set G))
    (hNK : normalizer (U : Set G) ≤ normalizer (K : Set G))
    (hker : ⁅K ⊓ centralizer (U : Set G), K⁆ ≤ K.pCoreIn 2) :
    ⁅K, centralizer (U : Set G)⁆ ≤ K.pCoreIn 2 := by
  have hC : normalizer (U : Set G) ≤ normalizer (centralizer (U : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer _)).mp inferInstance
  have hcomm : ⁅K, centralizer (U : Set G)⁆ ≤ K ⊓ centralizer (U : Set G) :=
    le_inf (le_normalizer_iff_commutator_le_left.mp ((centralizer_le_normalizer _).trans hNK))
      (le_normalizer_iff_commutator_le_right.mp (hKN.trans hC))
  have hdouble := (commutator_mono hcomm le_rfl).trans hker
  have hKQ : K ≤ normalizer (K.pCoreIn 2 : Set G) := K.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  have hCQ : centralizer (U : Set G) ≤ normalizer (K.pCoreIn 2 : Set G) :=
    ((centralizer_le_normalizer (U : Set G)).trans hNK).trans
    (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  have hr := commutator_commutator_le_of_rotate_of_le_normalizer hKQ hKQ hCQ
    hdouble (by simpa only [commutator_comm (centralizer (U : Set G)) K] using hdouble)
  rwa [K.commutator_eq_self] at hr

/-- The commutator bound descends to a perfect subgroup normalized by the larger two-core.
The proof first recovers normalization from the solvable residual of R O₂(K). -/
theorem perfect_subgroup_core_commutator [Finite G] (R K C : Subgroup G) [Group.IsPerfect R]
    (hRK : R ≤ K)
    (hQR : K.pCoreIn 2 ≤ normalizer (R : Set G))
    (hKC : ⁅K, C⁆ ≤ K.pCoreIn 2) : ⁅R, C⁆ ≤ R.pCoreIn 2 := by
  let Q := K.pCoreIn 2
  let D := R ⊔ Q
  have hKQ : K ≤ normalizer (Q : Set G) := K.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  have hRD : R ≤ D := le_sup_left
  have hQD : Q ≤ D := le_sup_right
  let : (R.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer (sup_le R.le_normalizer hQR)
  let : Group.IsPerfect (R.subgroupOf D) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hRD).symm.toMonoidHom) (subgroupOfEquivOfLe hRD).symm.surjective
  have hgen : R.subgroupOf D ⊔ Q.subgroupOf D = ⊤ := by
    apply map_injective D.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hRD, map_subgroupOf_eq_of_le hQD,
      ← MonoidHom.range_eq_map, range_subtype]
  have hs : (solvableResidual D).map D.subtype = R := by
    rw [(residuals_of_perfect_normal_sup_twoGroup (R.subgroupOf D) (Q.subgroupOf D)
      (isPGroup_pCoreIn 2 K).comap_subtype hgen).2, map_subgroupOf_eq_of_le hRD]
  have hCD : C ≤ normalizer (D : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr
      (((commutator_mono (sup_le hRK (pCoreIn_le 2 K)) le_rfl).trans hKC).trans le_sup_right)
  have hCR : C ≤ normalizer (R : Set G) := by
    rw [← hs]
    exact hCD.trans (normalizer_le_normalizer_characteristic_image D (solvableResidual D))
  have hcap : R ⊓ Q ≤ R.pCoreIn 2 := le_pCoreIn_of_normalizes
    ((isPGroup_pCoreIn 2 K).to_le inf_le_right) inf_le_left
    ((le_inf R.le_normalizer (hRK.trans hKQ)).trans inf_normalizer_le_normalizer_inf)
  exact (le_inf (le_normalizer_iff_commutator_le_left.mp hCR)
    ((commutator_mono hRK le_rfl).trans hKC)).trans hcap

end Subgroup
