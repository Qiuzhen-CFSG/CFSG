module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Basic
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Action
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.Basic
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.Basic
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Local control for the degree-eight configuration

Both choices of `Y₊` are two-perfect. Thus the genuine preliminary dichotomy
15.3.2(4), together with the noncentral action of `Y₊`, gives the unique
maximal two-local overgroup of `Y₊T`. The fixed plane is `T`-invariant, so
its three-prime residual centralizer joined with `S` is also invariant.
A compatible natural-eight action places the component module in `S`.

The natural-eight action is still an explicit input here. These deductions
do not construct it or identify the residual centralizers.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.2(4), 15.3.10 and the proof of 15.3.32, printed pp.1121, 1123, 1133.
-/

@[expose] public section

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry
variable {G : Type*} [Group G] [Finite G]
/-- Either choice in Hypothesis 15.3.10 has no nontrivial two-group quotient. -/
theorem yplus_isPPerfect (d : LocalData G) : IsPPerfect 2 d.Yplus := by
  rcases d.choice with h | ⟨_, h⟩
  · rw [h]
    exact residualY_isPPerfect _ _
  · rw [h, ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
    exact isPPerfect_embedded_pResidual 2 _

omit [Finite G] in
/-- Both source choices of `Y₊` lie inside `M`. -/
theorem yplus_le_M (d : LocalData G) : d.Yplus ≤ d.M := by
  have hYM : d.Y ≤ d.M := Chapter14.SourcePreliminaries.sourceResidual_le _ _
  rcases d.choice with h | ⟨_, h⟩
  · exact h ▸ hYM
  · rw [h]
    exact (map_subtype_le _).trans (inf_le_left.trans hYM)

/-- The noncentral action excludes the small-residual branch of 15.3.2(4). -/
theorem unique_yplus_join_sylow (d : LocalData G)
    (hnoncentral : ¬ d.Yplus ≤ centralizer (d.V : Set G))
    (hcases : ∀ X : Subgroup G, (d.T : Subgroup G) ≤ X → X ≤ d.M →
      twoResidualAmbient X ≤ centralizer (d.V : Set G) ∨
        Chapter4.UniqueMaximalOvergroup X d.M) :
    Chapter4.UniqueMaximalOvergroup (d.Yplus ⊔ (d.T : Subgroup G)) d.M := by
  rcases hcases _ le_sup_right (sup_le (yplus_le_M d) d.sylow_le) with hc | hu
  · have h := map_pResidual_le 2 (inclusion (show d.Yplus ≤ d.Yplus ⊔ (d.T : Subgroup G) from le_sup_left))
    rw [(pResidual_eq_top_iff 2 d.Yplus).mpr (yplus_isPPerfect d)] at h
    have hm := map_mono (f := (d.Yplus ⊔ (d.T : Subgroup G)).subtype) h
    rw [Subgroup.map_map, ← MonoidHom.range_eq_map,
      show (d.Yplus ⊔ (d.T : Subgroup G)).subtype.comp (inclusion le_sup_left) =
        d.Yplus.subtype from rfl, range_subtype] at hm
    rw [ComponentIntersection.twoResidualAmbient_eq_map_pResidual] at hc
    exact (hnoncentral (hm.trans hc)).elim
  · exact hu

omit [Finite G] in
/-- An index-two plane stabilizer has a `T`-invariant fixed plane. -/
theorem fixedPlane_normalized_by_sylow (d : LocalData G)
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2) :
    (d.T : Subgroup G) ≤ normalizer (d.ZS : Set G) := by
  have hTS : (d.T : Subgroup G) ≤ normalizer (d.S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show d.S ≤ (d.T : Subgroup G) from inf_le_left)).mp
      (normal_of_index_eq_two hindex)
  have hTV := d.sylow_le.trans d.action.normalizes
  have hTC := hTS.trans (normalizer_le_normalizer_centralizer d.S)
  intro t ht x
  exact and_congr (hTV ht x) (hTC ht x)

omit [Finite G] in
/-- `T` normalizes `XS` for the genuine three-prime residual of `C_G(Z_S)`. -/
theorem residual_join_normalized_by_sylow (d : LocalData G)
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2) :
    (d.T : Subgroup G) ≤ normalizer
      ((RankOne.threeResidualIn (centralizer (d.ZS : Set G)) ⊔ d.S : Subgroup G) : Set G) := by
  have hTS : (d.T : Subgroup G) ≤ normalizer (d.S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show d.S ≤ (d.T : Subgroup G) from inf_le_left)).mp
      (normal_of_index_eq_two hindex)
  have hTZ := fixedPlane_normalized_by_sylow d hindex
  have hTX := (hTZ.trans (normalizer_le_normalizer_centralizer d.ZS)).trans
    (normalizer_le_normalizer_characteristic_image (centralizer (d.ZS : Set G))
      (primePowerGenerated 3 (centralizer (d.ZS : Set G))))
  exact (le_inf hTX hTS).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- A compatible natural-eight module is a normal two-subgroup and lies in `S`. -/
theorem componentModule_le_sylow (d : LocalData G) {I : Subgroup G}
    (hI : I ∈ d.Hplus) (c : ComponentWitness d I)
    (a : NaturalEightAction I (d.componentModule I c.L))
    (S : Sylow 2 I) (hS : (S : Subgroup I).map I.subtype = d.S) :
    d.componentModule I c.L ≤ d.S := by
  let U := d.componentModule I c.L
  let _ : IsElementaryAbelian 2 U := {
    toIsMulCommutative := ⟨⟨fun x y => a.coordinates.injective (by simp only [map_mul, mul_comm])⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro u
      apply a.coordinates.injective
      rw [map_pow, map_one]
      change (2 : ℕ) • (a.coordinates u).toAdd = 0
      rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
      exact zero_smul (ZMod 2) _) }
  have hZS : d.Z ≤ d.S := (le_conjugateSpanBy d.Z d.M).trans
    (d.action.le_planeStabilizer d.T d.sylow_le (localModule_le d.T d.sylow_le) 1)
  have hUI : U ≤ I := (Subgroup.commutator_le_sup _ _).trans (sup_le
    (conjugateSpanBy_le_self (hZS.trans (le_sup_right.trans hI.1.2))) (component_le c))
  have hUQ : U ≤ I.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 U) hUI a.normalizes
  exact hUQ.trans (hS ▸ pCoreIn_le_sylow I S)

omit [Finite G] in
/-- The local two-core centralizes every `I`-conjugate of the central involutions. -/
theorem core_le_star_kernel (d : LocalData G) {I : Subgroup G}
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S) :
    I.pCoreIn 2 ≤ (d.starMap I).ker.map I.subtype := by
  have hQT : I.pCoreIn 2 ≤ (d.T : Subgroup G) :=
    (show I.pCoreIn 2 ≤ d.S from hP ▸ pCoreIn_le_sylow I P).trans inf_le_left
  have hIQ : I ≤ normalizer (I.pCoreIn 2 : Set G) :=
    I.le_normalizer.trans (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hUZ : d.UI I ≤ centralizer (I.pCoreIn 2 : Set G) :=
    conjugateSpanBy_le
      ((centralInvolutions_le_centralizer_sylow d.T).trans (centralizer_le hQT))
      (hIQ.trans (normalizer_le_normalizer_centralizer _))
  change I.pCoreIn 2 ≤ (localActionMap d.Z I).ker.map I.subtype
  rw [show (localActionMap d.Z I).ker = localActionKernel d.Z I from
    QuotientGroup.ker_mk' _, localActionKernel, subgroupOf_map_subtype]
  exact le_inf (le_centralizer_iff.mp hUZ) (pCoreIn_le 2 I)

omit [Finite G] in
/-- The component commutator lies in the invariant local span. -/
theorem componentModule_le_span (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) : d.componentModule I c.L ≤ d.UI I :=
  le_normalizer_iff_commutator_le_left.mp
    ((component_le c).trans (le_normalizer_conjugateSpanBy d.Z I))

omit [Finite G] in
/-- The component-module centralizer equality also identifies the original star kernel. -/
theorem star_kernel_eq_core_of_centralizer (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hcentralizer : I ⊓ centralizer (d.componentModule I c.L : Set G) = I.pCoreIn 2) :
    (d.starMap I).ker.map I.subtype = I.pCoreIn 2 := by
  apply le_antisymm ?_ (core_le_star_kernel d P hP)
  change (localActionMap d.Z I).ker.map I.subtype ≤ I.pCoreIn 2
  rw [show (localActionMap d.Z I).ker = localActionKernel d.Z I from
    QuotientGroup.ker_mk' _, localActionKernel, subgroupOf_map_subtype]
  exact (le_inf inf_le_right
    (inf_le_left.trans (centralizer_le (componentModule_le_span d c)))).trans hcentralizer.le

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry

end
