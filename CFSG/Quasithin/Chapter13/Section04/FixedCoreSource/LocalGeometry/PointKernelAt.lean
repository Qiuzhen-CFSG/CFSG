module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.PointSourceAt

/-!
# Applying original 13.3.9 to the point-centralizer action kernel

The original reduced omega-orbit contains the fixed line, so its full
centralizer lies in N_G(L). Its non-two-group action kernel has a nontrivial
two-residual normal in the point centralizer. The proved augmentation
13.3.9 theorem identifies this literal residual with the selected L₁ or L₁,+
and proves that its two-core quotient has order three.

This discharges the residual-source premise of LargerRow on the actual
omega-orbit and original quotient maps, using structural facts only at G,T.
The first action core and final symplectic recognition still require their
remaining guarded assembly; no recognition conclusion is assumed here.
Source: Aschbacher--Smith 13.4.4(1--2), p.897, used in 13.4.8, pp.904--905.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Solvable
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem fixed_le_centralizerOmegaOrbit_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D) (z : G) :
    V ⊓ centralizer (L : Set G) ≤ centralizerOmegaOrbit T z := by
  apply le_trans _ (le_conjugateSpanBy _ _)
  intro d hd
  apply (mem_omegaOneCenterAmbient_iff _ _).mpr
  let := D.elementary
  refine ⟨D.le_sylow hd.1, elemPow_eq_one_of_isElementaryAbelian d hd.1, ?_⟩
  intro t ht
  exact (normalizer_component_le_fixed_centralizer_at h structural D m
    (D.sylow_normalizes_component ht) d hd).symm

/-- Its full ambient centralizer lies in the original component normalizer.
This is the specialized centralizer bound used in 13.4.8. -/
theorem centralizerOmegaOrbit_centralizer_le_normalizer_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D) (z : G) :
    centralizer (centralizerOmegaOrbit T z : Set G) ≤ normalizer (L : Set G) := by
  rw [← fixed_centralizer_eq_normalizer_at h structural D m]
  exact centralizer_le (fixed_le_centralizerOmegaOrbit_at h structural D m z)

/-- On the actual larger action kernel, the two-residual is the literal
selected first residual. Its quotient order and all 13.3.9 premises are proved. -/
theorem centralizer_kernel_residual_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hlarge : centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
      (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))) ≠
      pCore 2 (centralizer ({z.val} : Set G)))
 :
    let H := centralizer ({z.val} : Set G)
    let K := centralizer ((centralizerOmegaOrbit T z.val).subgroupOf H : Set H)
    let A := (pResidual 2 K).map K.subtype
    A.map H.subtype = selectedFirstResidual T L V z.val ∧ Nat.card (A ⧸ pCore 2 A) = 3 := by
  let H := centralizer ({z.val} : Set G)
  let U := (centralizerOmegaOrbit T z.val).subgroupOf H
  have hU := centralizerOmegaOrbit_reduced h₀ hz (fun he => hzL (he ▸ one_mem _))
  let := hU.normal
  let K := centralizer (U : Set H)
  let A := (pResidual 2 K).map K.subtype
  let Z := A.map H.subtype
  have hQK : pCore 2 H ≤ K := le_centralizer_iff.mp hU.le_centralizer_pCore
  have hAK : A ≤ K := map_subtype_le _
  have hZM : Z ≤ normalizer (L : Set G) := by
    apply le_trans _ (centralizerOmegaOrbit_centralizer_le_normalizer_at h structural D m z.val)
    rintro x ⟨a,ha,rfl⟩ v hv
    exact congrArg Subtype.val ((hAK ha) ⟨v,centralizerOmegaOrbit_le hz hv⟩ hv)
  have hZn : H ≤ normalizer (Z : Set G) := by
    have hh := A.le_normalizer_map H.subtype
    simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using hh
  have hp : IsPPerfect 2 Z := (isPPerfect_embedded_pResidual 2 K).of_surjective
    (H.subtype.subgroupMap A) (H.subtype.subgroupMap_surjective A)
  have hne : Z ≠ ⊥ := by
    intro he
    have hA : A = ⊥ := (map_eq_bot_iff_of_injective _ H.subtype_injective).mp he
    have hres : pResidual 2 K = ⊥ :=
      (map_eq_bot_iff_of_injective _ K.subtype_injective).mp hA
    have hpK : IsPGroup 2 K := (isPGroup_quotient_pResidual 2).of_equiv
      ((QuotientGroup.quotientMulEquivOfEq hres).trans QuotientGroup.quotientBot)
    exact hlarge (le_antisymm (le_sSup ⟨inferInstance,hpK⟩) hQK)
  obtain ⟨he,hc⟩ := (augmentation_point_residual_at h structural D m z hz hzL hout
    (map_subtype_le _) hZn hZM hp).resolve_left hne
  refine ⟨he,?_⟩
  let e := A.equivMapOfInjective H.subtype H.subtype_injective
  exact (Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv).trans hc

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
