module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.Actions.ChiefModules.Quotients
public import Theory.GroupAction.SmallQuotientCentralization
public import Theory.GroupTheory.CharacteristicCentralizerFusion
/-!
# The actual chief series in the elementary lift

The irreducible moved section gives the middle chief factor. The bottom and
top factors have order two and hence have trivial conjugation actions. All
invariance and interval statements concern the actual ambient subgroups.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private lemma interval_of_index_two (A D : Subgroup G) (hidx : A.relIndex D = 2)
    (E : Subgroup G) (hAE : A ≤ E) (hED : E ≤ D) : E = A ∨ E = D := by
  have hh := relIndex_mul_relIndex A E D hAE hED
  rw [hidx] at hh
  by_cases ha : A.relIndex E = 1
  · exact Or.inl (le_antisymm (relIndex_eq_one.mp ha) hAE)
  · right
    have hd : E.relIndex D = 1 := by
      by_contra hn
      exact (Nat.not_prime_of_mul_eq hh ha hn) (by decide)
    exact le_antisymm hED (relIndex_eq_one.mp hd)

/-- The strict chief flag for the actual P-conjugation action on D. -/
structure LiftChiefSeries (U K : Subgroup G) (z i : G) : Prop where
  normalizes_Z : K ⊔ U ≤ normalizer (zpowers z : Set G)
  normalizes_A : K ⊔ U ≤ normalizer (liftBase U z i : Set G)
  normalizes_D : K ⊔ U ≤ normalizer (centralizerLift U z i : Set G)
  strict : (⊥ : Subgroup G) < zpowers z ∧ zpowers z < liftBase U z i ∧
    liftBase U z i < centralizerLift U z i
  first : ∀ E : Subgroup G, E ≤ zpowers z → E = ⊥ ∨ E = zpowers z
  middle : ∀ E : Subgroup G, zpowers z ≤ E → E ≤ liftBase U z i →
    K ⊔ U ≤ normalizer (E : Set G) → E = zpowers z ∨ E = liftBase U z i
  last : ∀ E : Subgroup G, liftBase U z i ≤ E → E ≤ centralizerLift U z i →
    E = liftBase U z i ∨ E = centralizerLift U z i
  central_Z : K ⊔ U ≤ centralizer (zpowers z : Set G)
  central_top : ⁅centralizerLift U z i, K ⊔ U⁆ ≤ liftBase U z i

namespace MovedCoreModel
variable {U K : Subgroup G} {i : G} {hKU : K ≤ normalizer (U : Set G)}
variable [IsExtraspecial 2 U] (m : MovedCoreModel U K i hKU)
include m

/-- The binary moved-module identification proves every chief-series clause. -/
theorem chief_series (z : G) (hz : orderOf z = 2) (hi : orderOf i = 2)
    (hZ : (center U).map U.subtype = zpowers z)
    (hiU : i ∈ normalizer (U : Set G)) (hiz : i ∈ centralizer ({z} : Set G))
    (hout : i ∉ U) (hKi : K ≤ centralizer ({i} : Set G))
    (hmoved : Nat.card (movedImage U i) = 16) : LiftChiefSeries U K z i := by
  obtain ⟨hD,hDcard,hA,hAcard⟩ := m.elementary_lift z hz hi hZ hiU hiz hout hKi hmoved
  let _ := hD
  have hZcard : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers,hz]
  have hZA : zpowers z ≤ liftBase U z i := le_sup_right
  have hAD : liftBase U z i ≤ centralizerLift U z i :=
    sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hPZ : K ⊔ U ≤ normalizer (zpowers z : Set G) := by
    rw [← hZ]
    exact (sup_le hKU U.le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image U (center U))
  have hPA := liftBase_normalized U K z i hZ hiU hKU hKi hmoved
  have hPD := lift_normalized_by_residual_join_core U K z i hZ hiU hKU hKi hmoved
  have hN : ((liftBase U z i).subgroupOf (centralizerLift U z i)).Normal := by
    let _ := hD
    infer_instance
  have hidx : (liftBase U z i).relIndex (centralizerLift U z i) = 2 := by
    have hh := ((liftBase U z i).subgroupOf (centralizerLift U z i)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hAD).toEquiv,hAcard,hDcard] at hh
    change 32 * (liftBase U z i).relIndex (centralizerLift U z i) = 64 at hh
    omega
  refine ⟨hPZ,hPA,hPD,?_,?_,?_,?_,?_,?_⟩
  · refine ⟨bot_lt_iff_ne_bot.mpr ?_, lt_of_le_of_ne hZA ?_, lt_of_le_of_ne hAD ?_⟩
    · intro he; rw [he,Nat.card_unique] at hZcard; omega
    · intro he; rw [he,hAcard] at hZcard; omega
    · intro he; rw [he,hDcard] at hAcard; omega
  · intro E hE
    have hh : (⊥ : Subgroup G).relIndex (zpowers z) = 2 := by
      rw [relIndex_bot_left,hZcard]
    exact interval_of_index_two ⊥ (zpowers z) hh E bot_le hE
  · intro E hZE hEA hPE
    exact m.invariant_interval z hZ hiU hmoved E hZE hEA (le_sup_left.trans hPE)
  · exact interval_of_index_two _ _ hidx
  · have hc : K ⊔ U ≤ centralizer ({z} : Set G) := by
      rwa [normalizer_zpowers_eq_centralizer_of_order_two z hz] at hPZ
    simpa only [zpowers_eq_closure,centralizer_closure] using hc
  · apply commutator_le_of_normalized_quotient_card_le_two (K ⊔ U)
      (centralizerLift U z i) (liftBase U z i) hPD hPA hN
    exact le_of_eq hidx
end MovedCoreModel

omit [Finite G] in
/-- The actual action on the central line is trivial. -/
theorem LiftChiefSeries.line_action {U K : Subgroup G} {z i : G}
    (s : LiftChiefSeries U K z i) :
    ∃ ρ : ↥(K ⊔ U) →* MulAut (zpowers z), ρ = 1 ∧
      ∀ (p : ↥(K ⊔ U)) (v : zpowers z),
        ((ρ p v : zpowers z) : G) = (p : G) * (v : G) * (p : G)⁻¹ := by
  refine ⟨1,rfl,?_⟩
  intro p v
  change (v : G) = (p : G) * (v : G) * (p : G)⁻¹
  rw [← s.central_Z p.property v v.property]
  simp

omit [Finite G] in
/-- The actual action on the terminal factor D/A is trivial. -/
theorem LiftChiefSeries.top_action {U K : Subgroup G} {z i : G}
    (s : LiftChiefSeries U K z i)
    (hN : ((liftBase U z i).subgroupOf (centralizerLift U z i)).Normal) :
    let _ := hN
    ∃ ρ : ↥(K ⊔ U) →* MulAut (centralizerLift U z i ⧸
      (liftBase U z i).subgroupOf (centralizerLift U z i)),
      ρ = 1 ∧ ∀ (p : ↥(K ⊔ U)) (v : centralizerLift U z i),
        ρ p (QuotientGroup.mk' ((liftBase U z i).subgroupOf (centralizerLift U z i)) v) =
          QuotientGroup.mk' ((liftBase U z i).subgroupOf (centralizerLift U z i))
            ⟨(p : G) * (v : G) * (p : G)⁻¹,
              (mem_normalizer_iff.mp (s.normalizes_D p.property) v).mp v.property⟩ := by
  let _ := hN
  obtain ⟨ρ,hρ⟩ := exists_quotient_conjugation_action (K ⊔ U) (centralizerLift U z i)
    (liftBase U z i) s.normalizes_D s.normalizes_A hN
  refine ⟨ρ,?_,hρ⟩
  have hk := quotient_conjugation_action_kills_commutator_layer (K ⊔ U)
    (centralizerLift U z i) (liftBase U z i) (K ⊔ U) hN s.normalizes_D s.central_top ρ hρ
  apply MonoidHom.ext
  intro p
  have hp : p ∈ (K ⊔ U).subgroupOf (K ⊔ U) := p.property
  exact MonoidHom.mem_ker.mp (hk hp)


omit [Finite G] in
/-- The invariant flag consists of normal subgroups in the actual overgroup P D. -/
theorem LiftChiefSeries.relative_normal {U K : Subgroup G} {z i : G}
    (s : LiftChiefSeries U K z i)
    (hD : IsElementaryAbelian 2 (centralizerLift U z i)) :
    ((zpowers z).subgroupOf (K ⊔ U ⊔ centralizerLift U z i)).Normal ∧
      ((liftBase U z i).subgroupOf (K ⊔ U ⊔ centralizerLift U z i)).Normal ∧
      ((centralizerLift U z i).subgroupOf (K ⊔ U ⊔ centralizerLift U z i)).Normal := by
  let _ := hD
  have hn (E : Subgroup G) (hED : E ≤ centralizerLift U z i)
      (hPE : K ⊔ U ≤ normalizer (E : Set G)) :
      (E.subgroupOf (K ⊔ U ⊔ centralizerLift U z i)).Normal := by
    apply normal_subgroupOf_of_le_normalizer
    exact sup_le hPE (((centralizerLift U z i).le_centralizer.trans
      (centralizer_le hED)).trans (_root_.centralizer_le_normalizer _))
  exact ⟨hn _ (s.strict.2.1.le.trans s.strict.2.2.le) s.normalizes_Z,
    hn _ s.strict.2.2.le s.normalizes_A, hn _ le_rfl s.normalizes_D⟩

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
