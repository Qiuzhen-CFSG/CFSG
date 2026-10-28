module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.MovingComponent.PairQuotient
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.MovingComponent.Residuals

/-!
# Marked coordinates for the actual two-component orbit

Both factor embeddings land in K₀ = ⟨Kᵀ⟩. The quotient equivalence records
their images, the actor's permutation of the two factors, and a chosen
moving element which interchanges them. No triviality of Z(K₀) is used.
The residual application constructs Lv ≤ K₀ from the cubic quotient and
the actual O^{3'} equality before eliminating the PSL2 model.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, 13.6.6, p.927.
The source model comparison, 1.2.2(a) specialization and cubic Suzuki action
remain assembly obligations; the coordinate theorem assumes only the
single-factor identification, not the product identification.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent
variable {H S : Type*} [Group H] [Group S]

def firstFactor (K T : Subgroup H) : K →* componentOrbit K T :=
  inclusion (le_componentOrbit K T)

def secondFactor (K T : Subgroup H) (t : T) : K →* componentOrbit K T :=
  (inclusion (le_iSup (fun s : T => K.map (MulAut.conj (s : H)).toMonoidHom) t)).comp
    ((MulAut.conj (t : H)).subgroupMap K).toMonoidHom

noncomputable def factorModel (K : Subgroup H)
    (eK : NormalizerAction.componentImage K ≃* S) : K →* S :=
  ((NormalizerAction.componentCentralQuotientEquiv K).trans eK).toMonoidHom.comp
    (QuotientGroup.mk' (center K))

structure PairCoordinates (K T : Subgroup H)
    (eK : NormalizerAction.componentImage K ≃* S) where
  moving : T
  moved : (moving : H) ∉ normalizer (K : Set H)
  orbit_eq : componentOrbit K T = K ⊔ K.conjBy moving
  permutation : ∀ u : T,
    (K.conjBy u = K ∧ (K.conjBy moving).conjBy u = K.conjBy moving) ∨
      (K.conjBy u = K.conjBy moving ∧ (K.conjBy moving).conjBy u = K)
  swap : (K.conjBy moving).conjBy moving = K
  equiv : (componentOrbit K T ⧸ center (componentOrbit K T)) ≃* (S × S)
  factors : ∀ k l : K,
    equiv (QuotientGroup.mk' (center (componentOrbit K T))
      (firstFactor K T k * secondFactor K T moving l)) =
      (factorModel K eK k, factorModel K eK l)

theorem exists_pairCoordinates (K T : Subgroup H) (hK : IsComponent H K)
    (hi : (normalizer (K : Set H)).index = 2)
    (hm : ¬ T ≤ normalizer (K : Set H))
    (eK : NormalizerAction.componentImage K ≃* S) :
    Nonempty (PairCoordinates K T eK) := by
  obtain ⟨t, ht, htn⟩ := SetLike.not_le_iff_exists.mp hm
  have heq := orbit_eq_pair K T hi ht htn
  obtain ⟨e, he⟩ := component_pair_model K hK htn eK
  let c := quotientCenterCongr (MulEquiv.subgroupCongr heq)
  refine ⟨{ moving := ⟨t, ht⟩
            moved := htn
            orbit_eq := heq
            permutation := fun u => pair_permutation K hi htn u
            swap := moving_conjugate_swaps K hi htn
            equiv := c.trans e
            factors := ?_ }⟩
  intro k l
  exact he k l

variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}
open A5Module
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The residual equality of genuine 1.2.2(a) feeds the literal PSL2 exclusion. -/
theorem exclude_psl2_of_cubic_residual (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (hi : (X K).index = 2) (hm : ¬ localT T (markedV s) ≤ X K)
    (hDN : residual s ≤ X K)
    (hcard : Nat.card (residual s ⧸ pCore 2 (residual s)) = 3)
    (hres : primeToResidual 3 (Gv (markedV s)) = componentOrbit K (localT T (markedV s)))
    (hKD : ⁅K, residual s⁆ ≠ ⊥)
    (a : NormalizerAction.componentImage K) (ha : orderOf a = 2)
    (haC : ∀ d : X K, (d : Gv (markedV s)) ∈ residual s →
      Commute (NormalizerAction.quotient K d) (a : XStar K))
    (e : NormalizerAction.componentImage K ≃*
      BenderSuzuki.MatrixGroups.PSL2MatrixGroup F) : False := by
  obtain ⟨t, ht, htn⟩ := SetLike.not_le_iff_exists.mp hm
  have hc : ⁅K, K.conjBy t⁆ = ⊥ := hK.commutator_eq_bot_of_ne (hK.map_conj t)
    (fun he => htn (mem_normalizer_iff_map_conj_eq.mpr he.symm))
  have hD : residual s ≤ K ⊔ K.conjBy t := by
    rw [← orbit_eq_pair K (localT T (markedV s)) hi ht htn, ← hres]
    exact residual_le_cubic_residual s hcard
  exact exclude_psl2_of_pair s K (K.conjBy t) hc hDN hD hKD a ha haC e

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent
