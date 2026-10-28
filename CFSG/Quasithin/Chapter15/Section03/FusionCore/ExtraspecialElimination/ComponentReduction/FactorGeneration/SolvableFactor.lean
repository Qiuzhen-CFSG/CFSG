module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.StarLifting
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.Preparation
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.Theta
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ResidualNormalizer
public import Theory.GroupTheory.SymmetricThreeTwoCore
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Algebra of the putative solvable factor

A candidate has an actual S₃ star image, a rank-two commutator module on the
specified SectionAction, the cubic commutator-generation identity, and at most
two conjugates. Its carrier is the full inverse image inside J_H. These data
must be derived from the exhaustive B.5.6 analysis; this module does not assert
that a candidate exists when component generation fails.

The two-conjugate bound makes the two-perfect Y₀ normalize the star image.
Kernel saturation lifts this to the carrier. Its literal quotient by its own
two-core is S₃. The cubic subgroup escapes Y₀*T* because the selected actor lies
in that overgroup's two-core, and lifting order-three elements gives θ(L) ≰ Y₀.
Thus L is outside M, and the residual-normalizer argument proves that L* cannot
centralize Y₀*. The rank-two module and seed-normalizer argument still has to
contradict these two conclusions; it is not assumed here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49(i), printed pp.1143–1144, using B.5.6, printed pp.105–110.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration
variable {G : Type*} [Group G]

noncomputable def threeCoreImage (H L : Subgroup G) : Subgroup (H ⧸ pCore 2 H) :=
  (pCore 3 (starImage H L)).map (starImage H L).subtype

structure SolvableStarFactor (H ZS Z A : Subgroup G)
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z) where
  carrier : Subgroup G
  le_span : carrier ≤ localSpan A H
  kernel_le : localSpan A H ⊓ localTwoCore H ≤ carrier
  subnormal : (carrier.subgroupOf H).IsSubnormal
  model : starImage H carrier ≃* Equiv.Perm (Fin 3)
  three_generation : threeCoreImage H carrier = ⁅threeCoreImage H carrier, starImage H A⁆
  commutator_rank : Module.finrank (ZMod 2)
    (Representation.Coinvariants.ker (action.representation.comp (starImage H carrier).subtype)) = 2
  conjugacy_bound : (Set.range fun h : H ⧸ pCore 2 H =>
    (starImage H carrier).map (MulAut.conj h).toMonoidHom).ncard ≤ 2

private theorem symmetric_three_core_card :
    Nat.card (pCore 3 (Equiv.Perm (Fin 3))) = 3 := by
  have ha : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hle : alternatingGroup (Fin 3) ≤ pCore 3 (Equiv.Perm (Fin 3)) :=
    le_sSup ⟨inferInstance, IsPGroup.of_card (n := 1) (by simpa only [pow_one] using ha)⟩
  have hd := card_dvd_of_le hle
  rw [ha] at hd
  have hd6 : Nat.card (pCore 3 (Equiv.Perm (Fin 3))) ∣ 6 := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] using
      (pCore 3 (Equiv.Perm (Fin 3))).card_subgroup_dvd_card
  have hc : Nat.Coprime (Nat.card (pCore 3 (Equiv.Perm (Fin 3)))) 2 := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 3) (G := Equiv.Perm (Fin 3))).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_left n
  have hd3 : Nat.card (pCore 3 (Equiv.Perm (Fin 3))) ∣ 3 := hc.dvd_mul_left.mp hd6
  exact Nat.dvd_antisymm hd3 hd

namespace SolvableStarFactor
variable {H ZS Z A : Subgroup G} [IsElementaryAbelian 2 (localSpan ZS H)]
  {action : SectionAction H (localSpan ZS H) Z}
  (F : SolvableStarFactor H ZS Z A action)

/-- Projection of the ambient factor to the specified concrete S₃ model. -/
noncomputable def modelProjection (hAH : A ≤ H) :
    F.carrier →* Equiv.Perm (Fin 3) :=
  F.model.toMonoidHom.comp
    (((QuotientGroup.mk' (pCore 2 H)).subgroupMap (F.carrier.subgroupOf H)).comp
      (subgroupOfEquivOfLe
        (F.le_span.trans (conjugateSpanBy_le_self hAH))).symm.toMonoidHom)

theorem modelProjection_surjective (hAH : A ≤ H) :
    Function.Surjective (F.modelProjection hAH) :=
  F.model.surjective.comp
    (((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective _).comp
      (subgroupOfEquivOfLe
        (F.le_span.trans (conjugateSpanBy_le_self hAH))).symm.surjective)

theorem modelProjection_kernel [Finite G] (hAH : A ≤ H) :
    (F.modelProjection hAH).ker = pCore 2 F.carrier := by
  apply ker_eq_twoCore_of_surjective_perm_three _ (F.modelProjection_surjective hAH)
  let e := (subgroupOfEquivOfLe
    (F.le_span.trans (conjugateSpanBy_le_self hAH))).symm
  let q := (QuotientGroup.mk' (pCore 2 H)).subgroupMap (F.carrier.subgroupOf H)
  have hq : IsPGroup 2 q.ker := by
    dsimp [q]
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (F.carrier.subgroupOf H).subtype_injective
  have he : (F.modelProjection hAH).ker = q.ker.comap e.toMonoidHom := by
    ext x
    change F.model (q (e x)) = 1 ↔ q (e x) = 1
    exact F.model.map_eq_one_iff
  rw [he]
  exact hq.comap_of_injective e.toMonoidHom e.injective

/-- The model identifies the intrinsic quotient, not only the ambient image. -/
noncomputable def quotientModel [Finite G] (hAH : A ≤ H) :
    (F.carrier ⧸ pCore 2 F.carrier) ≃* Equiv.Perm (Fin 3) :=
  (QuotientGroup.quotientMulEquivOfEq (F.modelProjection_kernel hAH).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (F.modelProjection_surjective hAH))

theorem three_card : Nat.card (threeCoreImage H F.carrier) = 3 := by
  rw [threeCoreImage, card_map_of_injective (starImage H F.carrier).subtype_injective]
  have he := pCore_map_iso 3 F.model
  have hc := card_map_of_injective (f := F.model.toMonoidHom)
    (K := pCore 3 (starImage H F.carrier)) F.model.injective
  rw [he] at hc
  exact hc.symm.trans symmetric_three_core_card

theorem star_normalizes [Finite G] (Y0 : Subgroup G)
    (hYH : Y0 ≤ H) (hY : IsPPerfect 2 Y0) :
    starImage H Y0 ≤ normalizer (starImage H F.carrier : Set (H ⧸ pCore 2 H)) :=
  star_normalizes_of_two_conjugates H Y0 F.carrier hYH hY F.conjugacy_bound

/-- The canonical lift is normalized by the two-perfect source residual. -/
theorem normalizes [Finite G] (Y0 : Subgroup G)
    (hAH : A ≤ H) (hYH : Y0 ≤ H) (hY : IsPPerfect 2 Y0) :
    Y0 ≤ normalizer (F.carrier : Set G) :=
  normalizes_saturated_of_star_normalizes H (localSpan A H) F.carrier Y0
    (F.le_span.trans (conjugateSpanBy_le_self hAH)) hYH F.le_span F.kernel_le
    (hYH.trans (le_normalizer_conjugateSpanBy A H)) (F.star_normalizes Y0 hYH hY)

theorem theta_escape [Finite G] (Y0 T : Subgroup G) (hAH : A ≤ H)
    (hA : starImage H A ≤
      (pCore 2 ↥(starImage H Y0 ⊔ starImage H T)).map
        (starImage H Y0 ⊔ starImage H T).subtype) :
    ¬ theta F.carrier ≤ Y0 := by
  apply theta_escape_of_star_three_subgroup H F.carrier Y0
    (F.le_span.trans (conjugateSpanBy_le_self hAH)) (threeCoreImage H F.carrier)
    F.three_card (map_subtype_le _)
  intro hRY
  have hne : threeCoreImage H F.carrier ≠ ⊥ := by
    intro hb
    have hc := F.three_card
    rw [hb] at hc
    norm_num at hc
  exact three_factor_escapes_star_overgroup H Y0 T A _
    (pCore_isPGroup.map _) hne F.three_generation hA (hRY.trans le_sup_left)

/-- Escaping cubic generators also exclude containment in the source intersection. -/
theorem not_le_M [Finite G] (M Y0 T : Subgroup G) (hAH : A ≤ H)
    (hθ : theta (M ⊓ H) = Y0)
    (hA : starImage H A ≤
      (pCore 2 ↥(starImage H Y0 ⊔ starImage H T)).map
        (starImage H Y0 ⊔ starImage H T).subtype) : ¬ F.carrier ≤ M := by
  intro hLM
  exact F.theta_escape Y0 T hAH hA
    ((theta_mono (le_inf hLM (F.le_span.trans
      (conjugateSpanBy_le_self hAH)))).trans_eq hθ)

theorem commutator_not_le_twoCore [Finite G] (M Y0 T : Subgroup G)
    (hAH : A ≤ H) (hY : IsPPerfect 2 Y0)
    (hN : normalizer (Y0 : Set G) = M) (hQM : localTwoCore H ≤ M)
    (hθ : theta (M ⊓ H) = Y0)
    (hA : starImage H A ≤
      (pCore 2 ↥(starImage H Y0 ⊔ starImage H T)).map
        (starImage H Y0 ⊔ starImage H T).subtype) :
    ¬ ⁅F.carrier, Y0⁆ ≤ localTwoCore F.carrier :=
  commutator_not_le_twoCore_of_theta H M Y0 F.carrier hY hN
    (F.le_span.trans (conjugateSpanBy_le_self hAH)) F.subnormal hQM hθ
    (F.theta_escape Y0 T hAH hA)

/-- The residual-normalizer contradiction expressed in the faithful star action.
The rank-two module argument must force this commutator to be trivial. -/
theorem star_commutator_ne_bot [Finite G] (M Y0 T : Subgroup G)
    (hAH : A ≤ H) (hYH : Y0 ≤ H) (hY : IsPPerfect 2 Y0)
    (hN : normalizer (Y0 : Set G) = M) (hQM : localTwoCore H ≤ M)
    (hθ : theta (M ⊓ H) = Y0)
    (hA : starImage H A ≤
      (pCore 2 ↥(starImage H Y0 ⊔ starImage H T)).map
        (starImage H Y0 ⊔ starImage H T).subtype) :
    ⁅starImage H F.carrier, starImage H Y0⁆ ≠ ⊥ := by
  intro hc
  exact F.commutator_not_le_twoCore M Y0 T hAH hY hN hQM hθ hA
    (commutator_le_twoCore_of_star_commutes H F.carrier Y0
      (F.le_span.trans (conjugateSpanBy_le_self hAH)) hYH
      (F.normalizes Y0 hAH hYH hY) hc)

end SolvableStarFactor
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration
