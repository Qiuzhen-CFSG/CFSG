module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Actions

/-!
# The marked radical layer of the point parabolic

The point-stabilizer action restricts to a surjection from O₂(P) onto the
geometric line radical. Its kernel is exactly the old O₂(L), in the two
successive subgroup carriers. The first isomorphism theorem therefore gives
the actual quotient O₂(P)/O₂(L), of order eight, and the original action map
intertwines its conjugation marking. No abstract order-based identification
is used.

The supplied containment U_L ≤ O₂(P) also implies U_L ≤ O₂(L): U_L is a
two-group contained in L and normalized by L. These results prepare the
ordered chief layers; irreducibility and their complete flag remain separate
proof obligations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.24, printed pp.1129–1130.
-/

@[expose] public section
open Subgroup BinaryLinear.OuterCyclic
open BinaryNaturalDual.VectorStabilizers BinaryNaturalDual.VectorStabilizers.Pure
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic
universe u
variable {G : Type u} [Group G] {d : LocalData G} {L : Subgroup G}

/-- The supplied containment already places the whole module in the old core. -/
theorem module_le_componentCore (h : NaturalDual d L) (x : Space 4)
    (hU : spanCommutator d L ≤ (point h x).pCoreIn 2) :
    spanCommutator d L ≤ L.pCoreIn 2 := by
  apply le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 (point h x)).to_le hU)
  · exact hU.trans ((pCoreIn_le 2 (point h x)).trans (point_le h x))
  · exact normalizer_commutator_ge_right _ _

/-- The geometric radical marking of the actual parabolic two-core. -/
noncomputable def coreActor (h : NaturalDual d L) (x : Space 4) :
    pCore 2 (point h x) →* pointKernel x where
  toFun q := ⟨pointActor h x q.val, point_core_actor h x q.val q.property⟩
  map_one' := Subtype.ext (map_one (pointActor h x))
  map_mul' q r := Subtype.ext (map_mul (pointActor h x) q.val r.val)

theorem coreActor_surjective [Finite G] (h : NaturalDual d L) (x : Space 4) :
    Function.Surjective (coreActor h x) := by
  intro q
  obtain ⟨p, hp⟩ := pointActor_surjective h x q.val
  have hc : p ∈ pCore 2 (point h x) := by
    rw [← quotientActor_ker h x]
    change pointQuotientAction x (pointActor h x p) = 1
    rw [hp]
    exact q.property
  exact ⟨⟨p, hc⟩, Subtype.ext hp⟩

/-- The kernel is exactly O₂(L), pulled into the two nested carriers. -/
theorem coreActor_ker (h : NaturalDual d L) (x : Space 4) :
    (coreActor h x).ker = ((L.pCoreIn 2).subgroupOf (point h x)).subgroupOf
      (pCore 2 (point h x)) := by
  ext q
  change coreActor h x q = 1 ↔ ((q.val : point h x) : G) ∈ L.pCoreIn 2
  have he : coreActor h x q = 1 ↔ pointActor h x q.val = 1 :=
    ⟨fun hh => congrArg Subtype.val hh, fun hh => Subtype.ext hh⟩
  rw [he]
  change q.val ∈ (pointActor h x).ker ↔ _
  rw [pointActor_ker]
  rfl

/-- The actual relative old core, inside the intrinsic new core. -/
noncomputable def oldCoreInCore (h : NaturalDual d L) (x : Space 4) :
    Subgroup (pCore 2 (point h x)) :=
  ((L.pCoreIn 2).subgroupOf (point h x)).subgroupOf (pCore 2 (point h x))

instance oldCoreInCore_normal (h : NaturalDual d L) (x : Space 4) :
    (oldCoreInCore h x).Normal := by
  change (((L.pCoreIn 2).subgroupOf (point h x)).subgroupOf _).Normal
  rw [← coreActor_ker]
  infer_instance

/-- O₂(P)/O₂(L) is the geometric radical, through the original action map. -/
noncomputable def coreQuotientEquivKernel [Finite G] (h : NaturalDual d L) (x : Space 4) :
    (pCore 2 (point h x) ⧸ oldCoreInCore h x) ≃* pointKernel x :=
  (QuotientGroup.quotientMulEquivOfEq
    (show oldCoreInCore h x = (coreActor h x).ker from (coreActor_ker h x).symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (coreActor h x) (coreActor_surjective h x))

@[simp] theorem coreQuotientEquivKernel_mk [Finite G] (h : NaturalDual d L) (x : Space 4)
    (q : pCore 2 (point h x)) :
    coreQuotientEquivKernel h x (QuotientGroup.mk' (oldCoreInCore h x) q) =
      coreActor h x q := rfl

/-- The radical section has order eight, with its marked quotient retained above. -/
theorem coreQuotient_card [Finite G] (h : NaturalDual d L) {x : Space 4} (hx : x ≠ 0) :
    Nat.card (pCore 2 (point h x) ⧸ oldCoreInCore h x) = 8 := by
  rw [Nat.card_congr (coreQuotientEquivKernel h x).toEquiv, pointKernel_card hx]
  simp [Space]

/-- The radical quotient marking respects conjugation by each original element of P. -/
theorem coreActor_conj (h : NaturalDual d L) (x : Space 4)
    (p : point h x) (q : pCore 2 (point h x)) :
    (coreActor h x ⟨p * q.val * p⁻¹,
      (inferInstance : (pCore 2 (point h x)).Normal).conj_mem q.val q.property p⟩ : pointStabilizer x) =
      pointActor h x p * (coreActor h x q : pointStabilizer x) * (pointActor h x p)⁻¹ := by
  change pointActor h x (p * q.val * p⁻¹) = _
  rw [map_mul, map_mul, map_inv]
  rfl

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic
end
