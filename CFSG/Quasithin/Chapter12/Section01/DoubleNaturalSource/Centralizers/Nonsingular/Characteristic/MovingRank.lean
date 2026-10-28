module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.Containing
public import Theory.ElementaryAbelian.PrimeRankCard

/-!
# The faithful moving subgroup in the component central quotient

The original moving subgroup has order 2^(2(n-1)), by the marked natural
and dual hyperplanes. It lies in every surviving ordinary component, and
its intersection with that component's center is trivial because the
point residual has no fixed vectors on the moving space. Thus the literal
central quotient has two-rank at least six or eight, respectively.

These are the rank inputs to the actual model exclusions in `SmallQuotients`.
Source: Aschbacher--Smith, 12.1.1 and H.9.1(4), printed pp.788 and390.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
open BinaryNaturalDual BinaryNaturalDual.VectorStabilizers
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  {B : DoubledBranch T L V n}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
  (S : B.SourceModel)

include S in
/-- The original commutator subgroup has exactly the source moving-space order. -/
theorem nonsingular_moving_card
    (w : componentOrbit V (T : Subgroup G)) (hw : B.quadratic (Additive.ofMul w) = 1) :
    Nat.card (⁅componentOrbit V (T : Subgroup G),B.pointResidual w⁆ : Subgroup G) = 2 ^ (2 * (n - 1)) := by
  have hv : S.setup.quadratic (Additive.ofMul w) = 1 := by rwa [S.quadratic_eq]
  let v := S.setup.model.coordinates (Additive.ofMul w)
  let A := AdaptedPair.movingSpace v
  let e : A ≃ₗ[ZMod 2] (v.2.ker × annihilator v.1) := {
    toFun := fun z => (⟨z.val.1,(AdaptedPair.mem_movingSpace v z.val).mp z.property |>.1⟩,
      ⟨z.val.2,(AdaptedPair.mem_movingSpace v z.val).mp z.property |>.2⟩)
    invFun := fun z => ⟨(z.1.val,z.2.val),
      (AdaptedPair.mem_movingSpace v _).mpr ⟨z.1.property,z.2.property⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have hm : Module.finrank (ZMod 2) (S.setup.moving (Additive.ofMul w)) = 2 * (n - 1) := by
    rw [← S.setup.model.coordinates.finrank_map_eq,
      (S.setup.nonsingular_structure hv).2.2.2.2]
    change Module.finrank (ZMod 2) A = _
    rw [e.finrank_eq,Module.finrank_prod,
      (S.setup.nonsingular_complement_actions hv).2.2.1,
      (S.setup.nonsingular_complement_actions hv).2.2.2.1]
    omega
  rw [← S.moving_eq_ambient_commutator w,card_map_of_injective (componentOrbit V (T : Subgroup G)).subtype_injective,
    binarySubgroup_card,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hm]

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The moving subgroup injects into the literal component central quotient. -/
theorem doubleNatural_adapted_component_centralQuotient_rank
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        2 * (n - 1) ≤ primeRank 2 (K ⧸ center K) := by
  let := D.doubledOrbit_elementary h
  intro S w hw K hK
  let U := ⁅componentOrbit V (T : Subgroup G),B.pointResidual w⁆
  have hUK : U ≤ K := (D.doubleNatural_moving_le_residual h B w).trans
    (D.doubleNatural_adapted_ordinary_component_contains_residual h B S w hw K hK).1
  have hUW : U ≤ componentOrbit V (T : Subgroup G) :=
    le_normalizer_iff_commutator_le_left.mp (B.pointResidual_normalizes_orbit w)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective (inclusion hUW)
    (inclusion_injective hUW)
  let f : U →* K ⧸ center K := (QuotientGroup.mk' (center K)).comp (inclusion hUK)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro u hu
    apply Subtype.ext
    have hz : inclusion hUK u ∈ center K := (QuotientGroup.eq_one_iff _).mp hu
    have hc : (u : G) ∈ centralizer (K : Set G) := by
      intro k hk
      exact congrArg Subtype.val (mem_center_iff.mp hz ⟨k,hk⟩)
    exact mem_bot.mp ((D.doubleNatural_adapted_component_moving_centralizer h B S w hw K hK) ▸
      (show (u : G) ∈ U ⊓ centralizer (K : Set G) from ⟨u.property,hc⟩))
  have hr : primeRank 2 U = 2 * (n - 1) := by
    rw [← IsElementaryAbelian.log_card_eq_primeRank (p := 2),
      S.nonsingular_moving_card w hw.nonsingular,Nat.log_pow (by decide : 1 < 2)]
  rw [← hr]
  exact Theory.GroupTheory.primeRank_le_of_injective 2 f hf

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
