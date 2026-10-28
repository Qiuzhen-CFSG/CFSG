module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.ActorCentralizers.Coverage
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.ModelSylow
public import Mathlib.GroupTheory.Nilpotent
/-!
# The order-32 centralizer of a in the marked centralizer

The coordinate centralizer of a has order 32. Its intersection with E is
an elementary four, and the only nonidentity element of this four central
in the whole order-32 group is z. All calculations are transported through
the given equivalence with the actual ambient centralizer C(z).

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, pp.6–7.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
open LocalModelDichotomy
local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
local instance : Fintype TwistedModel := Fintype.ofEquiv
  (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm
@[expose] public def modelActorCentralizer : Subgroup TwistedModel := centralizer {a}
local instance : DecidablePred (· ∈ modelActorCentralizer) := fun x =>
  decidable_of_iff (x * a = a * x) mem_centralizer_singleton_iff.symm
local instance : DecidablePred (· ∈ modelE) := fun x =>
  inferInstanceAs (Decidable (x.right = 1))
public theorem modelActorCentralizer_card : Nat.card modelActorCentralizer = 32 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
public theorem modelActorCentralizer_center_E : ∀ x : TwistedModel,
    x.right = 1 → x * a = a * x → b * x = x * b →
    x = 1 ∨ x = z 0 := by decide +kernel
public theorem modelActorCentralizer_b_mem : b ∈ modelActorCentralizer := by decide +kernel
public theorem modelActorCentralizer_z_mem : z 0 ∈ modelActorCentralizer := by decide +kernel
public theorem modelActorCentralizer_four : ∀ x : TwistedModel,
    x ∈ modelActorCentralizer ⊓ modelE ↔ x = 1 ∨ x = z 0 ∨ x = z 2 ∨ x = z 0 * z 2 := by
  change ∀ x : TwistedModel, (x ∈ modelActorCentralizer ∧ x ∈ modelE) ↔ _
  decide +kernel
local instance : DecidablePred (· ∈ modelActorCentralizer ⊓ modelE) := fun x =>
  decidable_of_iff (x ∈ modelActorCentralizer ∧ x ∈ modelE) mem_inf.symm
public theorem modelActorCentralizer_four_card : Nat.card ↥(modelActorCentralizer ⊓ modelE) = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

universe u
variable {G : Type u} [Group G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)
@[expose] public def actorLocalCentralizer : Subgroup G :=
  centralizer ({into D k a} : Set G) ⊓ D.centralizer
public theorem modelActorCentralizer_map : modelActorCentralizer.map (into D k) =
    actorLocalCentralizer D k := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨mem_centralizer_singleton_iff.mpr
      (by simpa only [map_mul] using congrArg (into D k) (mem_centralizer_singleton_iff.mp hx)),
      (k x).property⟩
  · intro x hx
    obtain ⟨y, hy⟩ := k.surjective ⟨x, hx.2⟩
    have hyx : into D k y = x := congrArg Subtype.val hy
    refine ⟨y, mem_centralizer_singleton_iff.mpr ?_, hyx⟩
    apply into_injective D k
    simpa only [map_mul, hyx] using mem_centralizer_singleton_iff.mp hx.1
public theorem actorLocalCentralizer_card : Nat.card (actorLocalCentralizer D k) = 32 := by
  rw [← modelActorCentralizer_map, card_map_of_injective (into_injective D k),
    modelActorCentralizer_card]
public theorem actorLocalCentralizer_isPGroup : IsPGroup 2 (actorLocalCentralizer D k) :=
  IsPGroup.of_card (n := 5) (by rw [actorLocalCentralizer_card]; rfl)
variable [Finite G]

public theorem actorLocalCentralizer_z_mem : D.z ∈ actorLocalCentralizer D k := by
  rw [← modelActorCentralizer_map, ← into_z_zero D k]
  exact mem_map_of_mem _ modelActorCentralizer_z_mem
omit [Finite G] in
public theorem actorLocalCentralizer_le_normalizer_E : actorLocalCentralizer D k ≤
    normalizer (E D k : Set G) := inf_le_right.trans (centralizer_le_normalizer_E D k)
public theorem actorLocalCentralizer_center_E {x : G}
    (hxU : x ∈ actorLocalCentralizer D k) (hxE : x ∈ E D k)
    (hc : ∀ y ∈ actorLocalCentralizer D k, y * x = x * y) : x = 1 ∨ x = D.z := by
  rw [← modelActorCentralizer_map] at hxU
  obtain ⟨v, hv, rfl⟩ := hxU
  have hvE : v ∈ modelE := by
    rw [← modelE_map D k] at hxE
    exact (mem_map_iff_mem (into_injective D k)).mp hxE
  have hvb : b * v = v * b := by
    apply into_injective D k
    simpa only [map_mul] using hc (into D k b)
      (modelActorCentralizer_map D k ▸ mem_map_of_mem (into D k) modelActorCentralizer_b_mem)
  rcases modelActorCentralizer_center_E v hvE
      (mem_centralizer_singleton_iff.mp hv) hvb with h | h
  · exact Or.inl (by rw [h, map_one])
  · exact Or.inr (by rw [h, into_z_zero])
end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
