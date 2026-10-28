module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.LocalKernel
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.StructureTransport

/-!
# Explicit quaternion and cyclic factors in the HS pair kernel

Five already checked carrier words give two injective quaternion representations
and an injective cyclic representation of order four in the actual pair kernel.
The quaternion images commute, meet in the involution `e0`, and span a subgroup
of order 32. The cyclic image commutes with that subgroup and meets it in the
same involution. Thus their join is an embedded (Q₈ * Q₈) * C₄ of order 64.
An upper bound of 64 for the full pair kernel then identifies its exact shape.

Source: Aschbacher–Smith 16.1.5(10), printed p.1172; GLS3 Table 5.3m,
printed p.274. The quaternion factors are constructed directly in the fixed
ATLAS carrier, rather than inferred from the different dihedral presentation
in GLS3 or from order and exponent. Discovery scripts are retained in `source/`;
all group-map identities, injectivity and intersections are kernel-checked.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure
open Subgroup
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open Sporadic.LeechRelated.HS.EvenLocalCandidates.CentralInvolutionCore
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option Elab.async false

/-- The existing five word witnesses, as elements of the actual pair kernel. -/
def qElement (k : Fin 5) : core :=
  ⟨⟨q k, by
      rw [localGroup_zero_eq_centralizer]
      exact mem_centralizer_singleton_iff.mpr (q_commutes k)⟩,
    (mem_core_iff _).mpr (q_pair k)⟩

def leftI : core := qElement 0 * qElement 2
def leftJ : core := qElement 1 * qElement 3
def rightI : core := qElement 0 * qElement 3
def rightJ : core := qElement 0 * qElement 1 * qElement 2
def cyclicGenerator : core := qElement 0 * qElement 1 * qElement 2 * qElement 3 * qElement 4
def commonInvolution : core := leftI ^ 2

/-- The common involution of all three factors is the specified source representative. -/
theorem commonInvolution_eq_e0 : commonInvolution.val.val = e0 := by decide +kernel

def quaternionMap (i j : core) : QuaternionGroup 2 → core
  | .a n => i ^ n.val
  | .xa n => j * i ^ n.val

def leftEmbedding : QuaternionGroup 2 →* core where
  toFun := quaternionMap leftI leftJ
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def rightEmbedding : QuaternionGroup 2 →* core where
  toFun := quaternionMap rightI rightJ
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def cyclicEmbedding : C4 →* core where
  toFun n := cyclicGenerator ^ n.toAdd.val
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

theorem leftEmbedding_injective : Function.Injective leftEmbedding := by decide +kernel
theorem rightEmbedding_injective : Function.Injective rightEmbedding := by decide +kernel
theorem cyclicEmbedding_injective : Function.Injective cyclicEmbedding := by decide +kernel

def leftFactor : Subgroup core := leftEmbedding.range
def rightFactor : Subgroup core := rightEmbedding.range
def quaternionPart : Subgroup core := leftFactor ⊔ rightFactor
def cyclicPart : Subgroup core := cyclicEmbedding.range
/-- The embedded subgroup whose coverage of the full pair kernel remains to be proved. -/
def embeddedCore : Subgroup core := quaternionPart ⊔ cyclicPart

theorem factors_commute : ∀ b ∈ leftFactor, ∀ c ∈ rightFactor, b * c = c * b := by
  have h : ∀ q r : QuaternionGroup 2,
      leftEmbedding q * rightEmbedding r = rightEmbedding r * leftEmbedding q := by
    decide +kernel
  rintro _ ⟨q, rfl⟩ _ ⟨r, rfl⟩
  exact h q r

theorem factors_intersection_mem (g : core) :
    g ∈ leftFactor ⊓ rightFactor ↔ g = 1 ∨ g = commonInvolution := by
  constructor
  · rintro ⟨⟨q, rfl⟩, ⟨r, hr⟩⟩
    have h : ∀ q r : QuaternionGroup 2, rightEmbedding r = leftEmbedding q →
        leftEmbedding q = 1 ∨ leftEmbedding q = commonInvolution := by decide +kernel
    exact h q r hr
  · rintro (rfl | rfl)
    · exact ⟨leftFactor.one_mem, rightFactor.one_mem⟩
    · exact ⟨⟨QuaternionGroup.a 2, by decide +kernel⟩,
        ⟨QuaternionGroup.a 2, by decide +kernel⟩⟩

theorem factors_intersection_card : Nat.card (leftFactor ⊓ rightFactor : Subgroup core) = 2 := by
  have he : (↑(leftFactor ⊓ rightFactor) : Set core) = {1, commonInvolution} := by
    ext g
    exact (factors_intersection_mem g).trans (by simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff])
  rw [← SetLike.coe_sort_coe, he, Nat.card_coe_set_eq]
  apply Set.ncard_pair
  decide +kernel

noncomputable def quaternionPartData : QuaternionCentralProductData quaternionPart where
  left := leftFactor.subgroupOf quaternionPart
  right := rightFactor.subgroupOf quaternionPart
  left_model := ⟨(subgroupOfEquivOfLe (show leftFactor ≤ quaternionPart from le_sup_left)).trans
    (MonoidHom.ofInjective leftEmbedding_injective).symm⟩
  right_model := ⟨(subgroupOfEquivOfLe (show rightFactor ≤ quaternionPart from le_sup_right)).trans
    (MonoidHom.ofInjective rightEmbedding_injective).symm⟩
  intersection_card := by
    change Nat.card ((leftFactor ⊓ rightFactor).subgroupOf quaternionPart) = 2
    rw [Nat.card_congr (subgroupOfEquivOfLe
      (show leftFactor ⊓ rightFactor ≤ quaternionPart from inf_le_left.trans le_sup_left)).toEquiv]
    exact factors_intersection_card
  commute := by
    intro b hb c hc
    exact Subtype.ext (factors_commute b.val hb c.val hc)
  span := by
    rw [← subgroupOf_sup (show leftFactor ≤ quaternionPart from le_sup_left)
      (show rightFactor ≤ quaternionPart from le_sup_right)]
    exact subgroupOf_self _

theorem mem_quaternionPart (g : core) :
    g ∈ quaternionPart ↔ ∃ q r : QuaternionGroup 2, leftEmbedding q * rightEmbedding r = g := by
  have hn : leftFactor ≤ normalizer (rightFactor : Set core) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro b hb c hc
    exact (factors_commute b hb c hc).symm
  change g ∈ (↑(leftFactor ⊔ rightFactor) : Set core) ↔ _
  rw [coe_mul_of_left_le_normalizer_right leftFactor rightFactor hn]
  constructor
  · rintro ⟨b, ⟨q, rfl⟩, c, ⟨r, rfl⟩, h⟩
    exact ⟨q, r, h⟩
  · rintro ⟨q, r, rfl⟩
    exact ⟨_, ⟨q, rfl⟩, _, ⟨r, rfl⟩, rfl⟩

theorem parts_commute : ∀ b ∈ quaternionPart, ∀ c ∈ cyclicPart, b * c = c * b := by
  have h : ∀ q r : QuaternionGroup 2, ∀ n : C4,
      (leftEmbedding q * rightEmbedding r) * cyclicEmbedding n =
        cyclicEmbedding n * (leftEmbedding q * rightEmbedding r) := by decide +kernel
  intro b hb c hc
  obtain ⟨q, r, rfl⟩ := (mem_quaternionPart b).mp hb
  obtain ⟨n, rfl⟩ := hc
  exact h q r n

theorem parts_intersection_mem (g : core) :
    g ∈ quaternionPart ⊓ cyclicPart ↔ g = 1 ∨ g = commonInvolution := by
  constructor
  · rintro ⟨hb, n, hn⟩
    obtain ⟨q, r, rfl⟩ := (mem_quaternionPart g).mp hb
    have h : ∀ q r : QuaternionGroup 2, ∀ n : C4,
        cyclicEmbedding n = leftEmbedding q * rightEmbedding r →
        leftEmbedding q * rightEmbedding r = 1 ∨
          leftEmbedding q * rightEmbedding r = commonInvolution := by decide +kernel
    exact h q r n hn
  · rintro (rfl | rfl)
    · exact ⟨quaternionPart.one_mem, cyclicPart.one_mem⟩
    · exact ⟨(show leftFactor ≤ quaternionPart from le_sup_left)
        ((factors_intersection_mem _).mpr (Or.inr rfl)).1,
        ⟨Multiplicative.ofAdd (2 : ZMod 4), by decide +kernel⟩⟩

theorem parts_intersection_card : Nat.card (quaternionPart ⊓ cyclicPart : Subgroup core) = 2 := by
  have he : (↑(quaternionPart ⊓ cyclicPart) : Set core) = {1, commonInvolution} := by
    ext g
    exact (parts_intersection_mem g).trans (by simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff])
  rw [← SetLike.coe_sort_coe, he, Nat.card_coe_set_eq]
  apply Set.ncard_pair
  decide +kernel

/-- Actual embedded factors in the explicit subgroup, including both intersections. -/
theorem embeddedCore_shape : IsQuaternionSquareCyclicFourProduct embeddedCore := by
  refine ⟨quaternionPart.subgroupOf embeddedCore, cyclicPart.subgroupOf embeddedCore,
    ⟨quaternionTransport (subgroupOfEquivOfLe (show quaternionPart ≤ embeddedCore from
      le_sup_left)).symm quaternionPartData⟩,
    ⟨(subgroupOfEquivOfLe (show cyclicPart ≤ embeddedCore from le_sup_right)).trans
      (MonoidHom.ofInjective cyclicEmbedding_injective).symm⟩, ?_, ?_, ?_⟩
  · change Nat.card ((quaternionPart ⊓ cyclicPart).subgroupOf embeddedCore) = 2
    rw [Nat.card_congr (subgroupOfEquivOfLe
      (show quaternionPart ⊓ cyclicPart ≤ embeddedCore from
        inf_le_left.trans le_sup_left)).toEquiv]
    exact parts_intersection_card
  · intro b hb c hc
    exact Subtype.ext (parts_commute b.val hb c.val hc)
  · rw [← subgroupOf_sup (show quaternionPart ≤ embeddedCore from le_sup_left)
      (show cyclicPart ≤ embeddedCore from le_sup_right)]
    exact subgroupOf_self _

theorem embeddedCore_card : Nat.card embeddedCore = 64 := shape_card embeddedCore_shape

theorem core_card_ge : 64 ≤ Nat.card core := by
  rw [← embeddedCore_card]
  exact card_le_card_group embeddedCore

/-- An upper bound on the full pair kernel suffices once the embedded factors are constructed. -/
theorem core_shape_of_card_le (h : Nat.card core ≤ 64) :
    IsQuaternionSquareCyclicFourProduct core := by
  have he : embeddedCore = ⊤ := by
    apply eq_of_le_of_card_ge le_top
    simpa only [Nat.card_congr (topEquiv : (⊤ : Subgroup core) ≃* core).toEquiv,
      embeddedCore_card] using h
  exact shape_transport ((MulEquiv.subgroupCongr he).trans topEquiv) embeddedCore_shape

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure
