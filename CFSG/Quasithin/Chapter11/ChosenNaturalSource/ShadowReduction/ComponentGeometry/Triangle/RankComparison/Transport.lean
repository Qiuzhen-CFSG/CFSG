module
public import Theory.Representation.BinaryGroupAction
public import Theory.Representation.BinaryOffender.EmbeddedFixedIndex
public import CFSG.Quasithin.ChapterE.Section03.Parameters.AutomizerFF

/-!
# Literal subgroup transport for the mutual-action comparison

An injective marking of a binary module transports its moved space to the
ambient subgroup commutator and its fixed space to the relative centralizer.
For a faithful model action, its kernel is the original centralizer kernel,
so its image has the rank of the literal induced automizer.

Source application: Aschbacher--Smith, 11.4.1(2), printed p.776.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.RankComparison
variable {G K W : Type*} [Group G] [Group K] [AddCommGroup W] [Module (ZMod 2) W]

/-- A marked binary subspace, with its literal embedding in the ambient group. -/
def embeddedSpace (j : Multiplicative W →* G) (P : Submodule (ZMod 2) W) : Subgroup G :=
  (BinaryGroupAction.submoduleEquivSubgroup P).map j

/-- The embedded moved space is the original subgroup commutator. -/
theorem embedded_moved (σ : Representation (ZMod 2) K W)
    (U A : Subgroup G) (j : Multiplicative W →* G) (hjr : j.range = U) (β : A →* K)
    (hact : ∀ (a : A) (v : W), j (Multiplicative.ofAdd (σ (β a) v)) =
      a.val * j (Multiplicative.ofAdd v) * a.val⁻¹) :
    embeddedSpace j (subspaceCommutator σ ⊤ β.range) = ⁅U,A⁆ := by
  let P := subspaceCommutator σ ⊤ β.range
  let C : Submodule (ZMod 2) W := BinaryGroupAction.submoduleEquivSubgroup.symm
    ((⁅U,A⁆ : Subgroup G).comap j)
  have hP : P ≤ C := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, ⟨a,rfl⟩, v, _, rfl⟩
    change j (Multiplicative.ofAdd (σ (β a) v - v)) ∈ ⁅U,A⁆
    have hv : j (Multiplicative.ofAdd v) ∈ U := hjr ▸ ⟨_,rfl⟩
    have he : j (Multiplicative.ofAdd (σ (β a) v - v)) =
        ⁅a.val,j (Multiplicative.ofAdd v)⁆ := by
      rw [ofAdd_sub, map_div, hact]
      simp only [div_eq_mul_inv]
      rfl
    rw [he,commutator_comm]
    exact commutator_mem_commutator a.property hv
  apply le_antisymm
  · rintro _ ⟨v,hv,rfl⟩
    exact hP hv
  · rw [commutator_comm]
    apply commutator_le.mpr
    intro a ha u hu
    obtain ⟨v,rfl⟩ := (hjr ▸ hu : u ∈ j.range)
    refine ⟨Multiplicative.ofAdd (σ (β ⟨a,ha⟩) v.toAdd - v.toAdd), ?_, ?_⟩
    · change σ (β ⟨a,ha⟩) v.toAdd - v.toAdd ∈ subspaceCommutator σ ⊤ β.range
      exact Submodule.subset_span ⟨_, ⟨⟨a,ha⟩,rfl⟩,v.toAdd,Submodule.mem_top,rfl⟩
    · rw [ofAdd_sub, map_div, hact]
      simp only [div_eq_mul_inv]
      rfl

/-- The embedded fixed space is the relative centralizer of the same actor. -/
theorem embedded_fixed (σ : Representation (ZMod 2) K W)
    (U A : Subgroup G) (j : Multiplicative W →* G) (hj : Function.Injective j)
    (hjr : j.range = U) (β : A →* K)
    (hact : ∀ (a : A) (v : W), j (Multiplicative.ofAdd (σ (β a) v)) =
      a.val * j (Multiplicative.ofAdd v) * a.val⁻¹) :
    embeddedSpace j (fixedSpace σ β.range) = U ⊓ centralizer (A : Set G) := by
  ext u
  constructor
  · rintro ⟨v,hv,rfl⟩
    refine ⟨hjr ▸ ⟨v,rfl⟩,?_⟩
    intro a ha
    have hh := hact ⟨a,ha⟩ v.toAdd
    have hf := hv ⟨β ⟨a,ha⟩,⟨⟨a,ha⟩,rfl⟩⟩
    change σ (β ⟨a,ha⟩) v.toAdd = v.toAdd at hf
    rw [hf] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh.symm
  · rintro ⟨hu,hc⟩
    obtain ⟨v,rfl⟩ := (hjr ▸ hu : u ∈ j.range)
    refine ⟨v,?_,rfl⟩
    rintro ⟨k,⟨a,rfl⟩⟩
    change σ (β a) v.toAdd = v.toAdd
    apply Multiplicative.ofAdd.injective
    apply hj
    rw [hact, ofAdd_toAdd, hc a.val a.property, mul_inv_cancel_right]

/-- Cardinality is retained by an injective marking of a binary subspace. -/
theorem embeddedSpace_card [FiniteDimensional (ZMod 2) W]
    (j : Multiplicative W →* G) (hj : Function.Injective j) (P : Submodule (ZMod 2) W) :
    Nat.card (embeddedSpace j P) = 2 ^ Module.finrank (ZMod 2) P := by
  rw [embeddedSpace, Subgroup.card_map_of_injective hj,
    BinaryGroupAction.card_submoduleEquivSubgroup,
    Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

/-- Faithful model coordinates identify the original centralizer kernel. -/
theorem marked_action_kernel (σ : Representation (ZMod 2) K W)
    (hσ : Function.Injective σ) (U A : Subgroup G)
    (j : Multiplicative W →* G) (hj : Function.Injective j) (hjr : j.range = U)
    (β : A →* K)
    (hact : ∀ (a : A) (v : W), j (Multiplicative.ofAdd (σ (β a) v)) =
      a.val * j (Multiplicative.ofAdd v) * a.val⁻¹) :
    β.ker = (centralizer (U : Set G)).subgroupOf A := by
  ext a
  constructor
  · intro ha u hu
    obtain ⟨v,rfl⟩ := (hjr ▸ hu : u ∈ j.range)
    have hh := hact a v.toAdd
    change β a = 1 at ha
    rw [ha,map_one,Module.End.one_apply] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  · intro ha
    change β a = 1
    apply hσ
    ext v
    simp only [map_one, Module.End.one_apply]
    apply Multiplicative.ofAdd.injective
    apply hj
    have hv : j (Multiplicative.ofAdd v) ∈ U := hjr ▸ ⟨_,rfl⟩
    have hh : j (Multiplicative.ofAdd v) * a.val = a.val * j (Multiplicative.ofAdd v) := ha _ hv
    rw [hact, ← hh, mul_inv_cancel_right]

/-- The model actor has exactly the order of the literal induced automizer. -/
theorem marked_action_rank (σ : Representation (ZMod 2) K W)
    (hσ : Function.Injective σ) (U A : Subgroup G)
    (hn : A ≤ normalizer (U : Set G))
    (j : Multiplicative W →* G) (hj : Function.Injective j) (hjr : j.range = U)
    (β : A →* K)
    (hact : ∀ (a : A) (v : W), j (Multiplicative.ofAdd (σ (β a) v)) =
      a.val * j (Multiplicative.ofAdd v) * a.val⁻¹) :
    rank β.range = rank (ChapterE.inducedAutomizer U A) := by
  rw [ChapterE.rank_inducedAutomizer U A hn]
  unfold rank ChapterE.subgroupCorank
  rw [← Subgroup.index_ker,marked_action_kernel σ hσ U A j hj hjr β hact,
    inf_relIndex_left]
  rfl
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.RankComparison
