module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.Field.ZMod

/-!
# Linear groups regular on nonzero vectors

A regular linear action sends each nonzero vector to any other by a unique
group element. Evaluation therefore identifies the actor with the nonzero
vectors. Transitivity makes every invariant subspace zero or the whole space;
for an abelian actor it also identifies the full linear centralizer with the
actor itself. Over F₂, every linear automorphism in dimension at most one is
the identity.

These are the elementary Singer-action inputs in Aschbacher–Smith,
*The Classification of Quasithin Groups*, A.1.12, printed p.22.
No normalization by an overgroup is built into the definition.
-/

namespace LinearGroup

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Freeness and transitivity of the actual linear action on nonzero vectors. -/
@[expose] public def IsRegularOnNonzero (X : Subgroup (V ≃ₗ[K] V)) : Prop :=
  ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃! x : X, (x : V ≃ₗ[K] V) v = w

/-- Only the identity actor fixes a nonzero vector. -/
public theorem IsRegularOnNonzero.eq_one_of_apply_eq_self
    {X : Subgroup (V ≃ₗ[K] V)} (hX : IsRegularOnNonzero X)
    (x : X) {v : V} (hv : v ≠ 0) (hx : (x : V ≃ₗ[K] V) v = v) : x = 1 := by
  obtain ⟨a, _, ha⟩ := hX v v hv hv
  exact (ha x hx).trans (ha 1 rfl).symm

/-- A regular actor has as many elements as there are nonzero vectors. -/
public theorem IsRegularOnNonzero.card_eq [Finite V] [Nontrivial V]
    {X : Subgroup (V ≃ₗ[K] V)} (hX : IsRegularOnNonzero X) :
    Nat.card X = Nat.card V - 1 := by
  classical
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let f : X → {w : V // w ≠ 0} := fun x =>
    ⟨(x : V ≃ₗ[K] V) v, fun he => hv ((x : V ≃ₗ[K] V).injective (he.trans (map_zero _).symm))⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y he
      have hx : (x : V ≃ₗ[K] V) v = (y : V ≃ₗ[K] V) v := congrArg Subtype.val he
      obtain ⟨a, _, ha⟩ := hX v ((y : V ≃ₗ[K] V) v) hv (f y).property
      exact (ha x hx).trans (ha y rfl).symm
    · intro w
      obtain ⟨x, hx, _⟩ := hX v w.val hv w.property
      exact ⟨x, Subtype.ext hx⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf)]
  let : Fintype V := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  simp [Nat.card_eq_fintype_card]

/-- A regular actor has as many elements as there are nonzero vectors. -/
public theorem IsRegularOnNonzero.card_eq_pow_finrank_sub_one [Finite K]
    [FiniteDimensional K V] [Nontrivial V]
    {X : Subgroup (V ≃ₗ[K] V)} (hX : IsRegularOnNonzero X) :
    Nat.card X = Nat.card K ^ Module.finrank K V - 1 := by
  let : Finite V := Module.finite_of_finite K
  rw [hX.card_eq, Module.natCard_eq_pow_finrank (K := K)]

/-- An abelian regular linear group is its own centralizer in the full linear group. -/
public theorem IsRegularOnNonzero.centralizer_eq [Nontrivial V]
    {X : Subgroup (V ≃ₗ[K] V)} [IsMulCommutative X]
    (hX : IsRegularOnNonzero X) : Subgroup.centralizer (X : Set (V ≃ₗ[K] V)) = X := by
  open scoped IsMulCommutative in
  apply le_antisymm
  · intro g hg
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hgv : g v ≠ 0 := fun he => hv (g.injective (he.trans (map_zero _).symm))
    obtain ⟨x, hx, _⟩ := hX v (g v) hv hgv
    have hgx : g = (x : V ≃ₗ[K] V) := by
      ext w
      by_cases hw : w = 0
      · simp [hw]
      obtain ⟨y, hy, _⟩ := hX v w hv hw
      have hgy := Subgroup.mem_centralizer_iff.mp hg (y : V ≃ₗ[K] V) y.property
      have hxy : (y : V ≃ₗ[K] V) * x = (x : V ≃ₗ[K] V) * y :=
        congrArg Subtype.val (mul_comm y x)
      calc
        g w = g ((y : V ≃ₗ[K] V) v) := by rw [hy]
        _ = (y : V ≃ₗ[K] V) (g v) := (LinearEquiv.congr_fun hgy v).symm
        _ = (y : V ≃ₗ[K] V) ((x : V ≃ₗ[K] V) v) := by rw [hx]
        _ = (x : V ≃ₗ[K] V) ((y : V ≃ₗ[K] V) v) := LinearEquiv.congr_fun hxy v
        _ = (x : V ≃ₗ[K] V) w := by rw [hy]
    exact hgx ▸ x.property
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (mul_comm (⟨y, hy⟩ : X) (⟨x, hx⟩ : X))

/-- Regularity on nonzero vectors implies irreducibility of the linear action. -/
public theorem IsRegularOnNonzero.invariant_eq_bot_or_top
    {X : Subgroup (V ≃ₗ[K] V)} (hX : IsRegularOnNonzero X)
    (W : Submodule K V)
    (hW : ∀ (x : X) (v : V), v ∈ W → (x : V ≃ₗ[K] V) v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hb : W = ⊥
  · exact Or.inl hb
  right
  apply eq_top_iff.mpr
  intro w _
  by_cases hw : w = 0
  · exact hw ▸ W.zero_mem
  have hv : ∃ v : V, v ∈ W ∧ v ≠ 0 := by
    by_contra! h
    apply hb
    exact eq_bot_iff.mpr (fun v hv => (Submodule.mem_bot K).mpr (h v hv))
  obtain ⟨v, hvW, hv⟩ := hv
  obtain ⟨x, hx, _⟩ := hX v w hv hw
  exact hx ▸ hW x v hvW

end LinearGroup

namespace LinearGroup

/-- Every binary linear automorphism in dimension zero or one is the identity. -/
public theorem eq_one_of_binary_finrank_le_one
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (hn : Module.finrank (ZMod 2) V ≤ 1) (g : V ≃ₗ[ZMod 2] V) : g = 1 := by
  classical
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Fintype V := Fintype.ofFinite V
  have hc : Nat.card V ≤ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) hn).trans_eq (by simp)
  have hnonzero : Nat.card {v : V // v ≠ 0} ≤ 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    have hc' : Fintype.card V ≤ 2 := by simpa [Nat.card_eq_fintype_card] using hc
    simpa using Nat.sub_le_sub_right hc' 1
  let : Subsingleton {v : V // v ≠ 0} := Finite.card_le_one_iff_subsingleton.mp hnonzero
  ext v
  by_cases hv : v = 0
  · simp [hv]
  have hgv : g v ≠ 0 := fun he => hv (g.injective (he.trans (map_zero _).symm))
  exact congrArg Subtype.val (Subsingleton.elim (⟨g v, hgv⟩ : {v : V // v ≠ 0}) ⟨v, hv⟩)

/-- All binary linear subgroups normalize one another in dimension at most one. -/
public theorem le_normalizer_of_binary_finrank_le_one
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (hn : Module.finrank (ZMod 2) V ≤ 1)
    (X Y : Subgroup (V ≃ₗ[ZMod 2] V)) : Y ≤ Subgroup.normalizer (X : Set (V ≃ₗ[ZMod 2] V)) := by
  intro g _
  rw [eq_one_of_binary_finrank_le_one hn g]
  exact (Subgroup.normalizer (X : Set (V ≃ₗ[ZMod 2] V))).one_mem

end LinearGroup
