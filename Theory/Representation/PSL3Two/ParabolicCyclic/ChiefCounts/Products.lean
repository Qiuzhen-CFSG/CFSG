module

public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts.Flags
public import Mathlib.LinearAlgebra.Prod

/-!+# Additivity of actual noncentral chief counts on direct sums

The first flag runs through U × 0; the second through M × V. The corresponding
intervals in the invariant-subspace lattice are order-isomorphic to those of
the original representations. Thus they give chief flags, with the same
central sections, and their concatenation adds the noncentral counts.

Source application: the two direct-sum alternatives of H.6.5 and 14.7.22(2).
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Representation
namespace BinaryLinearThree.ParabolicCyclic.ChiefCounts

variable {G M N : Type*} [Group G]
  [AddCommGroup M] [Module (ZMod 2) M]
  [AddCommGroup N] [Module (ZMod 2) N]
  {ρ : Representation (ZMod 2) G M} {σ : Representation (ZMod 2) G N}

def productNode (U : Subrepresentation ρ) (V : Subrepresentation σ) :
    Subrepresentation (ρ.prod σ) where
  toSubmodule := U.toSubmodule.prod V.toSubmodule
  apply_mem_toSubmodule g _ h :=
    ⟨U.apply_mem_toSubmodule g h.1, V.apply_mem_toSubmodule g h.2⟩

private def pullLeft (P : Subrepresentation (ρ.prod σ)) : Subrepresentation ρ where
  toSubmodule := P.toSubmodule.comap (LinearMap.inl (ZMod 2) M N)
  apply_mem_toSubmodule g v hv := by
    have h := P.apply_mem_toSubmodule g hv
    simpa using h

private def pullRight (P : Subrepresentation (ρ.prod σ)) : Subrepresentation σ where
  toSubmodule := P.toSubmodule.comap (LinearMap.inr (ZMod 2) M N)
  apply_mem_toSubmodule g v hv := by
    have h := P.apply_mem_toSubmodule g hv
    simpa using h

private def leftOrderIso : Subrepresentation ρ ≃o
    Set.Iic (productNode (⊤ : Subrepresentation ρ) (⊥ : Subrepresentation σ)) where
  toFun U := ⟨productNode U ⊥, fun _ h => ⟨Submodule.mem_top, h.2⟩⟩
  invFun P := pullLeft P.val
  left_inv U := by
    apply Subrepresentation.toSubmodule_injective
    ext v
    change (v ∈ U ∧ (0 : N) = 0) ↔ v ∈ U
    simp
  right_inv P := by
    apply Subtype.ext
    apply Subrepresentation.toSubmodule_injective
    ext v
    rcases v with ⟨x, y⟩
    change ((x, 0) ∈ P.val ∧ y = 0) ↔ (x, y) ∈ P.val
    constructor
    · rintro ⟨h, h0⟩
      simpa only [h0] using h
    · intro h
      have h0 : y = 0 := (P.property h).2
      exact ⟨by simpa only [h0] using h, h0⟩
  map_rel_iff' := by
    intro U V
    constructor
    · intro h v hv
      exact (h (show (v, 0) ∈ productNode U (⊥ : Subrepresentation σ) from ⟨hv, rfl⟩)).1
    · intro h v hv
      exact ⟨h hv.1, hv.2⟩

private def rightOrderIso : Subrepresentation σ ≃o
    Set.Ici (productNode (⊤ : Subrepresentation ρ) (⊥ : Subrepresentation σ)) where
  toFun V := ⟨productNode ⊤ V, fun v h => ⟨h.1, by
    have h0 : v.2 = 0 := h.2
    rw [h0]
    exact V.toSubmodule.zero_mem⟩⟩
  invFun P := pullRight P.val
  left_inv V := by
    apply Subrepresentation.toSubmodule_injective
    ext v
    change ((0 : M) ∈ (⊤ : Submodule (ZMod 2) M) ∧ v ∈ V) ↔ v ∈ V
    simp
  right_inv P := by
    apply Subtype.ext
    apply Subrepresentation.toSubmodule_injective
    ext v
    rcases v with ⟨x, y⟩
    change (x ∈ (⊤ : Submodule (ZMod 2) M) ∧ (0, y) ∈ P.val.toSubmodule) ↔
      (x, y) ∈ P.val.toSubmodule
    have hx : (x, 0) ∈ P.val.toSubmodule := P.property ⟨Submodule.mem_top, rfl⟩
    constructor
    · rintro ⟨_, hy⟩
      simpa using P.val.toSubmodule.add_mem hx hy
    · intro h
      exact ⟨Submodule.mem_top, by simpa using P.val.toSubmodule.sub_mem h hx⟩
  map_rel_iff' := by
    intro U V
    constructor
    · intro h v hv
      exact (h (show (0, v) ∈ productNode (⊤ : Subrepresentation ρ) U from
        ⟨Submodule.mem_top, hv⟩)).2
    · intro h v hv
      exact ⟨hv.1, h hv.2⟩

theorem productNode_covBy_left {U V : Subrepresentation ρ} (h : U ⋖ V) :
    productNode U (⊥ : Subrepresentation σ) ⋖ productNode V ⊥ := by
  have hc := (apply_covBy_apply_iff (leftOrderIso (σ := σ))).mpr h
  refine ⟨hc.lt, ?_⟩
  intro P hUP hPV
  exact hc.2 (c := ⟨P, hPV.le.trans (leftOrderIso V).property⟩) hUP hPV

theorem productNode_covBy_right {U V : Subrepresentation σ} (h : U ⋖ V) :
    productNode (⊤ : Subrepresentation ρ) U ⋖ productNode ⊤ V := by
  have hc := (apply_covBy_apply_iff (rightOrderIso (ρ := ρ))).mpr h
  refine ⟨hc.lt, ?_⟩
  intro P hUP hPV
  exact hc.2 (c := ⟨P, (rightOrderIso U).property.trans hUP.le⟩) hUP hPV

theorem central_productNode_left (U V : Subrepresentation ρ) :
    Central (productNode U (⊥ : Subrepresentation σ)) (productNode V ⊥) ↔
      Central U V := by
  constructor
  · intro h g v hv
    exact (h g (v, 0) ⟨hv, rfl⟩).1
  · intro h g v hv
    refine ⟨h g v.1 hv.1, ?_⟩
    have h0 : v.2 = 0 := hv.2
    change σ g v.2 - v.2 = 0
    simp [h0]

theorem central_productNode_right (U V : Subrepresentation σ) :
    Central (productNode (⊤ : Subrepresentation ρ) U) (productNode ⊤ V) ↔
      Central U V := by
  constructor
  · intro h g v hv
    exact (h g (0, v) ⟨Submodule.mem_top, hv⟩).2
  · intro h g v hv
    exact ⟨Submodule.mem_top, h g v.2 hv.2⟩

private def leftSeries (s : Series ρ) (σ : Representation (ZMod 2) G N) : Series (ρ.prod σ) :=
  ⟨s.length, fun i => productNode (s i) ⊥, fun i => productNode_covBy_left (s.step i)⟩

private def rightSeries (ρ : Representation (ZMod 2) G M) (s : Series σ) : Series (ρ.prod σ) :=
  ⟨s.length, fun i => productNode ⊤ (s i), fun i => productNode_covBy_right (s.step i)⟩

private theorem leftSeries_count (s : Series ρ) (σ : Representation (ZMod 2) G N) :
    (leftSeries s σ).count = s.count := by
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun i => not_congr (central_productNode_left _ _)

private theorem rightSeries_count (ρ : Representation (ZMod 2) G M) (s : Series σ) :
    (rightSeries ρ s).count = s.count := by
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun i => not_congr (central_productNode_right _ _)

/-- Direct sums add counts of actual chief factors, using a complete concatenated flag. -/
theorem HasCount.prod {a b : ℕ} (hρ : HasCount ρ a) (hσ : HasCount σ b) :
    HasCount (ρ.prod σ) (a + b) := by
  obtain ⟨s, hs0, hs1, hsc⟩ := hρ
  obtain ⟨t, ht0, ht1, htc⟩ := hσ
  have hst : (leftSeries s σ).last = (rightSeries ρ t).head := by
    change productNode s.last ⊥ = productNode ⊤ t.head
    rw [hs1, ht0]
  refine ⟨(leftSeries s σ).smash (rightSeries ρ t) hst, ?_, ?_, ?_⟩
  · rw [RelSeries.head_smash]
    change productNode s.head ⊥ = ⊥
    rw [hs0]
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.prod_bot
  · rw [RelSeries.last_smash]
    change productNode ⊤ t.last = ⊤
    rw [ht1]
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.prod_top
  · rw [Series.count_smash, leftSeries_count, rightSeries_count, hsc, htc]

end BinaryLinearThree.ParabolicCyclic.ChiefCounts
