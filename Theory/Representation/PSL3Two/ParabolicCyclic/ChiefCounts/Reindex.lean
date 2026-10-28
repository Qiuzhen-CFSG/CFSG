module

public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts.Flags

/-!
# Chief flags under a surjective change of actor

Pullback along a surjective homomorphism has exactly the same invariant
subspaces and central sections. This retains the literal action map when a
source section is identified with a module for the embedded parabolic residual.
It also permits transport from a conjugate or dual parabolic marking.

Source application: the actor transport in Aschbacher–Smith 14.7.22(2), 14.7.72.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Representation
namespace BinaryLinearThree.ParabolicCyclic.ChiefCounts
variable {G H M : Type*} [Group G] [Group H]
  [AddCommGroup M] [Module (ZMod 2) M]
  (ρ : Representation (ZMod 2) G M) (f : H →* G) (hf : Function.Surjective f)

/-- Surjectivity identifies the actual invariant-subspace lattices. -/
def reindexOrderIso : Subrepresentation ρ ≃o Subrepresentation (ρ.comp f) where
  toFun U := ⟨U.toSubmodule, fun h _ hv => U.apply_mem_toSubmodule (f h) hv⟩
  invFun V := ⟨V.toSubmodule, fun g v hv => by
    obtain ⟨h, rfl⟩ := hf g
    exact V.apply_mem_toSubmodule h hv⟩
  left_inv U := rfl
  right_inv V := rfl
  map_rel_iff' := Iff.rfl

theorem central_reindex (U V : Subrepresentation ρ) :
    Central (reindexOrderIso ρ f hf U) (reindexOrderIso ρ f hf V) ↔ Central U V := by
  constructor
  · intro h g v hv
    obtain ⟨a, rfl⟩ := hf g
    exact h a v hv
  · intro h a v hv
    exact h (f a) v hv

variable {ρ}
/-- The same subspaces, with the actor pulled back by the specified homomorphism. -/
def Series.reindex (s : Series ρ) : Series (ρ.comp f) :=
  ⟨s.length, fun i => reindexOrderIso ρ f hf (s i),
    fun i => (apply_covBy_apply_iff (reindexOrderIso ρ f hf)).mpr (s.step i)⟩

theorem Series.count_reindex (s : Series ρ) : (s.reindex f hf).count = s.count := by
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun i => not_congr (central_reindex ρ f hf _ _)

include hf in
/-- Counts are preserved under the literal surjective source action map. -/
theorem HasCount.reindex {n : ℕ} (h : HasCount ρ n) : HasCount (ρ.comp f) n := by
  obtain ⟨s, h0, h1, hn⟩ := h
  refine ⟨s.reindex f hf, ?_, ?_, (s.count_reindex f hf).trans hn⟩
  · change reindexOrderIso ρ f hf s.head = ⊥
    rw [h0, OrderIso.map_bot]
  · change reindexOrderIso ρ f hf s.last = ⊤
    rw [h1, OrderIso.map_top]

end BinaryLinearThree.ParabolicCyclic.ChiefCounts
