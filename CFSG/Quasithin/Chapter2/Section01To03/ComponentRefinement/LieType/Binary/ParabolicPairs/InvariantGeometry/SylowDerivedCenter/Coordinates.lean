module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.ParabolicPairs.InvariantGeometry.MiddleRadical

/-!
# Coordinate spaces for the binary degree-five derived center

The standard coordinate prefixes of dimensions two and three form a flag.
Their radical intersection consists exactly of matrices differing from the
identity in the four positions (0,3), (0,4), (1,3), and (1,4). This equivalence
uses the actual SL₅(2) action: the intersection fixes the three-space pointwise
and has displacement in the two-space.

These are the coordinate and geometric interfaces for the Sylow calculation
used in Aschbacher–Smith 2.3.9(7), printed pp.525–526. The convention allowing
flag stabilizers as invariant parabolics is on printed p.216. The Sylow and
commutator calculations are separate obligations.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
open Subgroup

/-- The first `k` standard coordinate directions in binary five-space. -/
def fivePrefix (k : ℕ) : Space 5 where
  carrier := {v | ∀ i : Fin 5, k ≤ i.val → v i = 0}
  zero_mem' := by simp
  add_mem' := by intro v w hv hw i hi; simp [hv i hi, hw i hi]
  smul_mem' := by intro c v hv i hi; simp [hv i hi]

theorem fivePrefix_mono {k l : ℕ} (h : k ≤ l) : fivePrefix k ≤ fivePrefix l :=
  fun _ hv i hi => hv i (h.trans hi)

private def fivePrefixEquiv (k : ℕ) (hk : k ≤ 5) :
    fivePrefix k ≃ₗ[ZMod 2] (Fin k → ZMod 2) where
  toFun v i := v.val ⟨i.val, lt_of_lt_of_le i.isLt hk⟩
  invFun v := ⟨fun i => if h : i.val < k then v ⟨i.val, h⟩ else 0,
    fun i hi => dif_neg (not_lt.mpr hi)⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    dsimp
    split_ifs with hi
    · rfl
    · exact (v.property i (Nat.le_of_not_gt hi)).symm
  right_inv v := by funext i; simp
  map_add' v w := rfl
  map_smul' c v := rfl

theorem fivePrefix_finrank (k : ℕ) (hk : k ≤ 5) :
    Module.finrank (ZMod 2) (fivePrefix k) = k := by
  rw [(fivePrefixEquiv k hk).finrank_eq, Module.finrank_fin_fun]

theorem single_mem_fivePrefix {j : Fin 5} {k : ℕ} (hj : j.val < k) :
    Pi.single j (1 : ZMod 2) ∈ fivePrefix k := by
  intro i hi
  have hij : i ≠ j := by intro h; subst i; omega
  simp [hij]

private theorem mem_radical_inf_iff {W U : Space 5} (hWU : W ≤ U)
    (g : BinaryLinear.GL (Vector 5)) :
    g ∈ BinaryLinear.radical W ⊓ BinaryLinear.radical U ↔
      (∀ v ∈ U, g v = v) ∧ ∀ v, g v - v ∈ W := by
  constructor
  · exact fun h => ⟨h.2.1, h.1.2⟩
  · rintro ⟨hfix, hdisp⟩
    exact ⟨⟨fun v hv => hfix v (hWU hv), hdisp⟩,
      ⟨hfix, fun v => hWU (hdisp v)⟩⟩

/-- Matrices differing from the identity only at `(0,3)`, `(0,4)`, `(1,3)`, `(1,4)`. -/
def FiveRectangle (A : SL 5) : Prop :=
  ∀ i j : Fin 5, 2 ≤ i.val ∨ j.val < 3 →
    A.val i j = (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) i j

/-- The four-entry rectangle is precisely `Hom(V/W₃,W₂)` in the actual matrix action. -/
theorem fiveRectangle_iff_radical (A : SL 5) :
    FiveRectangle A ↔ slEquivLinear 5 A ∈
      BinaryLinear.radical (fivePrefix 2) ⊓ BinaryLinear.radical (fivePrefix 3) := by
  rw [mem_radical_inf_iff (fivePrefix_mono (by decide : 2 ≤ 3))]
  constructor
  · intro hA
    have hrow (i : Fin 5) (hi : 2 ≤ i.val) (v : Vector 5) :
        Matrix.mulVec A.val v i = v i := by
      calc
        _ = Matrix.mulVec (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) v i := by
          simp only [Matrix.mulVec, dotProduct]
          apply Finset.sum_congr rfl
          intro j _
          rw [hA i j (Or.inl hi)]
        _ = _ := congrFun (Matrix.one_mulVec v) i
    constructor
    · intro v hv
      rw [slEquivLinear_apply]
      calc
        _ = Matrix.mulVec (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) v := by
          funext i
          simp only [Matrix.mulVec, dotProduct]
          apply Finset.sum_congr rfl
          intro j _
          by_cases hj : j.val < 3
          · rw [hA i j (Or.inr hj)]
          · rw [hv j (Nat.le_of_not_gt hj)]
            simp
        _ = _ := Matrix.one_mulVec v
    · intro v i hi
      change Matrix.mulVec A.val v i - v i = 0
      rw [hrow i hi, sub_self]
  · rintro ⟨hfix, hdisp⟩ i j (hi | hj)
    · have h := hdisp (Pi.single j 1) i hi
      have h' : (slEquivLinear 5 A (Pi.single j 1)) i = (Pi.single j 1 : Vector 5) i :=
        sub_eq_zero.mp h
      simpa [slEquivLinear_apply, Matrix.mulVec_single_one, Pi.single_apply,
        Matrix.one_apply, eq_comm] using h'
    · have h := congrFun (hfix (Pi.single j 1) (single_mem_fivePrefix hj)) i
      simpa [slEquivLinear_apply, Matrix.mulVec_single_one, Pi.single_apply,
        Matrix.one_apply, eq_comm] using h

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary

end
