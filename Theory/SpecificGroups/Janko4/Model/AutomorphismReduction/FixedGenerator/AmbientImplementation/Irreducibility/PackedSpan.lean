module

public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates.Packed

/-! Packed row-action and spanning certificates for the 112-dimensional binary space. -/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.IrreducibilityCertificate
open GeneratorCertificates Matrix

abbrev Vec := Fin 112 → ZMod 2

def vector (x : ℕ) : Vec := fun i => bit x i.val

theorem vector_packedRow (x : ℕ) (ys : Vector ℕ 112) :
    vector (packedRow x ys) = vecMul (vector x) (decodeRows ys) := by
  funext j
  change bit (packedRow x ys) j.val = ∑ k : Fin 112, vector x k * decodeRows ys k j
  rw [packedRow, bit_xorList, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro k _
  simp only [vector, decodeRows, bit]
  cases h : x.testBit k.val <;> simp [h]

theorem eq_top_of_rows (W : Submodule (ZMod 2) Vec)
    (rows inverse : Vector ℕ 112)
    (hinv : packedMul inverse rows = packedOne)
    (hrows : ∀ i : Fin 112, vector (rows.get i) ∈ W) : W = ⊤ := by
  have hm : decodeRows inverse * decodeRows rows = 1 := by
    rw [← decode_packedMul, hinv, decode_packedOne]
  apply top_unique
  intro v _
  have hv : vecMul (vecMul v (decodeRows inverse)) (decodeRows rows) ∈ W := by
    rw [vecMul_eq_sum]
    exact W.sum_mem fun i _ => W.smul_mem _ (hrows i)
  simpa only [vecMul_vecMul, hm, vecMul_one] using hv

/-- Each row is the seed or the image of an earlier row under one generator. -/
def OrbitSteps (rows : Vector ℕ 112) (parents : Vector (Fin 112 × Bool) 112)
    (a b : Vector ℕ 112) : Prop :=
  ∀ i : Fin 112, i ≠ 0 →
    (parents.get i).1 < i ∧
    rows.get i = packedRow (rows.get (parents.get i).1)
      (if (parents.get i).2 then b else a)

instance (rows : Vector ℕ 112) (parents : Vector (Fin 112 × Bool) 112)
    (a b : Vector ℕ 112) : Decidable (OrbitSteps rows parents a b) :=
  inferInstanceAs (Decidable (∀ i : Fin 112, i ≠ 0 → _))

theorem orbit_mem (W : Submodule (ZMod 2) Vec)
    (rows : Vector ℕ 112) (parents : Vector (Fin 112 × Bool) 112)
    (a b : Vector ℕ 112) (hsteps : OrbitSteps rows parents a b)
    (ha : ∀ v ∈ W, vecMul v (decodeRows a) ∈ W)
    (hb : ∀ v ∈ W, vecMul v (decodeRows b) ∈ W)
    (hseed : vector (rows.get 0) ∈ W) :
    ∀ i : Fin 112, vector (rows.get i) ∈ W := by
  have aux : ∀ n : ℕ, ∀ hn : n < 112, vector (rows.get ⟨n, hn⟩) ∈ W := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hzero : n = 0
      · subst n; exact hseed
      · have hs := hsteps ⟨n, hn⟩ (by intro h; exact hzero (congrArg Fin.val h))
        rw [hs.2, vector_packedRow]
        have hp := ih (parents.get ⟨n, hn⟩).1.val hs.1 (parents.get ⟨n, hn⟩).1.isLt
        split <;> [exact hb _ hp; exact ha _ hp]
  intro i
  exact aux i.val i.isLt

end Janko4.OuterReduction.FixedGenerator.IrreducibilityCertificate
