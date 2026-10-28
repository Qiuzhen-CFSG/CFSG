module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Loewy.Canonical
public import Mathlib.LinearAlgebra.StdBasis

/-!
# Span semantics for packed native displacement certificates

Bitwise row combinations decode as linear combinations over the binary field.
Reversible row combinations certify equality of subspaces. The actual native
eight-generator theorem then identifies a checked displacement span with the
next canonical layer, preserving the original 112-dimensional row convention.
These are the finite-calculation interfaces for KW (1988), Corollary 2.3.6.
-/

@[expose] public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry.Loewy
open Subgroup Matrix GeneratorCertificates
open scoped Matrix
attribute [local irreducible] modelGroup matrixA matrixB

def combine {n : ℕ} (r : Vector ℕ n) (m : ℕ) : ℕ :=
  xorList (List.ofFn (fun i : Fin n => if m.testBit i.val then r.get i else 0))

def decode (m : ℕ) : V := fun j => bit m j.val

theorem packedOne_get (i : Fin 112) : packedOne.get i = 2^i.val := by
  rw [GeneratorCertificates.packedOne, GeneratorCertificates.get_ofFn]

theorem packedRow_pow (r : Vector ℕ 112) (i : Fin 112) :
    packedRow (2^i.val) r = r.get i := by
  apply Nat.eq_of_testBit_eq
  intro j
  have h : bit (packedRow (2^i.val) r) j = bit (r.get i) j := by
    rw [packedRow, bit_xorList, List.map_ofFn, List.sum_ofFn]
    simp only [Nat.testBit_two_pow, decide_eq_true_eq, ← Fin.ext_iff]
    calc
      ∑ x : Fin 112, bit (if i = x then r.get x else 0) j =
          ∑ x : Fin 112, if i = x then bit (r.get x) j else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hix : i = x <;> simp [hix, bit]
      _ = bit (r.get i) j := by simp
  cases ha : (packedRow (2^i.val) r).testBit j <;>
    cases hb : (r.get i).testBit j <;> simp_all [bit]

theorem decode_xor (m n : ℕ) : decode (m ^^^ n) = decode m + decode n := by
  funext j
  exact bit_xor m n j.val

theorem decode_combine {n : ℕ} (r : Vector ℕ n) (m : ℕ) :
    decode (combine r m) = ∑ i : Fin n, bit m i.val • decode (r.get i) := by
  funext j
  simp only [decode,combine,bit_xorList,List.map_ofFn,List.sum_ofFn,Finset.sum_apply,
    Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [bit]
  cases hm : m.testBit i.val <;> simp [hm]

def rowSpan {n : ℕ} (r : Vector ℕ n) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) (Set.range (fun i : Fin n => decode (r.get i)))

theorem decode_combine_mem {n : ℕ} (r : Vector ℕ n) (m : ℕ) :
    decode (combine r m) ∈ rowSpan r := by
  rw [decode_combine]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self i)))

theorem rowSpan_le_of_combine {n k : ℕ} (r : Vector ℕ n) (s : Vector ℕ k)
    (c : Fin n → ℕ) (hc : ∀ i, r.get i = combine s (c i)) : rowSpan r ≤ rowSpan s := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  change decode (r.get i) ∈ rowSpan s
  rw [hc]
  exact decode_combine_mem s _

theorem decode_packedRow (m : ℕ) (r : Vector ℕ 112) :
    decode (packedRow m r) = decode m ᵥ* decodeRows r := by
  funext j
  change bit (packedRow m r) j.val = _
  rw [packedRow,bit_xorList,List.map_ofFn,List.sum_ofFn]
  change _ = ∑ i : Fin 112, bit m i.val * bit (r.get i) j.val
  apply Finset.sum_congr rfl
  intro i _
  simp only [bit]
  cases hm : m.testBit i.val <;> simp [hm]

theorem displacement_decode (x : Model) (r : Vector ℕ 112)
    (hx : toMatrix x = decodeRows r) (m : ℕ) :
    displacement x (decode m) = decode (packedRow m r ^^^ m) := by
  rw [displacement_apply,rowAction_apply,hx,decode_xor,decode_packedRow]
  exact sub_eq_add_neg _ _ |>.trans (by congr 1; ext j; exact CharTwo.neg_eq _)

theorem rowSpan_one : rowSpan packedOne = ⊤ := by
  have hd (i : Fin 112) : decode (packedOne.get i) = Pi.single i 1 := by
    funext j
    simp only [decode,packedOne,get_ofFn,bit,Nat.testBit_two_pow,decide_eq_true_eq]
    simp only [Pi.single_apply,Fin.ext_iff, eq_comm]
  have hb := (Pi.basisFun (ZMod 2) (Fin 112)).span_eq
  change Submodule.span (ZMod 2) (Set.range (fun i : Fin 112 => decode (packedOne.get i))) = ⊤
  have he : (fun i : Fin 112 => decode (packedOne.get i)) = Pi.basisFun (ZMod 2) (Fin 112) := by
    funext i
    rw [hd,Pi.basisFun_apply]
  rw [he]
  exact hb

/-- Images of a spanning family span the literal displacement image. -/
theorem movedBy_rows {n : ℕ} (k : ℕ) (r : Vector ℕ n)
    (hr : layer (nativeEight 0) k = rowSpan r) (x : Model) :
    movedBy (nativeEight 0) k x = Submodule.span (ZMod 2)
      (Set.range (fun i : Fin n => displacement x (decode (r.get i)))) := by
  rw [movedBy,hr,rowSpan,Submodule.map_span,← Set.range_comp]
  rfl

/-- Computing displacement on the displayed spanning rows computes the next
canonical layer, using all eight certified native generators. -/
theorem next_layer_rows {n : ℕ} (k : ℕ) (r : Vector ℕ n)
    (hr : layer (nativeEight 0) k = rowSpan r) :
    layer (nativeEight 0) (k+1) = Submodule.span (ZMod 2)
      (Set.range (fun p : Fin n × Fin 8 => displacement (nativeGenerator p.2) (decode (r.get p.1)))) := by
  rw [native_layer_succ,hr]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨j,v,hv,rfl⟩
    apply Submodule.span_induction (p := fun v _ => displacement (nativeGenerator j) v ∈
      Submodule.span (ZMod 2) (Set.range (fun p : Fin n × Fin 8 =>
        displacement (nativeGenerator p.2) (decode (r.get p.1))))) _ _ _ _ hv
    · rintro _ ⟨i,rfl⟩
      exact Submodule.subset_span (Set.mem_range_self (i,j))
    · simp only [map_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb
      simpa only [map_add] using Submodule.add_mem _ ha hb
    · intro a b _ hb
      simpa only [map_smul] using Submodule.smul_mem _ a hb
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨i,j⟩,rfl⟩
    exact Submodule.subset_span ⟨j,decode (r.get i),Submodule.subset_span (Set.mem_range_self i),rfl⟩

end Janko4.LocalStructure.ElementaryEightGeometry.Loewy
