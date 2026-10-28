module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.IncidenceTransport
public import Mathlib.Order.Fin.Basic

/-!
# Bitmask certificates for literal native trios

Support identifies a 24-bit mask with its actual point subset. Sorted triples
of masks are determined by their unordered support partitions. These lemmas
turn short checked mask equalities into the literal M₂₄ action and permit a
linear-size distinctness certificate for the trio table used in AS91 (3.8).
-/
@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.FarOrbit
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open scoped Pointwise

def support (a : BitVec 24) : Finset (Fin 24) :=
  Finset.univ.filter (fun i => a.getLsb i = true)

theorem support_injective : Function.Injective support := by
  intro a b hab
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hh := Finset.ext_iff.mp hab ⟨i,hi⟩
  simp only [support,Finset.mem_filter,Finset.mem_univ,true_and] at hh
  have hb : a.getLsb ⟨i,hi⟩ = b.getLsb ⟨i,hi⟩ := by simpa using hh
  rw [BitVec.getLsbD_eq_getElem hi, BitVec.getLsbD_eq_getElem hi]
  exact hb

theorem support_permute (g : Equiv.Perm (Fin 24)) (a : BitVec 24) :
    support (m24PermuteMask g a) = g • support a := by
  ext x
  rw [← Finset.inv_smul_mem_iff]
  simp [support,m24PermuteMask]

def maskParts (a : Fin 3 → BitVec 24) : Finset (BitVec 24) := {a 0,a 1,a 2}
def parts (a : Fin 3 → BitVec 24) : Finset (Finset (Fin 24)) := (maskParts a).image support

theorem parts_transport (g : M24) (a b : Fin 3 → BitVec 24)
    (he : (maskParts a).image (m24PermuteMask g.val) = maskParts b) :
    g • parts a = parts b := by
  simp only [parts]
  rw [←he,Finset.image_image]
  change ((maskParts a).image support).image (g • ·) = _
  rw [Finset.image_image]
  apply Finset.image_congr
  intro x _
  exact (support_permute g.val x).symm

theorem sorted_parts_injective (a b : Fin 3 → BitVec 24)
    (ha : (a 0).toNat < (a 1).toNat ∧ (a 1).toNat < (a 2).toNat)
    (hb : (b 0).toNat < (b 1).toNat ∧ (b 1).toNat < (b 2).toNat)
    (he : parts a = parts b) : a = b := by
  have he' : maskParts a = maskParts b := Finset.image_injective support_injective he
  have hm (j : Fin 3) : a j ∈ maskParts b := by
    rw [←he']
    fin_cases j <;> simp [maskParts]
  have hn (j : Fin 3) : b j ∈ maskParts a := by
    rw [he']
    fin_cases j <;> simp [maskParts]
  have h0 := hm 0
  have h1 := hm 1
  have h2 := hm 2
  have k0 := hn 0
  have k1 := hn 1
  have k2 := hn 2
  simp only [maskParts,Finset.mem_insert,Finset.mem_singleton] at h0 h1 h2 k0 k1 k2
  have va (i : Fin 3) := (a i).isLt
  have vb (i : Fin 3) := (b i).isLt
  have e0 : a 0 = b 0 := by
    rcases h0 with h0|h0|h0 <;> rcases k0 with k0|k0|k0 <;>
      first | exact h0 | exact k0.symm | (have := congrArg BitVec.toNat h0; have := congrArg BitVec.toNat k0; omega)
  have e2 : a 2 = b 2 := by
    rcases h2 with h2|h2|h2 <;> rcases k2 with k2|k2|k2 <;>
      first | exact h2 | exact k2.symm | (have := congrArg BitVec.toNat h2; have := congrArg BitVec.toNat k2; omega)
  have e1 : a 1 = b 1 := by
    rcases h1 with h1|h1|h1
    · have := congrArg BitVec.toNat h1; have := congrArg BitVec.toNat e0; omega
    · exact h1
    · have := congrArg BitVec.toNat h1; have := congrArg BitVec.toNat e2; omega
  funext i
  fin_cases i <;> assumption
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.FarOrbit
