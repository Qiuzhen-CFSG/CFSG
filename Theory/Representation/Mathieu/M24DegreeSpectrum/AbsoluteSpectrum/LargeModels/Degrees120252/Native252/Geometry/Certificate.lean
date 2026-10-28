module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252.Data
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.GraphInvariance.BitNetwork
/-!
# Packed certificates for the native sextet action

A checked bit-routing network implements the literal native point generators.
Sorting the six transformed masks changes only their order. Decoding therefore
commutes with the native action, and length-six rows decode to `pointParts`.
This connects the numerical checks in `Geometry.Forward` to actual partitions.

The generic routing semantics are reused from the Fi22 bit-network module;
no Fischer-group assertion is used. Sources: the native generators and sextet
conditions in `Theory/Mathieu/M24`, James (1973), and the saved-data provenance
in `Degrees120252/source/README.md`.
-/

open Sporadic.Mathieu
open scoped Pointwise
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252 Native252
open Sporadic.Fischer.Fi22.KernelCertificate

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252.Geometry.Certificate
def stages0 : List BitNetwork.Stage := [⟨3, 2, 16, 16777197⟩,
  ⟨5, 4, 128, 16777083⟩,
  ⟨14, 8, 131072, 16646135⟩,
  ⟨8, 32, 8192, 16768991⟩,
  ⟨3, 64, 512, 16776639⟩,
  ⟨7, 256, 32768, 16744191⟩,
  ⟨9, 1024, 524288, 16251903⟩,
  ⟨7, 2048, 262144, 16513023⟩,
  ⟨9, 4096, 2097152, 14675967⟩,
  ⟨2, 16384, 65536, 16695295⟩,
  ⟨20, 1, 1048576, 15728638⟩,
  ⟨1, 4194304, 8388608, 4194303⟩]
def stages1 : List BitNetwork.Stage := [⟨3, 2, 16, 16777197⟩,
  ⟨2, 16, 64, 16777135⟩,
  ⟨19, 4, 2097152, 14680059⟩,
  ⟨7, 16384, 2097152, 14663679⟩,
  ⟨6, 8, 512, 16776695⟩,
  ⟨6, 512, 32768, 16743935⟩,
  ⟨13, 32, 262144, 16515039⟩,
  ⟨8, 1024, 262144, 16514047⟩,
  ⟨4, 8192, 131072, 16637951⟩,
  ⟨1, 65536, 131072, 16580607⟩,
  ⟨19, 1, 524288, 16252926⟩,
  ⟨23, 1, 8388608, 8388606⟩]
def stages (j : Fin 2) := ![stages0, stages1] j

def forceNat {α : Sort*} (n : ℕ) (f : ℕ → α) : α :=
  match n with | 0 => f 0 | n + 1 => f (n + 1)
def applyNetwork : List BitNetwork.Stage → ℕ → ℕ
  | [], n => n
  | s :: ss, n => forceNat (applyNetwork ss n) s.apply

private theorem applyNetwork_eq (ss : List BitNetwork.Stage) (n : ℕ) :
    applyNetwork ss n = BitNetwork.apply ss n := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    simp only [applyNetwork, BitNetwork.apply, ← ih]
    generalize applyNetwork ss n = k
    cases k <;> rfl

private theorem route_correct : ∀ (j : Fin 2) (x : Fin 24),
    BitNetwork.route (stages j) x.val = some ((actor j).val.symm x).val := by decide +kernel

/-- Reducible insertion and sorting keep the arithmetic certificate available
across module boundaries. Their membership lemmas supply all the semantics. -/
def insertMask (n : ℕ) : List ℕ → List ℕ
  | [] => [n]
  | m :: ms => if n ≤ m then n :: m :: ms else m :: insertMask n ms

def sortMasks : List ℕ → List ℕ
  | [] => []
  | n :: ns => insertMask n (sortMasks ns)

private theorem mem_insertMask (n m : ℕ) (row : List ℕ) :
    m ∈ insertMask n row ↔ m = n ∨ m ∈ row := by
  induction row with
  | nil => simp [insertMask]
  | cons a row ih =>
    simp only [insertMask]
    split <;> simp_all [or_left_comm]

private theorem mem_sortMasks (n : ℕ) (row : List ℕ) :
    n ∈ sortMasks row ↔ n ∈ row := by
  induction row with
  | nil => rfl
  | cons a row ih => simp only [sortMasks, mem_insertMask, ih, List.mem_cons]

def transform (j : Fin 2) (row : List ℕ) : List ℕ :=
  sortMasks (row.map (applyNetwork (stages j)))

private theorem mask_network (j : Fin 2) (n : ℕ) :
    mask (applyNetwork (stages j) n) = actor j • mask n := by
  ext x
  rw [← Finset.inv_smul_mem_iff]
  simp only [mask, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [applyNetwork_eq, BitNetwork.sound _ _ _ _ (route_correct j x)]
  rfl

def parts (row : List ℕ) : Finset (Finset (Fin 24)) := row.toFinset.image mask

theorem parts_transform (j : Fin 2) (row : List ℕ) :
    parts (transform j row) = actor j • parts row := by
  have hs : (transform j row).toFinset = (row.map (applyNetwork (stages j))).toFinset := by
    ext n
    simp only [transform, List.mem_toFinset, mem_sortMasks]
  rw [parts, hs]
  ext A
  simp only [Finset.mem_image, List.mem_toFinset, List.mem_map, Finset.mem_smul_finset]
  constructor
  · rintro ⟨n, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨mask m, Finset.mem_image.mpr ⟨m, List.mem_toFinset.mpr hm, rfl⟩,
      (mask_network j m).symm⟩
  · rintro ⟨B, hB, rfl⟩
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hB
    exact ⟨applyNetwork (stages j) m, ⟨m, List.mem_toFinset.mp hm, rfl⟩, mask_network j m⟩

theorem parts_six (row : List ℕ) (h : row.length = 6) :
    parts row = Finset.univ.image (fun k : Fin 6 => mask (row[k.val]?.getD 0)) := by
  ext A
  simp only [parts, Finset.mem_image, List.mem_toFinset, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨m,hm,rfl⟩
    obtain ⟨k,hk,he⟩ := List.mem_iff_getElem.mp hm
    refine ⟨⟨k, by omega⟩, ?_⟩
    simp only [List.getElem?_eq_getElem hk, Option.getD_some]
    rw [he]
  · rintro ⟨k,rfl⟩
    have hk : k.val < row.length := by omega
    refine ⟨row[k.val], List.getElem_mem hk, ?_⟩
    simp only [List.getElem?_eq_getElem hk, Option.getD_some]
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native252.Geometry.Certificate
