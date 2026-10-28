module

public import Theory.Representation.AlternatingSevenBinaryLargeModels.Subspace
public import Theory.Representation.AlternatingSevenBinaryLargeModels.PackedDensity
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic

/-!
# An explicit binary fourteen-space for A₇

Coordinates describe symmetric edge vectors on seven vertices with zero diagonal,
even degree at every vertex, and even total edge weight. The free edges are those
among the first six vertices other than (4,5). That last edge enforces even weight;
the edges incident with vertex 6 enforce the degree equations.

Six checked adjacent-transposition identities prove invariance under S₇. Restricting
the coordinate action to A₇ supplies the actual fourteen-dimensional representation.
Absolute irreducibility is proved separately by a checked matrix-algebra certificate.

Source: the fourteen-dimensional candidate needed in the binary degree-spectrum
argument for Aschbacher–Smith K.1.2, printed p.452/PDF p.463.
-/

public section

open Matrix Thompson.BinaryMatrix
namespace Representation.AlternatingSevenBinaryLargeModels
namespace Fourteen

abbrev Vector := Fin 14 → ZMod 2
abbrev Ambient := (Fin 7 × Fin 7) → ZMod 2

private def edgeRows : Array ℕ := #[0, 1, 2, 4, 8, 16, 31, 1, 0, 32, 64, 128, 256, 481, 2, 32, 0, 512, 1024, 2048, 3618, 4, 64, 512, 0, 4096, 8192, 12868, 8, 128, 1024, 4096, 0, 16383, 11127, 16, 256, 2048, 8192, 16383, 0, 5871, 31, 481, 3618, 12868, 11127, 5871, 0]

private def freeEdges : Fin 14 → Fin 7 × Fin 7 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5)]

private def embeddingMatrix : Matrix (Fin 7 × Fin 7) (Fin 14) (ZMod 2) :=
  fun p j => bit edgeRows[7 * p.1.val + p.2.val]! j.val

/-- The edge embedding in the full permutation module on ordered pairs. -/
def embed : Vector →ₗ[ZMod 2] Ambient := embeddingMatrix.toLin'

/-- Read the fourteen free edge coordinates. -/
def read : Ambient →ₗ[ZMod 2] Vector :=
  LinearMap.pi fun i => LinearMap.proj (freeEdges i)

/-- The simultaneous permutation of both vertices. -/
def ambient : Representation (ZMod 2) (Equiv.Perm (Fin 7)) Ambient where
  toFun g := {
    toFun := fun v p => v (g.symm p.1, g.symm p.2)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem read_embed_basis : ∀ i j : Fin 14,
    read (embed (Pi.single j 1)) i = (Pi.single j (1 : ZMod 2) : Vector) i := by
  decide +kernel

theorem read_embed : read.comp embed = LinearMap.id := by
  apply LinearMap.toMatrix'.injective
  ext i j
  exact read_embed_basis i j

private def adjacentMatrices : Fin 6 → Array ℕ :=
  ![#[1, 32, 64, 128, 256, 2, 4, 8, 16, 512, 1024, 2048, 4096, 8192],
    #[2, 1, 4, 8, 16, 32, 512, 1024, 2048, 64, 128, 256, 4096, 8192],
    #[1, 4, 2, 8, 16, 64, 32, 128, 256, 512, 4096, 8192, 1024, 2048],
    #[1, 2, 8, 4, 16, 32, 128, 64, 256, 1024, 512, 2048, 4096, 16383],
    #[1, 2, 4, 16, 8, 32, 64, 256, 128, 512, 2048, 1024, 8192, 4096],
    #[1, 2, 4, 8, 31, 32, 64, 128, 481, 512, 1024, 3618, 4096, 12868]]

private theorem adjacentMatrices_spec : ∀ i : Fin 6, ∀ k : Fin 14,
    (adjacentMatrices i)[k.val]! =
      edgeRows[7 * ((Equiv.swap i.castSucc i.succ) (freeEdges k).1).val +
        ((Equiv.swap i.castSucc i.succ) (freeEdges k).2).val]! := by
  decide +kernel

set_option maxRecDepth 4000 in
private theorem adjacent_rows : ∀ i : Fin 6, ∀ p : Fin 7 × Fin 7,
    rowProduct edgeRows[7 * p.1.val + p.2.val]!
      (adjacentMatrices i) 14 =
      edgeRows[7 * ((Equiv.swap i.castSucc i.succ) p.1).val +
        ((Equiv.swap i.castSucc i.succ) p.2).val]! := by
  decide +kernel

private theorem embed_single (j : Fin 14) (p : Fin 7 × Fin 7) :
    embed (Pi.single j 1) p = bit edgeRows[7 * p.1.val + p.2.val]! j.val := by
  exact congrFun (Matrix.mulVec_single_one embeddingMatrix j) p

private theorem adjacent_basis (i : Fin 6) (j : Fin 14) :
    embed (read (ambient (Equiv.swap i.castSucc i.succ) (embed (Pi.single j 1)))) =
      ambient (Equiv.swap i.castSucc i.succ) (embed (Pi.single j 1)) := by
  ext p
  have h := congrArg (fun x => bit x j.val) (adjacent_rows i p)
  rw [bit_rowProduct, ← Fin.sum_univ_eq_sum_range] at h
  change (∑ k : Fin 14, bit edgeRows[7 * p.1.val + p.2.val]! k.val *
    embed (Pi.single j 1)
      ((Equiv.swap i.castSucc i.succ) (freeEdges k).1,
       (Equiv.swap i.castSucc i.succ) (freeEdges k).2)) =
    embed (Pi.single j 1)
      ((Equiv.swap i.castSucc i.succ) p.1, (Equiv.swap i.castSucc i.succ) p.2)
  simp only [embed_single]
  simpa only [adjacentMatrices_spec] using h

theorem invariant (g : Equiv.Perm (Fin 7)) :
    embed.comp (read.comp ((ambient g).comp embed)) = (ambient g).comp embed := by
  apply invariant_of_adjacent ambient embed read read_embed
  intro i
  apply LinearMap.toMatrix'.injective
  ext p j
  exact congrFun (adjacent_basis i j) p

/-- The coordinate representation of the fourteen-dimensional edge space. -/
def representation : Representation (ZMod 2) (alternatingGroup (Fin 7)) Vector :=
  (onSubspace ambient embed read read_embed invariant).comp (alternatingGroup (Fin 7)).subtype

def threeCycle : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [_root_.Equiv.Perm.mem_alternatingGroup]; decide⟩

def sevenCycle : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 *
    Equiv.swap 3 4 * Equiv.swap 4 5 * Equiv.swap 5 6, by rw [_root_.Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def firstMatrix : Matrix (Fin 14) (Fin 14) (ZMod 2) := Packed.matrix 14 50218346384480496960274474600508483800306909983504538796034

@[expose] def secondMatrix : Matrix (Fin 14) (Fin 14) (ZMod 2) := Packed.matrix 14 6277293300252381480307984650496061287220879657278417420319

private theorem first_basis : ∀ i j : Fin 14,
    read (ambient threeCycle.val (embed (Pi.single j 1))) i = bit 50218346384480496960274474600508483800306909983504538796034 (14 * i.val + j.val) := by
  decide +kernel

private theorem second_basis : ∀ i j : Fin 14,
    read (ambient sevenCycle.val (embed (Pi.single j 1))) i = bit 6277293300252381480307984650496061287220879657278417420319 (14 * i.val + j.val) := by
  decide +kernel

theorem matrix_threeCycle : LinearMap.toMatrix' (representation threeCycle) = firstMatrix := by
  ext i j
  exact first_basis i j

theorem matrix_sevenCycle : LinearMap.toMatrix' (representation sevenCycle) = secondMatrix := by
  ext i j
  exact second_basis i j

end Fourteen
end Representation.AlternatingSevenBinaryLargeModels
