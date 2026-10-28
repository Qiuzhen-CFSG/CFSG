module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.MatrixIdentification.Representation.Kernel.Words
public import Mathlib.GroupTheory.Coxeter.Basic

/-!
# Explicit binary matrices on all 52 F₄ coordinates

The first four coordinates are the Cartan basis in simple-node order. The
remaining 48 are the roots, in lexicographic order of their doubled Euclidean
coordinates. A natural number packs a matrix row, with bit j recording column j.
The four matrices are the proposed Geck root elements at nodes 1+, 2+, 1−, 2−.

The tables alone do not identify them with the ambient root curves. That is the
separate `FullMatrixComparison` obligation. `FiniteRelations` verifies their
word identities with kernel-checked binary arithmetic on every coordinate.

Source: the integral Geck simple-root formulas in
`Theory.AlgebraicGroup.RootSystems.IntegralGeckConstruction`, specialized to
characteristic two; Aschbacher–Smith F.1.12(I)(5), printed pp.263–264
(PDF pp.274–275) of `refs/quasithin.pdf`.
-/

@[expose] public section
namespace ReeF4.Parabolics.BinarySuzuki.MatrixIdentification.KernelProof.AmbientComputation

/-- Doubled root coordinates, in the order used by rows and columns 4 through 51. -/
def rootCoords : Fin 48 → Fin 4 → ℤ :=
  ![![-2, -2, 0, 0],
    ![-2, 0, -2, 0],
    ![-2, 0, 0, -2],
    ![-2, 0, 0, 0],
    ![-2, 0, 0, 2],
    ![-2, 0, 2, 0],
    ![-2, 2, 0, 0],
    ![-1, -1, -1, -1],
    ![-1, -1, -1, 1],
    ![-1, -1, 1, -1],
    ![-1, -1, 1, 1],
    ![-1, 1, -1, -1],
    ![-1, 1, -1, 1],
    ![-1, 1, 1, -1],
    ![-1, 1, 1, 1],
    ![0, -2, -2, 0],
    ![0, -2, 0, -2],
    ![0, -2, 0, 0],
    ![0, -2, 0, 2],
    ![0, -2, 2, 0],
    ![0, 0, -2, -2],
    ![0, 0, -2, 0],
    ![0, 0, -2, 2],
    ![0, 0, 0, -2],
    ![0, 0, 0, 2],
    ![0, 0, 2, -2],
    ![0, 0, 2, 0],
    ![0, 0, 2, 2],
    ![0, 2, -2, 0],
    ![0, 2, 0, -2],
    ![0, 2, 0, 0],
    ![0, 2, 0, 2],
    ![0, 2, 2, 0],
    ![1, -1, -1, -1],
    ![1, -1, -1, 1],
    ![1, -1, 1, -1],
    ![1, -1, 1, 1],
    ![1, 1, -1, -1],
    ![1, 1, -1, 1],
    ![1, 1, 1, -1],
    ![1, 1, 1, 1],
    ![2, -2, 0, 0],
    ![2, 0, -2, 0],
    ![2, 0, 0, -2],
    ![2, 0, 0, 0],
    ![2, 0, 0, 2],
    ![2, 0, 2, 0],
    ![2, 2, 0, 0]]

/-- Packed rows of the long+, short+, long−, and short− root elements. -/
def generatorRows (i : Fin 4) : Array ℕ :=
  ![#[1, 67108866, 4, 8, 16, 32, 96, 128, 256, 768, 1024, 2048, 4096, 12288, 16384, 32768, 65536, 196608, 262144, 524288, 1572864, 2097152, 4194304, 12582912, 16777216, 33554432, 67108864, 167772160, 268435456, 603979777, 1342177280, 2147483648, 4294967296, 12884901888, 17179869184, 34359738368, 103079215104, 137438953472, 274877906944, 824633720832, 1099511627776, 2199023255552, 4398046511104, 13194139533312, 17592186044416, 35184372088832, 70368744177664, 211106232532992, 281474976710656, 562949953421312, 1688849860263936, 2251799813685248],
    #[1, 2, 134217732, 8, 16, 32, 64, 192, 320, 512, 1024, 2048, 6144, 8192, 24576, 32768, 98304, 131072, 393216, 524288, 1048576, 3145728, 5242880, 8388608, 16777216, 50331648, 83886080, 134217728, 402653194, 536870912, 1610612736, 2684354560, 4294967296, 8589934592, 25769803776, 42949672960, 68719476736, 137438953472, 412316860416, 549755813888, 1649267441664, 2199023255552, 6597069766656, 8796093022208, 26388279066624, 35184372088832, 70368744177664, 140737488355328, 422212465065984, 703687441776640, 1125899906842624, 2251799813685248],
    #[1, 536870914, 4, 8, 16, 96, 64, 128, 768, 512, 1024, 2048, 12288, 8192, 16384, 32768, 196608, 131072, 262144, 1572864, 1048576, 2097152, 12582912, 8388608, 16777216, 167772160, 603979777, 134217728, 1342177280, 536870912, 1073741824, 2147483648, 12884901888, 8589934592, 17179869184, 103079215104, 68719476736, 137438953472, 824633720832, 549755813888, 1099511627776, 2199023255552, 13194139533312, 8796093022208, 17592186044416, 35184372088832, 211106232532992, 140737488355328, 281474976710656, 1688849860263936, 1125899906842624, 2251799813685248],
    #[1, 2, 268435460, 8, 16, 32, 320, 384, 256, 512, 1024, 6144, 4096, 24576, 16384, 98304, 65536, 393216, 262144, 524288, 5242880, 6291456, 4194304, 8388608, 83886080, 100663296, 67108864, 402653194, 268435456, 2684354560, 3221225472, 2147483648, 4294967296, 42949672960, 51539607552, 34359738368, 68719476736, 412316860416, 274877906944, 1649267441664, 1099511627776, 6597069766656, 4398046511104, 26388279066624, 17592186044416, 35184372088832, 70368744177664, 703687441776640, 844424930131968, 562949953421312, 1125899906842624, 2251799813685248]] i

/-- Interpret one packed bit in the binary field. -/
def bit (a j : ℕ) : ZMod 2 := if a.testBit j then 1 else 0

/-- Decode all 52 rows and columns, including the Cartan coordinates. -/
def decode (a : Array ℕ) : Matrix (Fin 52) (Fin 52) (ZMod 2) :=
  fun i j => bit a[i.val]! j.val

/-- The four explicitly tabulated 52-dimensional binary matrices. -/
def generator (i : Fin 4) : Matrix (Fin 52) (Fin 52) (ZMod 2) :=
  decode (generatorRows i)

end ReeF4.Parabolics.BinarySuzuki.MatrixIdentification.KernelProof.AmbientComputation
