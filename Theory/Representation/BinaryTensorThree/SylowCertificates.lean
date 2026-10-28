module
public import Theory.Representation.BinaryTensorThree.SylowModel

/-!
# Checked quadratic actors in the binary tensor Sylow model

There are 44 square-one elements, including the identity. The certificate
rejects each incompatible ordered pair by a nonzero entry of a double
displacement. Every compatible pair of distinct nonidentity vertices has
at most four common neighbors. Three independent displacement vectors are
also checked for each nonidentity vertex. These are small kernel-checked
calculations on the literal tensor matrices; no native evaluator is used.

Source: Aschbacher--Smith H.4.10--11, printed p.384. The companion theorem
uses Thompson replacement to deduce non-FF for the actual action.
-/

@[expose] public section

namespace BinaryTensorThree.Small
open BinaryPermutation.FiveTensorSquare

def vertexData : Fin 44 → D8 × D8 × Bool := ![
  (.r 0, .r 0, false),
  (.r 0, .r 0, true),
  (.r 0, .r 2, false),
  (.r 0, .sr 0, false),
  (.r 0, .sr 1, false),
  (.r 0, .sr 2, false),
  (.r 0, .sr 3, false),
  (.r 1, .r 3, true),
  (.r 2, .r 0, false),
  (.r 2, .r 2, false),
  (.r 2, .r 2, true),
  (.r 2, .sr 0, false),
  (.r 2, .sr 1, false),
  (.r 2, .sr 2, false),
  (.r 2, .sr 3, false),
  (.r 3, .r 1, true),
  (.sr 0, .r 0, false),
  (.sr 0, .r 2, false),
  (.sr 0, .sr 0, false),
  (.sr 0, .sr 0, true),
  (.sr 0, .sr 1, false),
  (.sr 0, .sr 2, false),
  (.sr 0, .sr 3, false),
  (.sr 1, .r 0, false),
  (.sr 1, .r 2, false),
  (.sr 1, .sr 0, false),
  (.sr 1, .sr 1, false),
  (.sr 1, .sr 1, true),
  (.sr 1, .sr 2, false),
  (.sr 1, .sr 3, false),
  (.sr 2, .r 0, false),
  (.sr 2, .r 2, false),
  (.sr 2, .sr 0, false),
  (.sr 2, .sr 1, false),
  (.sr 2, .sr 2, false),
  (.sr 2, .sr 2, true),
  (.sr 2, .sr 3, false),
  (.sr 3, .r 0, false),
  (.sr 3, .r 2, false),
  (.sr 3, .sr 0, false),
  (.sr 3, .sr 1, false),
  (.sr 3, .sr 2, false),
  (.sr 3, .sr 3, false),
  (.sr 3, .sr 3, true)]

def vertex (v : Fin 44) : P :=
  ⟨(fun i => if i=1 then (vertexData v).1 else (vertexData v).2.1),
    if (vertexData v).2.2 then swapIndex else 1⟩

def adjacencyRows : Fin 44 → Nat := ![17592186044415, 3, 125, 45, 85, 45, 85, 129, 138521149697, 513, 1025, 2049, 4097, 8193, 16385, 32769, 1073807617, 131073, 262145, 524289, 1048577, 2097153, 4194305, 137447342337, 16777217, 33554433, 67108865, 134217729, 268435457, 536870913, 1073807617, 2147483649, 4294967297, 8589934593, 17179869185, 34359738369, 68719476737, 137447342337, 274877906945, 549755813889, 1099511627777, 2199023255553, 4398046511105, 8796093022209]

def adjacent (v w : Fin 44) : Bool := (adjacencyRows v).testBit w.val

def witness : Fin 44 → Fin 44 → (Fin 9 × Fin 9 × Bool) := ![
  ![(0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false)],
  ![(0,0,false), (0,0,false), (0,1,false), (0,1,false), (0,1,false), (0,2,false), (1,1,false), (0,2,false), (0,1,false), (1,1,false), (1,1,false), (0,1,false), (1,2,false), (0,5,false), (0,1,false), (0,2,false), (0,1,false), (0,1,false), (2,1,false), (2,1,false), (0,1,false), (0,2,false), (0,1,false), (0,1,false), (1,1,false), (0,1,false), (1,2,false), (1,2,false), (0,5,false), (0,1,false), (0,2,false), (0,5,false), (0,2,false), (0,5,false), (1,1,false), (1,1,false), (0,2,false), (3,1,false), (0,1,false), (0,1,false), (0,1,false), (0,2,false), (1,1,false), (1,1,false)],
  ![(0,0,false), (1,3,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,2,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,3,false), (0,3,false), (0,3,false), (0,3,false), (0,3,false), (0,3,false), (0,3,false), (0,3,false), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (3,0,false), (3,0,false), (3,0,false), (3,0,false), (3,0,false), (3,0,false), (1,0,false)],
  ![(0,0,false), (1,4,false), (0,0,false), (0,0,false), (0,0,true), (0,0,false), (0,0,true), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,4,false), (0,4,false), (0,4,false), (0,4,false), (0,4,false), (0,4,false), (0,4,false), (0,4,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (3,1,false), (3,1,false), (3,1,false), (3,1,false), (3,1,false), (3,1,false), (1,1,false)],
  ![(0,0,false), (1,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,2,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,3,false), (0,3,false), (0,3,true), (0,2,true), (0,3,false), (0,3,true), (0,3,false), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (3,0,false), (3,0,false), (3,0,true), (3,0,false), (3,0,true), (3,0,false), (1,6,false)],
  ![(0,0,false), (1,3,false), (0,0,false), (0,0,false), (0,0,true), (0,0,false), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,3,false), (0,3,false), (0,3,false), (0,3,false), (0,3,false), (0,3,false), (0,3,false), (0,3,false), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (3,0,false), (3,0,false), (3,0,false), (3,0,false), (3,0,false), (3,0,false), (1,0,false)],
  ![(0,0,false), (1,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,0,false), (0,6,false), (1,0,false), (1,0,false), (1,0,false), (0,3,false), (1,0,false), (0,3,false), (1,0,false), (1,0,true), (1,3,false), (1,3,false), (1,3,true), (1,2,true), (1,3,false), (1,3,true), (1,3,false), (1,0,false), (1,0,false), (0,3,false), (1,0,false), (1,0,false), (0,3,false), (1,0,false), (1,0,false), (1,0,false), (0,6,false), (1,0,false), (0,6,false), (0,6,false), (1,0,false), (4,0,false), (4,0,false), (4,0,true), (4,0,false), (4,0,true), (4,0,false), (1,0,false)],
  ![(0,0,false), (1,0,false), (0,2,false), (0,1,true), (0,2,false), (0,0,true), (1,2,false), (0,0,false), (0,1,true), (0,0,true), (0,0,true), (0,4,true), (0,1,true), (0,0,true), (0,0,true), (0,0,true), (0,3,false), (0,0,true), (0,2,false), (0,2,false), (0,0,true), (0,0,true), (0,3,false), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,1,true), (0,3,false), (2,0,false), (0,3,false), (0,0,true), (0,0,true), (0,0,true), (3,0,false), (0,2,false), (0,0,true), (0,2,false), (0,0,true), (1,2,false), (2,0,false)],
  ![(0,0,false), (1,1,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (0,1,false), (0,0,false), (0,0,true), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (0,1,true), (0,0,false), (0,0,true), (0,1,false), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (0,0,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (0,0,true), (1,0,false), (0,0,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (0,0,true), (1,0,false), (0,0,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (1,1,false)],
  ![(0,0,false), (1,1,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (0,0,true), (0,0,true), (0,0,false), (1,1,false), (0,0,true), (1,0,false), (0,1,false), (0,0,true), (0,0,true), (0,3,false), (0,0,true), (0,1,false), (0,1,false), (0,0,true), (0,0,true), (0,3,false), (0,0,true), (3,0,false), (0,0,true), (1,0,false), (1,0,false), (0,1,false), (0,0,true), (0,0,true), (0,3,false), (0,0,true), (0,3,false), (0,1,false), (0,1,false), (0,0,true), (3,0,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (1,0,false)],
  ![(0,0,false), (1,1,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (0,0,true), (0,0,true), (1,1,false), (0,0,false), (0,0,true), (1,0,false), (0,3,false), (0,0,true), (0,0,true), (0,3,false), (0,0,true), (0,1,false), (0,1,false), (0,0,true), (0,0,true), (0,3,false), (0,0,true), (1,1,false), (0,0,true), (1,0,false), (1,0,false), (0,3,false), (0,0,true), (0,0,true), (0,1,false), (0,0,true), (0,1,false), (0,1,false), (0,1,false), (0,0,true), (3,0,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (1,0,false)],
  ![(0,0,false), (1,1,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (0,4,false), (0,1,false), (0,0,true), (0,0,true), (0,0,false), (0,1,true), (0,0,true), (0,1,false), (0,0,true), (0,4,false), (0,0,true), (0,1,false), (0,1,false), (0,0,true), (0,0,true), (0,4,false), (0,1,false), (0,0,true), (3,1,false), (0,1,true), (0,5,true), (0,0,true), (0,1,false), (0,1,false), (0,0,true), (0,4,false), (0,1,true), (0,0,true), (0,0,true), (0,1,false), (3,1,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (1,4,false)],
  ![(0,0,false), (1,1,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (0,1,false), (0,0,true), (1,0,false), (1,1,false), (0,1,false), (0,0,false), (0,1,true), (0,0,true), (0,0,true), (0,3,false), (0,0,true), (0,1,false), (0,1,false), (0,0,true), (0,0,true), (0,3,false), (0,0,true), (1,0,false), (0,1,false), (3,0,false), (1,0,false), (0,1,true), (0,0,true), (0,0,true), (0,3,false), (0,1,false), (0,3,false), (0,1,true), (0,1,true), (0,0,true), (3,0,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (1,0,false)],
  ![(0,0,false), (1,1,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (0,0,true), (0,0,true), (0,1,false), (0,1,false), (0,0,true), (0,1,false), (0,0,false), (0,1,true), (0,1,true), (0,3,false), (0,0,true), (0,1,false), (0,1,false), (0,0,true), (0,0,true), (0,3,false), (0,0,true), (0,1,false), (0,0,true), (0,1,false), (0,1,false), (3,0,false), (0,1,true), (0,0,true), (0,1,false), (0,0,true), (0,1,false), (0,3,false), (0,3,false), (0,1,true), (3,0,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (1,0,false)],
  ![(0,0,false), (1,1,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (0,0,true), (1,0,false), (0,0,true), (0,0,true), (0,1,true), (0,0,true), (0,1,false), (0,0,false), (0,1,true), (1,3,false), (0,0,true), (0,1,false), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (1,0,false), (0,0,true), (0,1,true), (0,0,true), (0,0,true), (0,1,false), (4,0,false), (1,0,false), (0,0,true), (0,1,true), (0,0,true), (0,1,false), (0,1,false), (1,3,false), (4,0,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (1,1,false)],
  ![(0,0,false), (1,0,false), (0,3,true), (0,1,false), (0,0,true), (0,3,true), (1,0,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,1,false), (0,1,false), (0,0,false), (0,3,true), (0,4,true), (0,1,false), (0,1,false), (0,0,true), (1,0,false), (0,0,true), (0,1,false), (0,1,true), (0,0,true), (0,0,true), (0,0,true), (0,1,false), (0,1,false), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (3,1,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (1,0,false)],
  ![(0,0,false), (1,4,false), (0,3,false), (0,4,false), (0,3,false), (0,3,false), (1,3,false), (0,4,false), (0,0,false), (0,3,false), (0,3,false), (0,4,false), (0,3,false), (0,3,false), (1,3,false), (0,3,false), (0,0,false), (0,3,false), (0,4,false), (0,4,false), (0,3,false), (0,3,false), (1,3,false), (0,0,true), (0,3,false), (0,4,false), (0,3,false), (0,3,false), (0,3,false), (1,3,false), (0,0,false), (0,3,false), (0,4,false), (0,3,false), (0,3,false), (0,3,false), (1,3,false), (0,0,true), (0,3,false), (0,4,false), (0,3,false), (0,3,false), (1,3,false), (1,4,false)],
  ![(0,0,false), (1,3,false), (0,3,false), (0,4,false), (0,3,false), (0,3,false), (1,3,false), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,4,false), (0,3,false), (0,0,false), (0,3,false), (0,3,false), (1,3,false), (0,4,false), (0,3,false), (0,0,true), (0,1,true), (0,0,true), (0,1,true), (0,2,true), (0,2,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (3,0,false), (0,3,false), (0,4,false), (0,3,false), (0,3,false), (1,3,false), (1,0,false)],
  ![(0,0,false), (2,1,false), (0,3,false), (0,4,false), (0,3,false), (0,3,false), (1,3,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,3,false), (0,4,false), (0,3,false), (0,0,false), (2,1,false), (0,3,false), (0,3,false), (0,4,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (3,1,false), (0,3,false), (0,4,false), (0,3,false), (0,3,false), (1,3,false), (1,1,false)],
  ![(0,0,false), (2,1,false), (0,2,false), (0,1,false), (0,2,false), (0,1,false), (1,2,false), (0,2,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,2,false), (2,1,false), (0,0,false), (0,2,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,2,false), (0,1,false), (0,2,false), (0,1,false), (0,1,false), (0,1,false), (0,2,false), (3,1,false), (0,2,false), (0,1,false), (0,2,false), (0,1,false), (1,2,false), (1,1,false)],
  ![(0,0,false), (1,0,false), (0,3,false), (0,4,true), (0,3,false), (0,3,true), (1,3,false), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,3,false), (1,3,false), (0,3,true), (0,2,true), (0,0,false), (0,4,true), (0,3,false), (0,0,true), (0,1,true), (0,0,true), (0,1,true), (0,2,true), (0,2,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (3,0,false), (0,3,false), (0,2,true), (0,3,false), (0,0,true), (1,3,false), (1,3,false)],
  ![(0,0,false), (1,3,false), (0,3,false), (0,4,false), (0,3,false), (0,3,false), (1,3,false), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (1,0,false), (0,3,false), (0,4,false), (0,3,false), (0,3,false), (0,4,false), (0,0,false), (0,3,false), (0,0,true), (0,1,true), (0,0,true), (0,0,true), (0,0,true), (0,2,true), (0,1,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (3,0,false), (0,3,false), (0,4,false), (0,3,false), (0,3,false), (1,3,false), (1,0,false)],
  ![(0,0,false), (1,0,false), (0,3,false), (0,4,true), (0,3,false), (0,3,true), (1,3,false), (0,3,false), (1,0,false), (0,3,false), (0,3,false), (0,4,false), (0,3,false), (0,3,false), (1,0,false), (0,0,true), (1,3,false), (0,3,false), (0,4,true), (0,1,true), (0,3,false), (0,3,true), (0,0,false), (1,0,false), (0,3,false), (0,4,false), (0,3,false), (0,3,false), (0,3,false), (1,0,false), (1,0,false), (0,3,false), (0,3,false), (0,3,false), (0,4,false), (0,4,false), (1,0,false), (4,0,false), (0,3,false), (0,0,true), (0,3,false), (0,2,true), (1,3,false), (1,0,false)],
  ![(0,0,false), (1,0,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (0,0,true), (0,0,false), (0,0,true), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (0,1,true), (0,0,false), (0,0,true), (0,1,true), (0,1,true), (0,0,true), (0,0,true), (1,0,true), (0,0,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (0,0,true), (1,0,false), (0,0,false), (0,0,true), (0,1,true), (0,0,true), (0,0,true), (0,0,true), (1,0,true), (0,0,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (1,0,false)],
  ![(0,0,false), (1,2,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (0,0,true), (0,0,true), (3,0,false), (1,0,false), (0,0,true), (1,0,false), (0,1,false), (0,0,true), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,0,true), (0,0,false), (0,0,true), (1,0,false), (1,2,false), (0,1,false), (0,0,true), (0,0,true), (0,3,true), (0,0,true), (0,3,true), (0,1,true), (0,1,true), (0,0,true), (3,0,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (1,0,false)],
  ![(0,0,false), (1,0,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (3,1,false), (0,1,true), (0,0,true), (0,1,false), (0,0,true), (0,4,true), (0,0,true), (0,1,true), (0,1,true), (0,0,true), (0,0,true), (0,4,true), (0,1,false), (0,0,true), (0,0,false), (0,1,true), (0,5,true), (0,0,true), (0,1,false), (0,1,true), (0,0,true), (0,4,true), (0,1,true), (0,0,true), (0,0,true), (0,0,true), (3,1,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (1,0,false)],
  ![(0,0,false), (1,2,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (0,0,true), (0,0,true), (1,0,false), (1,0,false), (0,1,false), (3,0,false), (0,1,true), (0,0,true), (0,0,true), (0,1,false), (0,1,false), (0,1,true), (0,1,true), (0,1,false), (0,0,true), (0,1,false), (0,0,true), (1,0,false), (0,1,false), (0,0,false), (1,2,false), (0,1,true), (0,0,true), (0,0,true), (0,3,true), (0,0,true), (0,3,true), (0,1,true), (0,1,true), (0,0,true), (3,0,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (1,0,false)],
  ![(0,0,false), (1,2,false), (0,0,true), (0,2,false), (0,0,true), (0,0,true), (1,0,false), (0,0,true), (0,0,true), (1,0,false), (1,0,false), (0,5,false), (1,2,false), (0,1,true), (0,0,true), (0,0,true), (0,5,false), (0,2,false), (0,1,true), (0,1,true), (0,2,false), (0,0,true), (0,5,false), (0,0,true), (1,0,false), (0,5,false), (1,2,false), (0,0,false), (0,1,true), (0,0,true), (0,0,true), (0,3,true), (0,0,true), (0,3,true), (0,1,true), (0,1,true), (0,0,true), (3,0,false), (0,0,true), (0,2,false), (0,0,true), (0,0,true), (1,0,false), (1,0,false)],
  ![(0,0,false), (1,1,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (0,0,true), (0,0,true), (0,1,false), (0,1,false), (0,0,true), (0,1,false), (3,0,false), (0,1,true), (0,2,false), (0,2,false), (0,2,false), (0,2,false), (0,2,false), (0,2,false), (0,2,false), (0,2,false), (0,0,true), (0,1,false), (0,0,true), (0,1,false), (0,1,false), (0,0,false), (0,1,true), (0,0,true), (0,1,true), (0,0,true), (0,0,true), (0,3,true), (0,1,true), (0,1,true), (3,0,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (1,0,false)],
  ![(0,0,false), (1,0,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (0,0,true), (1,0,false), (0,0,true), (0,0,true), (0,1,true), (0,0,true), (0,1,false), (4,0,false), (0,1,false), (1,3,true), (0,0,true), (0,1,false), (0,1,false), (0,0,true), (0,1,false), (1,0,true), (1,0,false), (0,0,true), (0,1,true), (0,0,true), (0,0,true), (0,1,false), (0,0,false), (1,0,true), (0,0,true), (0,1,true), (0,0,true), (0,0,true), (0,0,true), (1,3,true), (4,0,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (1,0,false)],
  ![(0,0,false), (1,1,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (0,1,false), (0,0,false), (0,0,true), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (0,0,true), (0,0,false), (0,0,true), (0,1,false), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (0,0,true), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (0,0,true), (1,0,false), (0,0,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (0,0,true), (1,0,false), (0,0,true), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (1,1,false)],
  ![(0,0,false), (1,1,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (0,3,true), (0,0,true), (0,3,false), (0,3,false), (0,0,true), (0,3,false), (0,1,false), (0,0,true), (0,0,true), (0,3,false), (0,0,true), (0,1,false), (0,1,false), (0,0,true), (0,0,true), (0,3,false), (0,0,true), (0,3,false), (0,0,true), (0,3,false), (0,3,false), (0,1,false), (0,0,true), (0,0,true), (0,0,false), (0,0,true), (1,0,false), (0,1,false), (0,1,false), (0,0,true), (3,0,false), (0,1,true), (0,1,false), (0,1,true), (0,1,true), (1,0,false), (1,0,false)],
  ![(0,0,false), (1,1,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (2,0,false), (0,1,false), (0,0,true), (0,0,true), (0,4,false), (0,1,true), (0,0,true), (0,1,false), (0,0,true), (0,4,false), (0,0,true), (0,1,false), (0,1,false), (0,0,true), (0,0,true), (0,4,false), (0,1,false), (0,0,true), (0,4,false), (0,0,true), (0,0,true), (0,0,true), (0,1,false), (0,1,false), (0,0,true), (0,0,false), (0,1,true), (0,0,true), (0,0,true), (0,1,false), (3,1,false), (0,0,true), (0,1,false), (0,2,true), (0,0,true), (1,0,false), (2,0,false)],
  ![(0,0,false), (1,1,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (0,1,false), (0,0,true), (0,3,false), (0,3,false), (0,1,false), (0,3,false), (0,1,true), (0,0,true), (0,0,true), (0,3,false), (0,0,true), (0,1,false), (0,1,false), (0,0,true), (0,0,true), (0,3,false), (0,0,true), (0,3,false), (0,1,false), (0,3,false), (0,3,false), (0,0,true), (0,0,true), (0,0,true), (1,0,false), (0,1,false), (0,0,false), (0,1,true), (0,3,true), (0,0,true), (3,0,false), (0,1,true), (0,1,false), (0,1,true), (0,1,true), (1,0,false), (1,0,false)],
  ![(0,0,false), (1,1,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (0,0,true), (0,0,true), (0,1,false), (0,1,false), (0,0,true), (0,1,false), (0,3,false), (0,1,true), (0,0,true), (0,3,false), (0,0,true), (0,1,false), (0,1,false), (0,0,true), (0,0,true), (0,3,false), (0,0,true), (0,1,false), (0,0,true), (0,1,false), (0,1,false), (0,3,false), (0,0,true), (0,0,true), (0,1,false), (0,0,true), (0,1,false), (0,0,false), (1,1,false), (0,1,true), (3,0,false), (0,2,true), (0,1,false), (0,0,true), (0,2,true), (1,0,false), (1,0,false)],
  ![(0,0,false), (1,1,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (0,0,true), (0,0,true), (0,1,false), (0,1,false), (0,0,true), (0,1,false), (0,1,false), (0,1,true), (0,0,true), (0,3,false), (0,0,true), (0,1,false), (0,1,false), (0,0,true), (0,0,true), (0,3,false), (0,0,true), (0,1,false), (0,0,true), (0,1,false), (0,1,false), (0,1,false), (0,0,true), (0,0,true), (0,3,false), (0,0,true), (0,3,false), (1,1,false), (0,0,false), (0,1,true), (3,0,false), (0,2,true), (0,1,false), (0,0,true), (0,2,true), (1,0,false), (1,0,false)],
  ![(0,0,false), (1,1,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (0,0,true), (1,0,false), (0,0,true), (0,0,true), (0,1,true), (0,0,true), (0,1,false), (1,3,false), (0,0,true), (1,3,false), (0,0,true), (0,1,false), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (1,0,false), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,1,false), (1,3,false), (1,0,false), (0,0,true), (0,1,true), (0,0,true), (0,1,false), (0,1,false), (0,0,false), (4,0,false), (0,0,true), (0,1,false), (0,0,true), (0,0,true), (1,0,false), (1,1,false)],
  ![(0,0,false), (1,0,false), (3,0,false), (3,1,false), (3,0,false), (3,0,false), (4,0,false), (3,0,true), (0,0,false), (3,0,false), (1,1,false), (3,1,false), (3,0,false), (3,0,false), (4,0,false), (0,2,false), (0,0,false), (0,1,false), (3,1,true), (3,1,true), (0,1,false), (0,2,false), (4,0,true), (0,0,false), (3,0,false), (3,1,false), (3,0,false), (1,1,false), (3,0,false), (4,0,false), (0,0,false), (0,1,false), (3,1,true), (0,1,false), (0,2,false), (0,2,false), (4,0,true), (0,0,false), (3,0,false), (3,1,false), (3,0,false), (3,0,false), (4,0,false), (1,0,false)],
  ![(0,0,false), (1,1,false), (3,0,false), (3,1,false), (3,0,false), (3,0,false), (4,0,false), (0,2,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,1,false), (0,3,true), (0,2,false), (0,2,false), (0,3,true), (0,3,true), (0,1,false), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,1,false), (0,0,true), (0,1,false), (0,2,false), (0,2,false), (0,0,true), (3,0,false), (0,0,false), (3,0,false), (4,0,false), (3,1,false), (3,0,false), (1,0,false)],
  ![(0,0,false), (1,0,false), (3,0,false), (3,1,false), (3,0,false), (3,0,false), (4,0,false), (0,0,true), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,4,true), (0,2,false), (0,4,true), (0,1,true), (0,2,false), (0,1,false), (0,0,true), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,false), (0,1,true), (0,1,false), (0,1,true), (0,1,false), (0,2,false), (0,2,false), (0,1,true), (3,1,false), (3,0,false), (0,0,false), (3,0,false), (3,0,false), (3,1,false), (1,0,false)],
  ![(0,0,false), (1,0,false), (3,0,false), (3,1,true), (3,0,false), (3,0,true), (4,0,false), (0,2,false), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,1,false), (0,3,true), (0,2,false), (0,2,false), (0,3,true), (0,3,true), (0,1,false), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,1,false), (0,2,false), (0,1,false), (0,0,true), (0,0,true), (0,0,true), (3,0,false), (4,0,false), (3,0,true), (0,0,false), (3,1,true), (3,0,false), (1,1,false)],
  ![(0,0,false), (1,2,false), (3,0,false), (3,1,false), (3,0,false), (3,0,false), (4,0,false), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,2,false), (0,3,true), (0,1,false), (0,1,false), (0,0,true), (0,3,true), (0,2,false), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,0,true), (0,1,false), (0,0,true), (0,1,false), (0,2,false), (0,2,false), (0,0,true), (3,0,false), (3,1,false), (3,0,false), (3,1,false), (0,0,false), (3,0,false), (1,0,false)],
  ![(0,0,false), (1,1,false), (3,0,false), (3,1,true), (3,0,false), (3,0,true), (4,0,false), (0,2,false), (1,0,false), (1,0,false), (1,0,false), (0,3,false), (1,0,false), (0,3,false), (1,0,false), (0,2,false), (1,3,true), (0,1,false), (1,3,true), (1,2,true), (0,1,false), (0,2,false), (1,3,true), (1,0,false), (1,0,false), (0,3,false), (1,0,false), (1,0,false), (0,3,false), (1,0,false), (1,0,true), (0,1,false), (0,2,false), (0,1,false), (1,0,true), (1,0,true), (1,0,true), (4,0,false), (3,0,false), (3,1,true), (3,0,false), (3,0,true), (0,0,false), (1,1,false)],
  ![(0,0,false), (1,1,false), (0,1,false), (1,1,true), (0,1,false), (1,0,true), (1,1,false), (2,0,false), (0,1,false), (1,0,false), (1,0,false), (0,3,false), (1,0,false), (0,1,false), (0,1,false), (1,0,false), (1,4,true), (0,1,false), (1,1,true), (1,1,true), (0,1,false), (1,0,false), (1,0,true), (0,1,false), (1,0,false), (0,3,false), (1,0,false), (1,0,false), (0,1,false), (0,1,false), (1,1,true), (0,3,false), (2,0,false), (0,3,false), (1,0,true), (1,0,true), (1,1,true), (3,1,false), (0,1,false), (1,0,true), (0,1,false), (1,0,true), (1,1,false), (0,0,false)]]

def unit (k : Fin 9) : Space := Pi.single ⟨k.val/3,by omega⟩ (Pi.single ⟨k.val%3,by omega⟩ 1)
def displacement (v : Fin 44) (X : Space) : Space := act (vertex v) X-X

def rejection (v w : Fin 44) : Prop :=
  adjacent v w = true ∨
    let a := if (witness v w).2.2 then w else v
    let b := if (witness v w).2.2 then v else w
    let k := (witness v w).2.1
    displacement a (displacement b (unit (witness v w).1)) ⟨k.val/3,by omega⟩ ⟨k.val%3,by omega⟩ ≠ 0

def pivot : Fin 44 → Fin 3 → Fin 9 := ![
  ![0, 0, 0],
  ![1, 2, 5],
  ![0, 3, 6],
  ![0, 3, 6],
  ![0, 3, 6],
  ![0, 3, 6],
  ![1, 4, 7],
  ![0, 2, 3],
  ![0, 1, 2],
  ![0, 1, 2],
  ![0, 1, 3],
  ![0, 1, 2],
  ![0, 1, 2],
  ![0, 1, 2],
  ![0, 1, 2],
  ![0, 1, 4],
  ![0, 1, 2],
  ![0, 1, 2],
  ![0, 1, 2],
  ![0, 2, 5],
  ![0, 1, 2],
  ![0, 1, 2],
  ![0, 1, 2],
  ![0, 1, 2],
  ![0, 1, 2],
  ![0, 1, 2],
  ![0, 1, 2],
  ![0, 1, 3],
  ![0, 1, 2],
  ![0, 1, 2],
  ![0, 1, 2],
  ![0, 1, 2],
  ![0, 1, 2],
  ![0, 1, 2],
  ![0, 1, 2],
  ![0, 1, 3],
  ![0, 1, 2],
  ![3, 4, 5],
  ![0, 3, 4],
  ![0, 3, 4],
  ![0, 3, 4],
  ![0, 3, 4],
  ![1, 3, 4],
  ![1, 2, 4]]

def probe (v : Fin 44) : Natural →ₗ[ZMod 2] Space where
  toFun c := ∑ i : Fin 3, c i • unit (pivot v i)
  map_add' x y := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' a x := by simp [mul_smul,Finset.smul_sum]

theorem vertex_zero : vertex 0 = 1 := by decide +kernel

theorem vertex_cover : ∀ g : P, g*g=1 → ∃ v,vertex v=g := by decide +kernel

theorem vertex_ne : ∀ v : Fin 44,vertex v=1 → v=0 := by decide +kernel

private theorem rejection_check_00 : ∀ v : Fin 4, ∀ w : Fin 44,
    rejection ⟨4*0+v.val,by omega⟩ w := by
  unfold rejection
  decide +kernel

private theorem rejection_check_01 : ∀ v : Fin 4, ∀ w : Fin 44,
    rejection ⟨4*1+v.val,by omega⟩ w := by
  unfold rejection
  decide +kernel

private theorem rejection_check_02 : ∀ v : Fin 4, ∀ w : Fin 44,
    rejection ⟨4*2+v.val,by omega⟩ w := by
  unfold rejection
  decide +kernel

private theorem rejection_check_03 : ∀ v : Fin 4, ∀ w : Fin 44,
    rejection ⟨4*3+v.val,by omega⟩ w := by
  unfold rejection
  decide +kernel

private theorem rejection_check_04 : ∀ v : Fin 4, ∀ w : Fin 44,
    rejection ⟨4*4+v.val,by omega⟩ w := by
  unfold rejection
  decide +kernel

private theorem rejection_check_05 : ∀ v : Fin 4, ∀ w : Fin 44,
    rejection ⟨4*5+v.val,by omega⟩ w := by
  unfold rejection
  decide +kernel

private theorem rejection_check_06 : ∀ v : Fin 4, ∀ w : Fin 44,
    rejection ⟨4*6+v.val,by omega⟩ w := by
  unfold rejection
  decide +kernel

private theorem rejection_check_07 : ∀ v : Fin 4, ∀ w : Fin 44,
    rejection ⟨4*7+v.val,by omega⟩ w := by
  unfold rejection
  decide +kernel

private theorem rejection_check_08 : ∀ v : Fin 4, ∀ w : Fin 44,
    rejection ⟨4*8+v.val,by omega⟩ w := by
  unfold rejection
  decide +kernel

private theorem rejection_check_09 : ∀ v : Fin 4, ∀ w : Fin 44,
    rejection ⟨4*9+v.val,by omega⟩ w := by
  unfold rejection
  decide +kernel

private theorem rejection_check_10 : ∀ v : Fin 4, ∀ w : Fin 44,
    rejection ⟨4*10+v.val,by omega⟩ w := by
  unfold rejection
  decide +kernel

theorem rejection_check (v w : Fin 44) : rejection v w := by
  have hb : ∀ (b : Fin 11) (a : Fin 4), rejection ⟨4*b.val+a.val,by omega⟩ w := by
    intro b
    fin_cases b
    · exact fun a => rejection_check_00 a w
    · exact fun a => rejection_check_01 a w
    · exact fun a => rejection_check_02 a w
    · exact fun a => rejection_check_03 a w
    · exact fun a => rejection_check_04 a w
    · exact fun a => rejection_check_05 a w
    · exact fun a => rejection_check_06 a w
    · exact fun a => rejection_check_07 a w
    · exact fun a => rejection_check_08 a w
    · exact fun a => rejection_check_09 a w
    · exact fun a => rejection_check_10 a w
  have h := hb ⟨v.val/4,by omega⟩ ⟨v.val%4,by omega⟩
  have he : (⟨4*(v.val/4)+v.val%4,by omega⟩ : Fin 44)=v := by
    apply Fin.ext
    change 4*(v.val/4)+v.val%4=v.val
    omega
  simpa only [he] using h

theorem rank_check : ∀ v : Fin 44,v≠0 → ∀ c : Natural,
    displacement v (probe v c) = 0 → c=0 := by decide +kernel

theorem neighbors_check : ∀ v w : Fin 44,v≠0 → w≠0 → w≠v → adjacent v w=true →
    (Finset.univ.filter (fun k => adjacent v k && adjacent w k)).card≤4 := by decide +kernel

end BinaryTensorThree.Small
