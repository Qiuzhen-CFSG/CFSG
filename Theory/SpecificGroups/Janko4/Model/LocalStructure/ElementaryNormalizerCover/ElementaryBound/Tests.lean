module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ElementaryBound.FastAction

/-! Boolean comparison tests for the native tables; their meaning is proved in `Checks`. -/
@[expose] public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.ElementaryBound
open Janko4.LocalStructure.SylowCore.FiniteBoundCertificate
open Janko4.LocalStructure.SylowCore.FiniteBoundCertificate.NormalWeights

def actor (k : Fin 12) (a : Fin 16) : Fin 192 := ⟨k.val * 16 + a.val, by omega⟩

theorem actor_block_offset (v : Fin 192) : actor (block v) (offset v) = v := by
  apply Fin.ext
  change v.val / 16 * 16 + v.val % 16 = v.val
  omega

def pointCheck (v : Fin 192) : Bool :=
  (List.finRange 24).all (fun p => point v p == perm (vertexIndex v) p)

def rowCheck (v : Fin 192) : Bool :=
  (List.finRange 11).all (fun i => row v i == rows (vertexIndex v) i)

def compatibleCheck (v w : Fin 192) : Bool :=
  compatible v w || (point v (point w 0) != point w (point v 0)) ||
    (point v (point w 1) != point w (point v 1)) ||
    (point v (point w 2) != point w (point v 2))

def codeCheck (v : Fin 192) : Bool := vertexCode (vertexIndex v) == v

def squareCheck (i : Index) : Bool := (List.finRange 3).all (fun p =>
  perm i (perm i (p.castLE (by decide))) == p.castLE (by decide))

def coverageCheck (i : Index) : Bool :=
  !squareCheck i || decide (vertexIndex (vertexCode i) = i)

end Janko4.LocalStructure.ElementaryNormalizerCover.ElementaryBound
