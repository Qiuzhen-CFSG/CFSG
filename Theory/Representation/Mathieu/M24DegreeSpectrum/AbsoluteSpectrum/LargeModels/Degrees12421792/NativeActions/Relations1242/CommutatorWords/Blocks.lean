module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.Arithmetic

/-!
# Assembly of bounded degree-1242 row certificates

The checked one-coordinate shortcut and sequential XOR calculation are those
of `Relations1242.Arithmetic`. Independent row blocks concatenate to a full
matrix product. `FirstProduct` applies this to the unchanged ATLAS generators.
Source and conventions: `source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords

def checkChunks : List (List Nat) → List Nat → List (List Nat) →
    List (List (Option Nat)) → Bool
  | [], _, [], [] => true
  | a::as, bs, c::cs, h::hs => check a bs c h && checkChunks as bs cs hs
  | _, _, _, _ => false

theorem checkChunks_sound (as : List (List Nat)) (bs : List Nat)
    (cs : List (List Nat)) (hs : List (List (Option Nat)))
    (h : checkChunks as bs cs hs = true) :
    check as.flatten bs cs.flatten hs.flatten = true := by
  induction as generalizing cs hs with
  | nil => cases cs <;> cases hs <;> simp_all [checkChunks, check]
  | cons a as ih =>
    cases cs with
    | nil => cases hs <;> simp [checkChunks] at h
    | cons c cs =>
      cases hs with
      | nil => simp [checkChunks] at h
      | cons hint hs =>
        simp only [checkChunks, Bool.and_eq_true] at h
        exact check_append _ _ _ _ _ _ _ h.1 (ih cs hs h.2)

theorem product_of_chunks (as cs : List (List Nat)) (bs : List Nat)
    (hs : List (List (Option Nat)))
    (ha : as.flatten.length = 1242) (hb : bs.length = 1242)
    (h : checkChunks as bs cs hs = true) :
    Thompson.BinaryMatrix.decode 1242 as.flatten.toArray *
      Thompson.BinaryMatrix.decode 1242 bs.toArray =
      Thompson.BinaryMatrix.decode 1242 cs.flatten.toArray :=
  product 1242 _ _ _ _ ha hb (checkChunks_sound as bs cs hs h)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords
