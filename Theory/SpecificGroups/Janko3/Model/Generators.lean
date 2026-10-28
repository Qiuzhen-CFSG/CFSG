module

public import Theory.SpecificGroups.Janko3.Model.AtlasData

/-!
# Certified permutations for J₃

The ATLAS degree-6156 tables define permutations: `a` is an involution and `b`
has cube one. Both identities are checked on all 6156 letters by the kernel.
Source: the ATLAS representation `J3G1-p6156B0`, documented in `AtlasData`.
-/

namespace Sporadic.Janko3

set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-- Boolean enumeration of the letters, avoiding nested finite quantifiers. -/
@[expose] public def checkLetters (f : Fin 6156 → Bool) : Bool :=
  (List.range 6156).all (fun i => f ⟨i % 6156, Nat.mod_lt _ (by decide)⟩)

/-- Soundness of the exhaustive letter check. -/
public theorem allLetters (P : Fin 6156 → Prop) [DecidablePred P]
    (h : checkLetters (fun i => decide (P i)) = true) : ∀ i, P i := by
  intro i
  have h' := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [Nat.mod_eq_of_lt i.isLt, decide_eq_true_eq] using h'

public theorem atlasAFun_involutive : Function.Involutive atlasAFun := by
  apply allLetters
  decide +kernel

public theorem atlasBFun_cube (i : Fin 6156) :
    atlasBFun (atlasBFun (atlasBFun i)) = i := by
  revert i
  apply allLetters
  decide +kernel

/-- The ATLAS standard involution, acting on the left. -/
@[expose] public def atlasA : Equiv.Perm (Fin 6156) where
  toFun := atlasAFun
  invFun := atlasAFun
  left_inv := atlasAFun_involutive
  right_inv := atlasAFun_involutive

/-- The ATLAS standard element of order three, acting on the left. -/
@[expose] public def atlasB : Equiv.Perm (Fin 6156) where
  toFun := atlasBFun
  invFun := fun i => atlasBFun (atlasBFun i)
  left_inv := atlasBFun_cube
  right_inv := atlasBFun_cube

public theorem atlasA_sq : atlasA ^ 2 = 1 := by
  apply Equiv.ext
  exact atlasAFun_involutive

public theorem atlasB_cube : atlasB ^ 3 = 1 := by
  apply Equiv.ext
  exact atlasBFun_cube

end Sporadic.Janko3
