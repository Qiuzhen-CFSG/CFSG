module

public import Theory.Representation.FirstCohomologyG2Natural.BinaryPair
public import Theory.Representation.SubrepresentationLattice

/-!
# Binary coordinates and irreducibility of the natural G₂(2)′ module

The six off-diagonal coordinates identify the trace-zero octonion quotient
with `F₂⁶`. The two explicit commutators from `BinaryPair` act by the displayed
linear formulas. For each of the 63 nonzero vectors, a word of length at most
nine sends the first coordinate vector to it. Lean checks every entry of this
finite word table in the kernel. This proves transitivity and irreducibility
for the actual derived group, without assuming that these two elements generate.

These are concrete target-module facts used in Aschbacher--Smith G.9.3(10),
printed pp.354,356--357. They do not classify arbitrary degree-six modules.
The octonion and root conventions come from the attributed ATLAS ports imported
by `BinaryPair`; no additional ATLAS source is copied here.
-/

@[expose] public section

namespace Atlas.G2.Natural.Binary
open Atlas.G2.Natural
abbrev Six := Fin 6 → ZMod 2
def stepA (x : Six) : Six := ![x 0+x 2+x 5,x 1+x 3+x 4+x 5,x 2+x 4,x 3+x 5,x 4,x 5]
def stepB (x : Six) : Six := ![x 3,x 5,x 1,x 4,x 0,x 2]
private def wordAction : List Bool → Six → Six
  | [], x => x
  | b :: w, x => if b then stepB (wordAction w x) else stepA (wordAction w x)
private def seed : Six := ![1,0,0,0,0,0]
private def decode (n : Fin 64) : Six := fun i => (n.val / 2^i.val : ℕ)
private def encode (x : Six) : Fin 64 := ⟨(x 0).val + 2*(x 1).val + 4*(x 2).val + 8*(x 3).val + 16*(x 4).val + 32*(x 5).val, by
  have h0 := ZMod.val_lt (x 0); have h1 := ZMod.val_lt (x 1); have h2 := ZMod.val_lt (x 2)
  have h3 := ZMod.val_lt (x 3); have h4 := ZMod.val_lt (x 4); have h5 := ZMod.val_lt (x 5)
  omega⟩
private def orbitWord : Fin 64 → List Bool := ![
  [],
  [],
  [true,true,false,true,false,true,true],
  [true,false,true,true,false,true],
  [false,true,false,true,true],
  [true,false,true,true],
  [true,true,false,true,false,true],
  [false,true,true,false,true,false,true],
  [true,true],
  [true,true,false,false,true],
  [false,true,true],
  [false,true,true,false,false,true],
  [true,true,false,false,true,true,false,true],
  [false,true,false,true,false,false,false,true],
  [true,false,true,false,false,false,true],
  [true,false,true,true,false,false,true,false,true],
  [true],
  [false,false,true],
  [true,false,false,true,true,false,true],
  [true,true,false,true,false,false,true],
  [true,true,false,true,true,false,true],
  [true,false,true,true,false,false,true],
  [false,true],
  [false,false,false,true],
  [true,false,false,true],
  [false,false,true,false,false,true],
  [true,false,false,false,true,false,false,false,true],
  [true,true,false,false,false,true,false,false,true],
  [false,true,false,false,true],
  [false,false,false,true,false,false,true],
  [true,false,false,true,true,false,true,true],
  [true,true,false,true,true,false,true,true],
  [true,false,true,false,true,true],
  [false,false,true,true,false,true],
  [true,false,true,false,true],
  [true,true,false,true],
  [false,true,false,true],
  [true,true,false,true,false,false,false,true],
  [false,false,false,true,false,true],
  [true,false,false,true,false,true],
  [false,true,true,false,true],
  [true,false,true,false,false,true],
  [false,false,false,true,true,false,true],
  [true,true,false,false,false,true],
  [true,false,true],
  [false,true,false,false,true,false,true],
  [false,false,true,false,true],
  [false,true,true,false,true,false,false,false,true],
  [true,true,false,true,true],
  [false,false,false,true,false,false,false,true],
  [false,true,false,false,false,true],
  [false,false,true,true,false,true,true],
  [true,false,true,true,false,true,false,true],
  [false,false,true,true,false,false,true,false,true],
  [true,true,false,false,true,false,true],
  [false,true,true,false,true,true,false,false,true],
  [true,true,false,true,true,false,false,true],
  [true,false,false,false,true,false,false,true],
  [false,true,true,false,false,true,false,true],
  [true,false,true,true,false,true,true],
  [true,false,false,false,true],
  [false,true,true,false,true,true],
  [false,false,false,true,true,false,true,true],
  [false,false,true,false,false,false,true]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem decode_encode : ∀ x : Six, decode (encode x) = x := by
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem orbitWord_correct : ∀ n : Fin 64, n ≠ 0 → wordAction (orbitWord n) seed = decode n := by
  decide +kernel
private theorem exists_word (x : Six) (hx : x ≠ 0) : ∃ w : List Bool, wordAction w seed = x := by
  refine ⟨orbitWord (encode x), (orbitWord_correct _ ?_).trans (decode_encode x)⟩
  intro hz
  apply hx
  rw [← decode_encode x, hz]
  ext i
  change ((0 / 2^i.val : ℕ) : ZMod 2) = 0
  simp
end Atlas.G2.Natural.Binary

namespace Atlas.G2.Natural.Binary
open Atlas.G2.Natural
noncomputable section
abbrev Derived := commutator (Atlas.G2.Model (ZMod 2))
abbrev QuotientSpace := Atlas.G2.Natural.Space (ZMod 2)

/-- The six off-diagonal coordinates give a linear equivalence, not just an
embedding, of the actual octonion quotient. -/
def coordinatesEquiv : QuotientSpace ≃ₗ[ZMod 2] Six :=
  LinearEquiv.ofBijective (binaryCoordinates (ZMod 2))
    ⟨binaryCoordinates_injective _,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp
        (binaryCoordinates_injective _)⟩

theorem finrank_natural : Module.finrank (ZMod 2) QuotientSpace = 6 :=
  coordinatesEquiv.finrank_eq.trans (by simp)

theorem finiteDimensional_natural : FiniteDimensional (ZMod 2) QuotientSpace :=
  Module.Finite.equiv coordinatesEquiv.symm

/-- The actual derived octonion action expressed on binary six-tuples. -/
def coordinateAction : Representation (ZMod 2) Derived Six :=
  coordinatesEquiv.conjRingEquiv.toMonoidHom.comp (derivedAction (ZMod 2))

/-- The coordinate equivalence intertwines the entire derived group. -/
def coordinateEquiv : (derivedAction (ZMod 2)).Equiv coordinateAction :=
  Representation.Equiv.mk coordinatesEquiv (by
    intro g
    apply LinearMap.ext
    intro v
    change coordinatesEquiv (derivedAction (ZMod 2) g v) =
      coordinatesEquiv (derivedAction (ZMod 2) g (coordinatesEquiv.symm (coordinatesEquiv v)))
    rw [LinearEquiv.symm_apply_apply])

/-- Pointwise compatibility, also usable when the same additive quotient is
endowed with its scalar-restricted module structure. -/
theorem coordinatesEquiv_action (g : Derived) (v : QuotientSpace) :
    coordinatesEquiv (derivedAction (ZMod 2) g v) =
      coordinateAction g (coordinatesEquiv v) :=
  Representation.IntertwiningMap.isIntertwining _ _ coordinateEquiv.toIntertwiningMap g v

private def wordElement : List Bool → Derived
  | [] => 1
  | b :: w => (if b then binaryB (ZMod 2) else binaryA (ZMod 2)) * wordElement w

private theorem coordinates_word (w : List Bool) (v : QuotientSpace) :
    coordinatesEquiv (derivedAction (ZMod 2) (wordElement w) v) =
      wordAction w (coordinatesEquiv v) := by
  induction w with
  | nil => simp [wordElement, wordAction]
  | cons b w ih =>
    cases b
    · simp only [wordElement, Bool.false_eq_true, if_false, map_mul, Module.End.mul_apply]
      change binaryCoordinates (ZMod 2) (derivedAction (ZMod 2) (binaryA (ZMod 2)) _) = _
      rw [binaryCoordinates_binaryA]
      change stepA (coordinatesEquiv (derivedAction (ZMod 2) (wordElement w) v)) = _
      rw [ih]
      rfl
    · simp only [wordElement, if_true, map_mul, Module.End.mul_apply]
      change binaryCoordinates (ZMod 2) (derivedAction (ZMod 2) (binaryB (ZMod 2)) _) = _
      rw [binaryCoordinates_binaryB]
      change stepB (coordinatesEquiv (derivedAction (ZMod 2) (wordElement w) v)) = _
      rw [ih]
      rfl

private theorem coordinateAction_word (w : List Bool) (v : Six) :
    coordinateAction (wordElement w) v = wordAction w v := by
  change coordinatesEquiv (derivedAction (ZMod 2) (wordElement w)
    (coordinatesEquiv.symm v)) = _
  rw [coordinates_word, LinearEquiv.apply_symm_apply]

private theorem exists_from_seed (v : QuotientSpace) (hv : v ≠ 0) :
    ∃ g : Derived, derivedAction (ZMod 2) g (coordinatesEquiv.symm seed) = v := by
  have hv' : coordinatesEquiv v ≠ 0 := fun h => hv (coordinatesEquiv.map_eq_zero_iff.mp h)
  obtain ⟨w, hw⟩ := exists_word (coordinatesEquiv v) hv'
  refine ⟨wordElement w, coordinatesEquiv.injective ?_⟩
  rw [coordinates_word, LinearEquiv.apply_symm_apply, hw]

/-- First commutator action in the six coordinate positions. -/
theorem coordinateAction_binaryA (v : Six) :
    coordinateAction (binaryA (ZMod 2)) v = stepA v := by
  simpa [wordElement, wordAction] using coordinateAction_word [false] v

/-- Second commutator action in the six coordinate positions. -/
theorem coordinateAction_binaryB (v : Six) :
    coordinateAction (binaryB (ZMod 2)) v = stepB v := by
  simpa [wordElement, wordAction] using coordinateAction_word [true] v

/-- The derived group is transitive on nonzero natural vectors. The orbit
calculation uses only two actual commutators, without a generation assumption. -/
theorem natural_transitive {v w : QuotientSpace} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : Derived, derivedAction (ZMod 2) g v = w := by
  obtain ⟨a, ha⟩ := exists_from_seed v hv
  obtain ⟨b, hb⟩ := exists_from_seed w hw
  refine ⟨b * a⁻¹, ?_⟩
  have hc : derivedAction (ZMod 2) a⁻¹
      (derivedAction (ZMod 2) a (coordinatesEquiv.symm seed)) =
      coordinatesEquiv.symm seed := by
    change (derivedAction (ZMod 2) a⁻¹ * derivedAction (ZMod 2) a)
      (coordinatesEquiv.symm seed) = _
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  rw [map_mul, Module.End.mul_apply, ← ha, hc]
  exact hb

/-- Irreducibility of the actual binary derived natural action. -/
theorem natural_irreducible : Representation.IsIrreducible (derivedAction (ZMod 2)) := by
  let : Nontrivial QuotientSpace := Module.nontrivial_of_finrank_pos
    (show 0 < Module.finrank (ZMod 2) QuotientSpace by rw [finrank_natural]; decide)
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  have hS' : S.toSubmodule ≠ ⊥ := fun h => hS (Subrepresentation.toSubmodule_injective h)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS'
  apply le_antisymm le_top
  intro w _
  by_cases hw : w = 0
  · subst w
    exact S.toSubmodule.zero_mem
  · obtain ⟨g, rfl⟩ := natural_transitive hv0 hw
    exact S.apply_mem_toSubmodule g hv
end
end Atlas.G2.Natural.Binary
