module

public import Theory.Representation.G2.RestrictedModules.Steinberg.BinaryOrbit
public import Theory.Representation.G2.RestrictedModules.Steinberg.OrbitClosure
public import Theory.Representation.AbsolutelyIrreducible

/-!
# The 64-dimensional absolutely irreducible level-two G₂ Steinberg factor

The binary-orbit calculation and full-group stability identify the concrete
highest-weight orbit carrier with the span of its 64 independent translates.
The common fixed space of the six positive root groups is its highest line.
Every nonzero invariant subspace contains a nonzero vector fixed by the actual
binary unipotent group, hence contains the highest vector and its whole orbit.
This proves irreducibility over every characteristic-two field.

An intertwining endomorphism preserves the highest line, so cyclicity makes it
scalar on the entire module. The scalar-commutant criterion then proves absolute
irreducibility, with no assumption that the field is finite. In particular this
constructs the requested factor for every finite field of order `2^n`, `n ≥ 2`.

Source: GLS3, 2.8.6, 2.8.7 and Example 2.8.10(g), as used in Aschbacher--Smith
G.9.3, printed pp.354,356--357. This is the algebraic Steinberg factor of level
two, of dimension 64; it is not the dimension-`|F|^6` Steinberg module of G₂(F).
-/

@[expose] public noncomputable section
open scoped BigOperators
namespace Atlas.G2.Restricted.Steinberg
variable (F : Type*) [Field F] [CharP F 2]

/-- The finite binary span is exactly the actual highest-weight orbit carrier. -/
theorem binarySpan_eq_orbitSpan : binarySpan F = (orbitSpan F).toSubmodule := by
  apply le_antisymm (binarySpan_le_orbitSpan F)
  exact (orbitSpan_le_iff F (binarySubrepresentation F)).mpr (seed_mem_binarySpan F)

/-- A basis of the concrete Steinberg carrier, indexed by six binary parameters. -/
def basis : Module.Basis BinaryIndex F (Space F) :=
  (binaryBasis F).map (LinearEquiv.ofEq _ _ (binarySpan_eq_orbitSpan F))

@[simp] theorem basis_val (t : BinaryIndex) :
    (basis F t).val = binaryOrbitVector F t := by
  simp [basis]

/-- Every basis vector is an actual group translate of the chosen highest vector. -/
theorem basis_eq_action (t : BinaryIndex) :
    basis F t = action F (unipotentProduct (binaryParameters F t) * longestWeyl F)
      (highestVector F) := Subtype.ext (basis_val F t)

/-- The prime-field positive unipotent group permutes the basis regularly. -/
theorem action_binaryUnipotent_basis (g : BinaryUnipotent) (t : BinaryIndex) :
    action F (binaryUnipotentHom F g) (basis F t) =
      basis F (binaryTranslation g t) := by
  obtain ⟨s, rfl⟩ := binaryIndexEquiv.surjective g
  apply Subtype.ext
  simpa only [action_val, basis_val, binaryUnipotentHom_index,
    binaryUnipotentAction_index] using
    binaryUnipotentAction_binaryOrbitVector F (binaryIndexEquiv s) t

/-- Dimension of the level-two Steinberg factor, over any characteristic-two field. -/
theorem finrank_space : Module.finrank F (Space F) = 64 := by
  rw [Module.finrank_eq_card_basis (basis F)]
  simp [BinaryIndex]

/-- The six binary root elements already cut out the highest line. -/
theorem fixed_binary_roots_iff (v : Space F) :
    (action F (rootA 1) v = v ∧ action F (rootB 1) v = v ∧
      action F (rootC 1) v = v ∧ action F (rootD 1) v = v ∧
      action F (rootE 1) v = v ∧ action F (rootF 1) v = v) ↔
    ∃ c : F, v = c • highestVector F := by
  have hv : v.val ∈ binarySpan F := by rw [binarySpan_eq_orbitSpan]; exact v.property
  constructor
  · rintro ⟨hA, hB, hC, hD, hE, hF⟩
    obtain ⟨c, hc⟩ := (binarySpan_fixed_roots_iff F v.val hv).mp
      ⟨congrArg Subtype.val hA, congrArg Subtype.val hB, congrArg Subtype.val hC,
        congrArg Subtype.val hD, congrArg Subtype.val hE, congrArg Subtype.val hF⟩
    exact ⟨c, Subtype.ext hc⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨hA, hB, hC, hD, hE, hF⟩ := highestVector_fixed_roots F 1
    simp only [map_smul, hA, hB, hC, hD, hE, hF, and_self]

/-- Membership in the specified highest line is being a scalar multiple of its seed. -/
theorem mem_highestLine_iff (v : Space F) :
    v ∈ highestLine F ↔ ∃ c : F, v = c • highestVector F := by
  simp only [highestLine, Submodule.mem_span_singleton, eq_comm]

/-- The highest line has dimension one. -/
theorem finrank_highestLine : Module.finrank F (highestLine F) = 1 :=
  finrank_span_singleton (K := F) (V := Space F) (highestVector_ne_zero F)

/-- The full simultaneous positive-root fixed space is exactly the highest line. -/
theorem fixed_roots_iff_mem_highestLine (v : Space F) :
    (∀ a : F, action F (rootA a) v = v ∧ action F (rootB a) v = v ∧
      action F (rootC a) v = v ∧ action F (rootD a) v = v ∧
      action F (rootE a) v = v ∧ action F (rootF a) v = v) ↔
    v ∈ highestLine F := by
  rw [mem_highestLine_iff]
  constructor
  · exact fun h => (fixed_binary_roots_iff F v).mp (h 1)
  · rintro ⟨c, rfl⟩ a
    obtain ⟨hA, hB, hC, hD, hE, hF⟩ := highestVector_fixed_roots F a
    simp only [map_smul, hA, hB, hC, hD, hE, hF, and_self]

/-- Cyclicity: an invariant subspace containing the highest vector is the whole carrier. -/
theorem eq_top_of_highestVector_mem (W : Subrepresentation (action F))
    (h : highestVector F ∈ W) : W = ⊤ := by
  apply top_unique
  intro v _
  rw [← (basis F).sum_repr v]
  exact W.toSubmodule.sum_mem fun t _ => W.toSubmodule.smul_mem _
    (by rw [basis_eq_action]; exact W.apply_mem_toSubmodule _ h)

private theorem fixed_binaryGroup_iff (v : Space F) :
    (∀ g : BinaryUnipotent, action F (binaryUnipotentHom F g) v = v) ↔
      ∃ c : F, v = c • highestVector F := by
  constructor
  · intro h
    apply (fixed_binary_roots_iff F v).mp
    have hr (i : Fin 6) := h (binaryRoot i)
    simp only [binaryUnipotentHom_root] at hr
    exact ⟨hr 0, hr 1, hr 2, hr 3, hr 4, hr 5⟩
  · rintro ⟨c, rfl⟩ g
    obtain ⟨t, rfl⟩ := binaryIndexEquiv.surjective g
    rw [binaryUnipotentHom_index, map_smul, highestVector_fixed_unipotentProduct]

/-- Every nonzero invariant subspace contains the unique binary-unipotent fixed line. -/
theorem irreducible : Representation.IsIrreducible (V := Space F) (action F) := by
  apply IsSimpleOrder.of_forall_eq_top
  intro W hW
  have hn : W.toSubmodule ≠ ⊥ := fun h => hW (Subrepresentation.toSubmodule_injective h)
  let : Nontrivial W.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hn
  let : AddCommGroup W.toSubmodule := Submodule.addCommGroup (R := F) (M := Space F) W.toSubmodule
  have hc : ringChar F ≠ 0 := by rw [ringChar.eq F 2]; decide
  have hp : IsPGroup (ringChar F) BinaryUnipotent := by
    rw [ringChar.eq F 2]
    exact binaryUnipotent_isTwoGroup
  obtain ⟨v, hv, hfix⟩ := Representation.pGroup_fix_nonzero_vector (F := F) (G := BinaryUnipotent)
    (V := W.toSubmodule) hc hp
    (W.toRepresentation.comp (binaryUnipotentHom F))
  have hfix' (g : BinaryUnipotent) : action F (binaryUnipotentHom F g) v.val = v.val :=
    congrArg Subtype.val (hfix g)
  obtain ⟨c, he⟩ := (fixed_binaryGroup_iff F v.val).mp hfix'
  have hc0 : c ≠ 0 := by
    intro h
    apply hv
    apply Subtype.ext
    change v.val = (0 : Space F)
    simpa only [h, zero_smul] using he
  apply eq_top_of_highestVector_mem F W
  apply (W.toSubmodule.smul_mem_iff hc0).mp
  rw [← he]
  exact v.property

/-- The commutant is scalar, by the highest-line calculation and cyclicity. -/
theorem endomorphism_scalar (f : Representation.End (action F)) :
    ∃ c : F, f = algebraMap F (Representation.End (action F)) c := by
  have hf : ∃ c : F, f (highestVector F) = c • highestVector F := by
    apply (fixed_binaryGroup_iff F _).mp
    intro g
    rw [← f.isIntertwining]
    have hh := (fixed_binaryGroup_iff F (highestVector F)).mpr ⟨1, by simp⟩ g
    rw [hh]
  obtain ⟨c, hc⟩ := hf
  refine ⟨c, ?_⟩
  apply Representation.IntertwiningMap.ext
  apply (basis F).ext
  intro t
  change f (basis F t) = c • basis F t
  rw [basis_eq_action, f.isIntertwining, hc, map_smul]

/-- Absolute irreducibility of the actual 64-dimensional action. -/
theorem absolutelyIrreducible : Representation.IsAbsolutelyIrreducible (V := Space F) (action F) := by
  let : Representation.IsIrreducible (V := Space F) (action F) := irreducible F
  apply (Representation.isAbsolutelyIrreducible_iff_surjective (V := Space F) (action F)).mpr
  intro f
  obtain ⟨c, hc⟩ := endomorphism_scalar F f
  exact ⟨c, hc.symm⟩

end Atlas.G2.Restricted.Steinberg
