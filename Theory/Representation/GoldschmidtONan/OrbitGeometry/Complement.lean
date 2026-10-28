module

public import Theory.Representation.GoldschmidtONan.OrbitGeometry.Suborbits

/-!
# The complement alternative for Goldschmidt–O'Nan pairs

If the fixed-space orbit has a nonfixed member and every such member is
disjoint from the moved space, its nonfixed members form one regular Y-orbit.
Thus the whole orbit has cardinality `|Y| + 1 = |[V,Y]|`. The Step 1 covering
formula shows that its nonzero vectors are exactly the complement of `[V,Y]`.
Since the actual X-orbit union is invariant, this also makes `[V,Y]` invariant.

The final theorem derives the required disjointness from the proved suborbit
dichotomy when no nonfixed orbit member lies in the moved space. This is the
all-second-suborbit branch of Step 2, proving alternative (iii) of GLS, Number 2,
Chapter C, Proposition 14.2 (`refs/KGroup/GLS2/ChapterC.tex`). The source's union
notation suppresses zero, and its first paragraph of Step 2 refers to (ii)
where the three stated conclusions identify (iii).
-/

public section
namespace Representation.GoldschmidtONan
open BinaryOffender RegularCyclicNormalClosure
variable {X V : Type*} [Group X] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) X V} {Y : Subgroup X}

/-- Two nonfixed orbit members disjoint from the moved space belong to the same
Y-suborbit: their nonzero suborbit unions coincide, and TI identifies members
sharing a nonzero vector. -/
theorem Input.exists_actor_map_eq_of_disjoint_moved [Finite X] [Finite V]
    (h : Input ρ Y) {W U : Submodule (ZMod 2) V}
    (hW : W ∈ fixedOrbit ρ Y) (hWF : W ≠ fixedSpace ρ Y)
    (hWD : Disjoint W (displacementSpan ρ Y ⊤))
    (hU : U ∈ fixedOrbit ρ Y) (hUF : U ≠ fixedSpace ρ Y)
    (hUD : Disjoint U (displacementSpan ρ Y ⊤)) :
    ∃ y : Y, W.map (ρ y) = U := by
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (h.orbit_ne_bot hU)
  have huF : u ∉ fixedSpace ρ Y := fun huf => hu0
    (Submodule.disjoint_def.mp (h.orbit_disjoint_fixed hU hUF) u hu huf)
  have huD : u ∉ displacementSpan ρ Y ⊤ := fun hud => hu0
    (Submodule.disjoint_def.mp hUD u hu hud)
  have hcover := h.suborbit_of_disjoint_moved hW hWF hWD
  have humem : u ∈ nonzeroSuborbitUnion ρ Y W := by
    rw [hcover]
    exact ⟨huF, huD⟩
  obtain ⟨_, y, hy⟩ := humem
  exact ⟨y, h.orbit_eq_of_common_nonzero (map_mem_fixedOrbit hW y) hU hy hu hu0⟩

/-- A nonfixed complement has distinct images under distinct elements of Y. -/
theorem Input.actor_map_injective_of_disjoint_moved [Finite X] [Finite V]
    (h : Input ρ Y) {W : Submodule (ZMod 2) V}
    (hW : W ∈ fixedOrbit ρ Y) (hWF : W ≠ fixedSpace ρ Y)
    (hWD : Disjoint W (displacementSpan ρ Y ⊤)) :
    Function.Injective (fun y : Y => W.map (ρ y)) := by
  intro a b hab
  change W.map (ρ a) = W.map (ρ b) at hab
  have hc : W.map (ρ ((b⁻¹ * a : Y) : X)) = W := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, orbit_map_mul, hab,
      ← orbit_map_mul, inv_mul_cancel, orbit_map_one]
  exact (inv_mul_eq_one.mp (h.stabilizer_eq_one_of_disjoint_moved hW hWF hWD _ hc)).symm

/-- If all nonfixed orbit members are complements, adjoining the fixed member
to one regular Y-orbit counts the whole fixed-space orbit. -/
theorem Input.card_fixedOrbit_of_disjoint_moved [Finite X] [Finite V]
    (h : Input ρ Y) {W : Submodule (ZMod 2) V}
    (hW : W ∈ fixedOrbit ρ Y) (hWF : W ≠ fixedSpace ρ Y)
    (hall : ∀ U ∈ fixedOrbit ρ Y, U ≠ fixedSpace ρ Y →
      Disjoint U (displacementSpan ρ Y ⊤)) :
    Nat.card (fixedOrbit ρ Y) = Nat.card Y + 1 := by
  let f : Option Y → fixedOrbit ρ Y
    | none => ⟨fixedSpace ρ Y, fixed_mem_fixedOrbit⟩
    | some y => ⟨W.map (ρ y), map_mem_fixedOrbit hW y⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have he := congrArg Subtype.val hab
    rcases a with _ | a <;> rcases b with _ | b
    · rfl
    · exact False.elim (map_actor_ne_fixed hWF b he.symm)
    · exact False.elim (map_actor_ne_fixed hWF a he)
    · exact congrArg some (h.actor_map_injective_of_disjoint_moved hW hWF (hall W hW hWF) he)
  have hsurj : Function.Surjective f := by
    intro U
    by_cases hUF : U.val = fixedSpace ρ Y
    · exact ⟨none, Subtype.ext hUF.symm⟩
    obtain ⟨y, hy⟩ := h.exists_actor_map_eq_of_disjoint_moved hW hWF (hall W hW hWF)
      U.property hUF (hall U U.property hUF)
    exact ⟨some y, Subtype.ext hy⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)]
  let := Fintype.ofFinite Y
  simp only [Nat.card_eq_fintype_card, Fintype.card_option]

/-- In the all-complement branch, the orbit's nonzero vectors cover precisely
the complement of the moved space. -/
theorem Input.nonzero_fixedOrbit_union_of_disjoint_moved [Finite X] [Finite V]
    (h : Input ρ Y) {W : Submodule (ZMod 2) V}
    (hW : W ∈ fixedOrbit ρ Y) (hWF : W ≠ fixedSpace ρ Y)
    (hall : ∀ U ∈ fixedOrbit ρ Y, U ≠ fixedSpace ρ Y →
      Disjoint U (displacementSpan ρ Y ⊤)) :
    {v : V | v ≠ 0 ∧ ∃ U ∈ fixedOrbit ρ Y, v ∈ U} =
      {v : V | v ∉ displacementSpan ρ Y ⊤} := by
  ext v
  constructor
  · rintro ⟨hv0, U, hU, hvU⟩ hvD
    have hd : Disjoint U (displacementSpan ρ Y ⊤) := by
      by_cases hUF : U = fixedSpace ρ Y
      · rw [hUF]
        exact h.split.disjoint
      · exact hall U hU hUF
    exact hv0 (Submodule.disjoint_def.mp hd v hvU hvD)
  · intro hvD
    have hv0 : v ≠ 0 := fun he => hvD (he ▸ (displacementSpan ρ Y ⊤).zero_mem)
    refine ⟨hv0, ?_⟩
    by_cases hvF : v ∈ fixedSpace ρ Y
    · exact ⟨fixedSpace ρ Y, fixed_mem_fixedOrbit, hvF⟩
    have hcover := h.suborbit_of_disjoint_moved hW hWF (hall W hW hWF)
    have hvmem : v ∈ nonzeroSuborbitUnion ρ Y W := by
      rw [hcover]
      exact ⟨hvF, hvD⟩
    obtain ⟨_, y, hy⟩ := hvmem
    exact ⟨W.map (ρ y), map_mem_fixedOrbit hW y, hy⟩

/-- A subspace whose complement is the nonzero union of the actual fixed-space
orbit is X-invariant. No invariance of that subspace is assumed. -/
theorem invariant_of_nonzero_fixedOrbit_union_compl
    {D : Submodule (ZMod 2) V}
    (hcover : {v : V | v ≠ 0 ∧ ∃ U ∈ fixedOrbit ρ Y, v ∈ U} = {v : V | v ∉ D}) :
    Invariant ρ D := by
  have hmem (x : X) {v : V} (hv : v ∈ D) : ρ x v ∈ D := by
    by_contra hn
    have hunion : ρ x v ∈ {v : V | v ≠ 0 ∧ ∃ U ∈ fixedOrbit ρ Y, v ∈ U} := by
      rw [hcover]
      exact hn
    obtain ⟨hvx0, U, hU, hvU⟩ := hunion
    have hv0 : v ≠ 0 := by
      intro he
      exact hvx0 (by rw [he, map_zero])
    have hvmap : v ∈ U.map (ρ x⁻¹) := by
      have hh := Submodule.mem_map_of_mem (f := ρ x⁻¹) hvU
      simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
        map_one, Module.End.one_apply] using hh
    have hvunion : v ∈ {v : V | v ≠ 0 ∧ ∃ U ∈ fixedOrbit ρ Y, v ∈ U} :=
      ⟨hv0, U.map (ρ x⁻¹), map_mem_fixedOrbit hU x⁻¹, hvmap⟩
    rw [hcover] at hvunion
    exact hvunion hv
  intro x
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact hmem x hv
  · intro v hv
    refine ⟨ρ x⁻¹ v, hmem x⁻¹ hv, ?_⟩
    simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
      map_one, Module.End.one_apply]

/-- The all-second-suborbit branch of Step 2 gives every clause of alternative
(iii): the exact orbit cardinality, the nonzero union, and moved-space invariance.
One nonfixed orbit member suffices. -/
theorem Input.complementCase_of_disjoint_moved [Finite X] [Finite V]
    (h : Input ρ Y) {W : Submodule (ZMod 2) V}
    (hW : W ∈ fixedOrbit ρ Y) (hWF : W ≠ fixedSpace ρ Y)
    (hall : ∀ U ∈ fixedOrbit ρ Y, U ≠ fixedSpace ρ Y →
      Disjoint U (displacementSpan ρ Y ⊤)) :
    ComplementCase ρ Y := by
  have hcover := h.nonzero_fixedOrbit_union_of_disjoint_moved hW hWF hall
  refine ⟨?_, hcover, invariant_of_nonzero_fixedOrbit_union_compl hcover⟩
  rw [h.card_fixedOrbit_of_disjoint_moved hW hWF hall, h.card_eq]
  let := Fintype.ofFinite (displacementSpan ρ Y ⊤)
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  exact Nat.sub_add_cancel (Nat.one_le_pow _ _ (by decide))

/-- Step 1 supplies the complement alternative whenever the orbit is not a
singleton and no nonfixed orbit member lies in the moved space. -/
theorem Input.complementCase_of_no_moved_orbit [Finite X] [Finite V]
    (h : Input ρ Y)
    (hne : fixedOrbit ρ Y ≠ {fixedSpace ρ Y})
    (hnot : ∀ U ∈ fixedOrbit ρ Y, U ≠ fixedSpace ρ Y →
      ¬ U ≤ displacementSpan ρ Y ⊤) : ComplementCase ρ Y := by
  have hex : ∃ W ∈ fixedOrbit ρ Y, W ≠ fixedSpace ρ Y := by
    by_contra hn
    apply hne
    ext W
    constructor
    · intro hW
      exact Set.mem_singleton_iff.mpr (Classical.byContradiction fun hWF => hn ⟨W, hW, hWF⟩)
    · rintro rfl
      exact fixed_mem_fixedOrbit
  obtain ⟨W, hW, hWF⟩ := hex
  apply h.complementCase_of_disjoint_moved hW hWF
  intro U hU hUF
  rcases h.suborbitGeometry U hU hUF with hfirst | hsecond
  · exact False.elim (hnot U hU hUF hfirst.1)
  · exact hsecond.1

end Representation.GoldschmidtONan
