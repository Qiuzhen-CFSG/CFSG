module
public import Theory.SpecificGroups.GL2.DeterminantCentralizer

/-!
# Two-group centralizers through faithful determinant models

Let a group D embed into GL2 over any field, with image in determinant
two-power level m. The centralizer in D of any noncommutative subgroup T
is a two-group. No finiteness, characteristic or Sylow assumption is needed.

Injectivity preserves the noncommutativity of the actual image of T. The
centralizer of T embeds into the intersection of that image's matrix
centralizer with determinant level m. The established determinant-centralizer
theorem makes the latter a two-group: its elements are scalar, and their
determinant condition bounds their orders by 2^(m+1). The two-group property
then pulls back along the faithful centralizer map.

Source: Alperin--Brauer--Gorenstein II.3 Proposition 3(iv), article pp27–28.
This common transfer applies to both original linear and unitary matrix
models, using their one- or two-stage subtype inclusions into GL2.
-/

namespace Matrix.GeneralLinearGroup

/-- A faithful determinant model has a two-group centralizer for every
noncommutative subgroup. -/
public theorem isPGroup_centralizer_of_injective_determinant_model
    {D F : Type*} [Group D] [Field F]
    (j : D →* GL (Fin 2) F) (hj : Function.Injective j)
    (m : ℕ) (hlevel : j.range ≤ determinantTwoPower F m)
    (T : Subgroup D) (hT : ¬ IsMulCommutative T) :
    IsPGroup 2 (Subgroup.centralizer (T : Set D)) := by
  let U := T.map j
  have hU : ¬ IsMulCommutative U := by
    intro h
    apply hT
    apply isMulCommutative_iff.mpr
    intro x y
    apply Subtype.ext
    apply hj
    have hh := congrArg Subtype.val (h.is_comm.comm
      (⟨j x.val, Subgroup.mem_map_of_mem j x.property⟩ : U)
      (⟨j y.val, Subgroup.mem_map_of_mem j y.property⟩ : U))
    change j x.val * j y.val = j y.val * j x.val at hh
    change j (x.val * y.val) = j (y.val * x.val)
    simpa only [map_mul] using hh
  let C := Subgroup.centralizer (T : Set D)
  let K := Subgroup.centralizer (U : Set (GL (Fin 2) F)) ⊓ determinantTwoPower F m
  have hmem (c : C) : j c.val ∈ K := by
    refine ⟨?_, hlevel ⟨c.val, rfl⟩⟩
    apply Subgroup.mem_centralizer_iff.mpr
    rintro _ ⟨t, ht, rfl⟩
    simpa only [map_mul] using congrArg j (Subgroup.mem_centralizer_iff.mp c.property t ht)
  let k : C →* K := (j.comp C.subtype).codRestrict K hmem
  apply (isPGroup_centralizer_inf_determinantTwoPower U hU m).of_injective k
  intro x y h
  exact Subtype.ext (hj (congrArg Subtype.val h))
end Matrix.GeneralLinearGroup
