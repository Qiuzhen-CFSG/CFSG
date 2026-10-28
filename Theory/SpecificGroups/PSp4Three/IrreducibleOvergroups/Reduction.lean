module

public import Theory.SpecificGroups.PSp4Three.SectionReduction
public import Theory.ElementaryAbelian.Extraspecial
public import Theory.PGroupCore
public import Mathlib.Order.Atoms.Finite
public import Mathlib.Data.SetLike.Fintype

/-!
# Maximal overgroups and full symplectic preimages

Every proper irreducible subgroup of PSp₄(3) lies in a maximal irreducible
subgroup. Irreducibility refers throughout to the four-dimensional module
of the full inverse image in Sp₄(3). The projection onto the projective
subgroup is surjective and has central kernel.

The extraspecial-core condition below describes the actual two-core of that
inverse image, including its order, elementary rank and relative
self-centralization. It does not assert that any subgroup satisfies the
condition. Establishing the maximal-subgroup alternatives remains a separate
obligation.

Source application: Aschbacher–Smith, Theorem 0.1.2(4), condition K,
printed pp.4 and 482 of `refs/quasithin.pdf`.
-/

namespace Matrix.PSp4Three

/-- The full symplectic inverse image, including the ambient scalar kernel. -/
@[expose] public def fullPreimage (U : Subgroup (PSp 2 (ZMod 3))) :
    Subgroup (Sp 2 (ZMod 3)) := U.comap projection

/-- Restriction of the ambient central quotient onto the given subgroup. -/
@[expose] public def preimageProjection (U : Subgroup (PSp 2 (ZMod 3))) :
    fullPreimage U →* U := projection.subgroupComap U

public theorem preimageProjection_surjective (U : Subgroup (PSp 2 (ZMod 3))) :
    Function.Surjective (preimageProjection U) :=
  projection.subgroupComap_surjective_of_surjective U projection_surjective

public theorem preimageProjection_ker_le_center (U : Subgroup (PSp 2 (ZMod 3))) :
    (preimageProjection U).ker ≤ Subgroup.center (fullPreimage U) := by
  intro x hx
  have hx' : x.val ∈ Subgroup.center (Sp 2 (ZMod 3)) := by
    rw [← projection_kernel]
    exact congrArg Subtype.val hx
  apply Subgroup.mem_center_iff.mpr
  intro y
  exact Subtype.ext (Subgroup.mem_center_iff.mp hx' y.val)

/-- A concrete condition on the two-core of the full inverse image.
The centralizer is taken inside that inverse image, not in the ambient group. -/
@[expose] public def HasExtraspecialLiftCore (U : Subgroup (PSp 2 (ZMod 3))) : Prop :=
  IsExtraspecial 2 (pCore 2 (fullPreimage U)) ∧
    Nat.card (pCore 2 (fullPreimage U)) = 32 ∧
    (∀ E : Subgroup (pCore 2 (fullPreimage U)),
      IsElementaryAbelian 2 E → Nat.card E < 8) ∧
    Subgroup.centralizer (pCore 2 (fullPreimage U) : Set (fullPreimage U)) ≤
      pCore 2 (fullPreimage U)

public theorem HasInvariantSubspace.of_le {U M : Subgroup (PSp 2 (ZMod 3))}
    (hUM : U ≤ M) (hM : HasInvariantSubspace M) : HasInvariantSubspace U := by
  obtain ⟨W, hW0, hW1, hW⟩ := hM
  exact ⟨W, hW0, hW1, fun g hg => hW g (hUM hg)⟩

/-- Passing to a maximal proper overgroup preserves irreducibility. -/
public theorem exists_irreducible_coatom (U : Subgroup (PSp 2 (ZMod 3)))
    (hU : U ≠ ⊤) (hred : ¬ HasInvariantSubspace U) :
    ∃ M : Subgroup (PSp 2 (ZMod 3)), IsCoatom M ∧ U ≤ M ∧
      ¬ HasInvariantSubspace M := by
  obtain ⟨M, hM, hUM⟩ := (eq_top_or_exists_le_coatom U).resolve_left hU
  exact ⟨M, hM, hUM, fun h => hred (h.of_le hUM)⟩

end Matrix.PSp4Three
