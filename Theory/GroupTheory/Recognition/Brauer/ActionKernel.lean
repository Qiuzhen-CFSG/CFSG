module
public import Theory.GroupTheory.Recognition.Brauer.Action
public import Theory.GroupTheory.Recognition.Brauer.PairedStabilizer

/-!
# The kernel of Brauer's collineation representation

The actual conjugation action on both block families has kernel equal to
the centralizer of all involutions, equivalently the intersection of their
individual centralizers. This is Brauer, *On finite Desarguesian planes I*,
(4B), article page 123, and supplies the normal subgroup in (4C) and (4D).

An element of the kernel fixes the point and line associated with each
involution, so the paired-stabilizer theorem (4A) makes it centralize that
involution. Conversely, all members of a point or line block are involutions;
centralizing every involution therefore fixes both block families elementwise.
The proof uses the existing representation's public kernel criterion and
the original seed actions, without coordinates or a faithfulness assumption.
-/

open scoped Pointwise

namespace Theory.GroupTheory.BrauerPlaneSeed

private theorem smul_set_eq_of_centralizes_involutions
    {G : Type*} [Group G] (g : G)
    (hg : g ∈ Subgroup.centralizer {x : G | orderOf x = 2})
    (s : Set G) (hs : ∀ x ∈ s, orderOf x = 2) :
    ConjAct.toConjAct g • s = s := by
  have hfix (x : G) (hx : x ∈ s) : ConjAct.toConjAct g • x = x := by
    exact mul_inv_eq_iff_eq_mul.mpr
      ((Subgroup.mem_centralizer_iff.mp hg x (hs x hx)).symm)
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hx
    rwa [hfix y hy]
  · intro hx
    exact Set.mem_smul_set.mpr ⟨x, hx, hfix x hx⟩

public theorem ker_collineationRepresentation
    {G : Type*} [Group G] [Finite G] (S : BrauerPlaneSeed G) :
    S.collineationRepresentation.ker =
      Subgroup.centralizer {x : G | orderOf x = 2} := by
  ext g
  rw [S.mem_collineationRepresentation_ker_iff]
  constructor
  · rintro ⟨hp, hl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    exact (Subgroup.mem_centralizer_singleton_iff.mp
      ((S.fixes_point_and_line_iff_mem_centralizer x hx (ConjAct.toConjAct g)).mp
        ⟨hp _, hl _⟩)).symm
  · intro hg
    constructor
    · intro p
      apply Subtype.ext
      exact smul_set_eq_of_centralizes_involutions g hg (p : Set G)
        (fun _ hx => S.orderOf_mem_point p hx)
    · intro l
      apply Subtype.ext
      exact smul_set_eq_of_centralizes_involutions g hg (l : Set G)
        (fun _ hx => S.orderOf_mem_line l hx)

end Theory.GroupTheory.BrauerPlaneSeed
