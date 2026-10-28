module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal

/-!
# Extending an embedded projective special unitary subgroup

The natural inclusion PSU(J) → PGU(J) is the inclusion of their actual
images in PGL. Unitary conjugation preserves the determinant-one subgroup,
so PGU(J) normalizes PSU(J). Consequently, any embedding of PGU(J) whose
PSU(J) image is S lands in the ambient normalizer of S.

`ProjectiveExtension` records only this embedding and its prescribed socle
image. It does not assume that its image is normal in an overgroup, that
the normalizer is proper, or that any quotient has order two. The two
problems at the end separate constructing an extension from calculating
its normalizer; neither problem is asserted here to have a solution.

Source: Malle, J. Algebra 139 (1991), 52–69,
DOI 10.1016/0021-8693(91)90283-E. The unconditional list in the proof of
Theorem 5 of Himstedt–Nguyen–Tiep, arXiv:0910.4758, p.3, distinguishes
SU₃(q):2 (case 1) from PGU₃(q):2 (case 7). Only the latter is relevant here.
-/

public section

namespace ReeF4.MaximalSubgroups.SimpleNormal

open Subgroup Matrix BenderSuzuki.MatrixGroups

/-- The actual inclusion of the special projective image in the full
projective unitary image. -/
@[expose] def projectiveSpecialInclusion {F : Type*} [Field F]
    (J : HermitianForm 3 F) :
    ProjectiveSpecialUnitaryMatrixGroup J →*
      J.unitarySubgroup.map ProjGenLinGroup.mk :=
  inclusion (map_mono J.specialSubgroup_le_unitarySubgroup)

/-- Full projective unitary matrices normalize the special projective image. -/
theorem projectiveUnitary_le_normalizer {F : Type*} [Field F]
    (J : HermitianForm 3 F) :
    J.unitarySubgroup.map ProjGenLinGroup.mk ≤
      normalizer (J.specialSubgroup.map ProjGenLinGroup.mk) := by
  apply le_normalizer_iff.mpr
  rintro _ ⟨u, hu, rfl⟩ _ ⟨x, hx, rfl⟩
  refine ⟨u * x * u⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  refine ⟨J.unitarySubgroup.mul_mem
    (J.unitarySubgroup.mul_mem hu hx.1) (J.unitarySubgroup.inv_mem hu), ?_⟩
  change GeneralLinearGroup.det (u * x * u⁻¹) = 1
  have hxdet : GeneralLinearGroup.det x = 1 := hx.2
  simp [map_mul, hxdet]

/-- An extension to the actual PGU carrier, with the prescribed PSU image.
No choice of an abstract group of the same order is allowed. -/
structure ProjectiveExtension {G : Type*} [Group G] (S : Subgroup G)
    {F : Type*} [Field F] (J : HermitianForm 3 F) where
  embedding : J.unitarySubgroup.map ProjGenLinGroup.mk →* G
  injective : Function.Injective embedding
  socle_range_eq : (embedding.comp (projectiveSpecialInclusion J)).range = S

namespace ProjectiveExtension

variable {G : Type*} [Group G] {S : Subgroup G}
    {F : Type*} [Field F] {J : HermitianForm 3 F}

/-- The prescribed socle is contained in the embedded full projective group. -/
theorem socle_le_range (E : ProjectiveExtension S J) : S ≤ E.embedding.range := by
  intro x hx
  have hx' : x ∈ (E.embedding.comp (projectiveSpecialInclusion J)).range :=
    E.socle_range_eq.symm ▸ hx
  obtain ⟨y, hy⟩ := hx'
  exact ⟨projectiveSpecialInclusion J y, hy⟩

/-- Every such extension lies in the normalizer of the prescribed socle.
This is a consequence of the matrix definitions, not extra geometric input. -/
theorem range_le_normalizer (E : ProjectiveExtension S J) :
    E.embedding.range ≤ normalizer S := by
  have hnormal : (projectiveSpecialInclusion J).range.Normal := by
    rw [projectiveSpecialInclusion, inclusion_range]
    exact (normal_subgroupOf_iff_le_normalizer
      (map_mono J.specialSubgroup_le_unitarySubgroup)).mpr
        (projectiveUnitary_le_normalizer J)
  let := hnormal
  calc
    E.embedding.range =
        (normalizer ((projectiveSpecialInclusion J).range : Set _)).map E.embedding := by
      rw [normalizer_eq_top, ← MonoidHom.range_eq_map]
    _ ≤ normalizer ((projectiveSpecialInclusion J).range.map E.embedding) :=
      le_normalizer_map E.embedding
    _ = normalizer S := by rw [← MonoidHom.range_comp, E.socle_range_eq]

end ProjectiveExtension

/-- The geometric extension problem for the supplied unitary socle. It
does not require the chosen socle equivalence to extend as a marked map:
the exact embedded subgroup, rather than its marking, must be preserved. -/
@[expose] def UnitaryEmbeddingExtensions : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (Model m), IsCoatom M →
    ¬ Group.IsSolvable M → solvableRadical M = ⊥ → ∀ S : Subgroup M,
      S.Normal → IsSimpleGroup S → ¬ IsMulCommutative S →
      centralizer (S : Set M) = ⊥ →
      ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F),
        Nat.card F = (2 ^ (2 * m + 1)) ^ 2 →
        (∀ x, J.conj x = x ^ (2 ^ (2 * m + 1))) →
        (S ≃* ProjectiveSpecialUnitaryMatrixGroup J) →
        Nonempty (ProjectiveExtension (S.map M.subtype) J)

/-- The normalizer calculation may be proved independently, taking an
actual projective extension as input. Properness must be proved as well
as normality and the index; ambient simplicity is not an input. -/
@[expose] def UnitaryExtensionNormalizers : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (Model m), IsCoatom M →
    ¬ Group.IsSolvable M → solvableRadical M = ⊥ → ∀ S : Subgroup M,
      S.Normal → IsSimpleGroup S → ¬ IsMulCommutative S →
      centralizer (S : Set M) = ⊥ →
      ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F),
        Nat.card F = (2 ^ (2 * m + 1)) ^ 2 →
        (∀ x, J.conj x = x ^ (2 ^ (2 * m + 1))) →
        (S ≃* ProjectiveSpecialUnitaryMatrixGroup J) →
        ∀ E : ProjectiveExtension (S.map M.subtype) J,
          normalizer (S.map M.subtype : Set (Model m)) ≠ ⊤ ∧
          (E.embedding.range.subgroupOf
            (normalizer (S.map M.subtype : Set (Model m)))).Normal ∧
          Nat.card (normalizer (S.map M.subtype : Set (Model m)) ⧸
            E.embedding.range.subgroupOf
              (normalizer (S.map M.subtype : Set (Model m)))) = 2

end ReeF4.MaximalSubgroups.SimpleNormal
