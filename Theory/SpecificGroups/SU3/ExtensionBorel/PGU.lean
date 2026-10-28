module
public import Theory.SpecificGroups.SU3.ExtensionBorel.Matrix

/-!
# The Borel in the actual projective unitary matrix group

PGU is the literal image of the unitary subgroup in PGL. Its Borel is the
image of upper triangular unitary matrices, and its root subgroup is the
image of the PSU root under the original component inclusion. Conjugation
in this carrier agrees with the unitary action on PSU. The exact matrix
stabilizer test therefore computes the normalizer directly in PGU.

Source: Aschbacher–Smith, Lemma A.3.18 and the Borel placement in 13.6.6,
printed pp.51–52 and 927; the unitary matrix convention of GLS3 §2.7.
-/

@[expose] public section
open Matrix BenderSuzuki.External Subgroup
namespace BenderSuzuki.MatrixGroups.HermitianForm.ExtensionBorel
open BorelTorus
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

/-- PGU is the actual unitary matrix image in PGL. -/
def projectiveUnitary : Subgroup (ProjGenLinGroup (Fin 3) E) :=
  J.unitarySubgroup.map ProjGenLinGroup.mk

/-- The natural projection from unitary matrices to their actual projective image. -/
def unitaryToPGU : J.unitarySubgroup →* projectiveUnitary J :=
  (ProjGenLinGroup.mk.comp J.unitarySubgroup.subtype).codRestrict _
    (fun u => ⟨u.val, u.property, rfl⟩)

theorem unitaryToPGU_surjective : Function.Surjective (unitaryToPGU J) := by
  rintro ⟨x, u, hu, rfl⟩
  exact ⟨⟨u, hu⟩, rfl⟩

/-- The original component inclusion, retaining the literal PGL value. -/
def componentInPGU : ProjectiveSpecialUnitaryMatrixGroup J →* projectiveUnitary J :=
  Subgroup.inclusion (Subgroup.map_mono J.specialSubgroup_le_unitarySubgroup)

theorem componentInPGU_injective : Function.Injective (componentInPGU J) :=
  Subgroup.inclusion_injective _

/-- The Borel in PGU consists of images of upper triangular unitary matrices. -/
def pguBorel : Subgroup (projectiveUnitary J) :=
  (upperUnitary J).map (unitaryToPGU J)

/-- The root in PGU uses the natural component inclusion. -/
def pguRoot (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Subgroup (projectiveUnitary J) :=
  (projectiveRoot J hJ).map (componentInPGU J)

private theorem pgu_conj_comp (u : J.unitarySubgroup) :
    (MulAut.conj (unitaryToPGU J u) : projectiveUnitary J →* projectiveUnitary J).comp (componentInPGU J) =
      (componentInPGU J).comp (J.unitaryConj u).toMonoidHom := by
  ext x
  exact (J.unitaryConj_apply_val u x).symm

/-- Exact comparison between conjugation in PGU and its action on the component. -/
theorem mem_normalizer_pguRoot_iff
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (u : J.unitarySubgroup) :
    unitaryToPGU J u ∈ normalizer (pguRoot J hJ : Set (projectiveUnitary J)) ↔
      (projectiveRoot J hJ).map (J.unitaryConj u).toMonoidHom = projectiveRoot J hJ := by
  rw [mem_normalizer_iff_map_conj_eq, pguRoot, Subgroup.map_map, pgu_conj_comp,
    ← Subgroup.map_map]
  exact (Subgroup.map_injective (componentInPGU_injective J)).eq_iff

variable [Finite E]

/-- The root normalizer in the actual PGU carrier is its triangular matrix Borel. -/
theorem normalizer_pguRoot
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {q : ℕ} (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) :
    normalizer (pguRoot J hJ : Set (projectiveUnitary J)) = pguBorel J := by
  have hu (u : J.unitarySubgroup) :
      unitaryToPGU J u ∈ normalizer (pguRoot J hJ : Set (projectiveUnitary J)) ↔
        u ∈ upperUnitary J := by
    rw [mem_normalizer_pguRoot_iff]
    apply root_map_eq_iff_upper J hJ hcard hfixed _ 1 u
    intro x
    change (J.unitaryConj u x).val = _ * ProjGenLinGroup.map (RingHom.id E) _ * _
    rw [ProjGenLinGroup.map_id, MonoidHom.id_apply]
    exact J.unitaryConj_apply_val u x
  apply le_antisymm
  · intro x hx
    obtain ⟨u, rfl⟩ := unitaryToPGU_surjective J x
    exact ⟨u, (hu u).mp hx, rfl⟩
  · rintro x ⟨u, hupper, rfl⟩
    exact (hu u).mpr hupper

end BenderSuzuki.MatrixGroups.HermitianForm.ExtensionBorel
