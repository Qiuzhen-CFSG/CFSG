module
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse.RankTwoField.Kernel
public import Theory.AtlasPort.LinearGroups.G2.EvenBorelAction
public import Theory.AtlasPort.LinearGroups.G2.Perfectness

/-!
# The G₂ torus kernel from inner-field coverage

The actual unipotent Sylow and its Borel have quotient Fˣ × Fˣ. The proved
projection formula applies the field component of an inner-field actor to
both coordinates. If the actor is trivial on this quotient, every unit is
fixed, hence the field component is the identity. Actual inner conjugation
transports the deduction to any Sylow subgroup, and proved perfectness
identifies the nonbinary derived carrier with the full octonion model.

Surjectivity of `semilinearAction` remains the only automorphism-classification
input. This module does not prove that pending theorem or treat its mere
injectivity as coverage. The source assembly must supply surjectivity.

Source: Aschbacher–Smith, `refs/quasithin.pdf`, B.4.2(4), B.5.6 and printed
p.1144, proof of 15.3.49(k). The concrete formulas are from `EvenBorelAction`
and the licensed ATLAS port; see `LICENSES/ATLAS.txt` and
`LICENSES/ATLAS-CITATION.cff`.
-/

@[expose] public section
open Subgroup
open Atlas.G2 Atlas.G2.EvenBorelTorus Atlas.G2.LieAutomorphismExtensions

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse.RankTwoField

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
private theorem g2_inner_of_standard_torus
    (hcover : Function.Surjective (semilinearAction (F := F)))
    (a : MulAut (Model F)) (hU : unipotent.map a.toMonoidHom = unipotent)
    (ha : ∀ b ∈ borel (K := F), b⁻¹ * a b ∈ unipotent) :
    a ∈ MulAut.innerSubgroup (Model F) := by
  obtain ⟨z, rfl⟩ := hcover a
  have hproj (b : borel (K := F)) :
      projection (restrictActor (semilinearAction z) (semilinear_map_borel z hU) b) =
        projection b := by
    have hk : b⁻¹ * restrictActor (semilinearAction z) (semilinear_map_borel z hU) b ∈
        (projection (F := F)).ker := by
      rw [projection_ker]
      exact ha b b.property
    have he := MonoidHom.mem_ker.mp hk
    rw [map_mul, map_inv, inv_mul_eq_one] at he
    exact he.symm
  have hσ : z.right = 1 := by
    apply RingEquiv.ext
    intro x
    by_cases hx : x = 0
    · subst x
      exact map_zero _
    let u : Fˣ := Units.mk0 x hx
    have he := hproj (torusSection (u, 1))
    have hp : projection (torusSection (u, 1)) = (u, 1) := projection_torus (u, 1)
    rw [projection_semilinear z hU, hp] at he
    exact congrArg (fun p : Fˣ × Fˣ => (p.1 : F)) he
  refine ⟨z.left, ?_⟩
  rw [semilinearAction_apply, hσ, map_one, mul_one]

/-- Actual inner-field coverage identifies the kernel on every Sylow-normalizer quotient. -/
theorem g2_torusRigid_of_coverage
    (hcover : Function.Surjective (semilinearAction (F := F))) : TorusRigid (Model F) := by
  intro P a hP ha
  obtain ⟨g, hgU, hgB⟩ := sylow_normalizer_conjugate P
  let e := MulAut.conj g
  let b := MulAut.congr e.symm a
  have hbU : unipotent.map b.toMonoidHom = unipotent (K := F) := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_map]
    have he : e.toMonoidHom.comp b.toMonoidHom = a.toMonoidHom.comp e.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      change e (e.symm (a (e x))) = a (e x)
      exact e.apply_symm_apply _
    rw [he, ← Subgroup.map_map, hgU, hP]
  have hb : ∀ x ∈ borel (K := F), x⁻¹ * b x ∈ unipotent := by
    intro x hx
    apply (mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp
    rw [hgU]
    have hxe : e x ∈ normalizer (P : Set (Model F)) :=
      hgB.le (mem_map_of_mem e.toMonoidHom hx)
    have h := ha (e x) hxe
    change e (x⁻¹ * e.symm (a (e x))) ∈ (P : Subgroup (Model F))
    rw [map_mul, map_inv, e.apply_symm_apply]
    exact h
  have hi := g2_inner_of_standard_torus hcover b hbU hb
  have hm : (MulAut.congr e.symm a) ∈
      (MulAut.innerSubgroup (Model F)).map (MulAut.congr e.symm).toMonoidHom := by
    rw [MulAut.map_innerSubgroup_congr]
    exact hi
  exact (mem_map_iff_mem (f := (MulAut.congr e.symm).toMonoidHom)
    (MulAut.congr e.symm).injective).mp hm

/-- The genuine derived-to-full perfectness equivalence retains the local torus kernel. -/
theorem derived_g2_torusRigid_of_coverage (hq : 2 < Nat.card F)
    (hcover : Function.Surjective (semilinearAction (F := F))) :
    TorusRigid (commutator (Model F)) := by
  let _ := Atlas.G2.isPerfect hq
  let e : commutator (Model F) ≃* Model F :=
    (MulEquiv.subgroupCongr (Group.IsPerfect.commutator_eq_top (G := Model F))).trans
      Subgroup.topEquiv
  exact (g2_torusRigid_of_coverage hcover).of_equiv e

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse.RankTwoField
