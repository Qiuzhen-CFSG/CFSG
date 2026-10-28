module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.Filtration

/-!
# Coordinates for the section above S∩L₁

The marked local star projection has two-group kernel S∩L₁. Pullback of the
two-core therefore identifies O₂(L₁)/(S∩L₁) with the actual two-core of the
A₄ point stabilizer. The quotient isomorphism respects conjugation by L₁.
This supplies the parabolic section for the last noncentral contribution in
13.5.22; the section is distinct from the central interval S₂/V.

Source: Aschbacher–Smith, 13.5.22, printed p.924 (PDF p.941), using G.2.4(1).
-/

@[expose] public section
open Subgroup NoncentralChiefRefinement
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount
open ChapterG.Section02 ChapterG.Section02.Setup
open ChapterG.Section02.AlternatingFive
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}

/-- The full residual quotient, marked by the literal five-point Borel. -/
noncomputable def localQuotientEquiv (d : Hypothesis D g) :
    (D.L₁ ⧸ (core d).val) ≃* Borel d :=
  (QuotientGroup.quotientMulEquivOfEq (localProjection_kernel d).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (localProjection d)
      (localProjection_surjective d))

@[simp] theorem localQuotientEquiv_mk (d : Hypothesis D g) (x : D.L₁) :
    localQuotientEquiv d (QuotientGroup.mk' _ x) = localProjection d x := rfl

/-- Pulling back the Borel two-core gives the original local two-core. -/
theorem localCore_eq_comap (d : Hypothesis D g) :
    (localCore D).val = (pCore 2 (Borel d)).comap (localProjection d) := by
  have hk : IsPGroup 2 (localProjection d).ker := by
    rw [localProjection_kernel]
    exact (isPGroup_pCoreIn 2 (D.I g)).comap_subtype
  exact ((localProjection d).comap_pCore_of_ker_isPGroup
    (localProjection_surjective d) hk).symm

/-- The same star map restricted to the local two-core, with exact image. -/
noncomputable def parabolicProjection (d : Hypothesis D g) :
    (localCore D).val →* pCore 2 (Borel d) :=
  ((localProjection d).comp (localCore D).val.subtype).codRestrict _ (fun x => by
    exact (localCore_eq_comap d).le x.property)

theorem parabolicProjection_surjective (d : Hypothesis D g) :
    Function.Surjective (parabolicProjection d) := by
  intro x
  obtain ⟨y, hy⟩ := localProjection_surjective d x.val
  have hm : y ∈ (localCore D).val := by
    rw [localCore_eq_comap]
    exact hy ▸ x.property
  exact ⟨⟨y, hm⟩, Subtype.ext hy⟩

theorem parabolicProjection_kernel (d : Hypothesis D g) :
    (parabolicProjection d).ker = (core d).val.subgroupOf (localCore D).val := by
  ext x
  change parabolicProjection d x = 1 ↔ x.val ∈ (core d).val
  rw [Subtype.ext_iff]
  change localProjection d x.val = 1 ↔ _
  exact Iff.of_eq (congrArg (fun N : Subgroup D.L₁ => x.val ∈ N)
    (localProjection_kernel d))

/-- Equivariant section coordinates for the parabolic two-core above S. -/
noncomputable def parabolicSectionEquiv (d : Hypothesis D g) :
    Section (core d) (localCore D) ≃* pCore 2 (Borel d) :=
  (QuotientGroup.quotientMulEquivOfEq (parabolicProjection_kernel d).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (parabolicProjection d)
      (parabolicProjection_surjective d))

@[simp] theorem parabolicSectionEquiv_mk (d : Hypothesis D g) (x : (localCore D).val) :
    parabolicSectionEquiv d (QuotientGroup.mk' _ x) = parabolicProjection d x := rfl

/-- The action on the actual section is Borel conjugation through the same map. -/
theorem parabolicSectionEquiv_equivariant (d : Hypothesis D g)
    (k : D.L₁) (x : Section (core d) (localCore D)) :
    parabolicSectionEquiv d (sectionAction (core d) (localCore D) k x) =
      MulAut.conjNormal (localProjection d k) (parabolicSectionEquiv d x) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ x
  rw [sectionAction_mk, parabolicSectionEquiv_mk, parabolicSectionEquiv_mk]
  apply Subtype.ext
  change localProjection d (k * x.val * k⁻¹) =
    localProjection d k * localProjection d x.val * (localProjection d k)⁻¹
  simp only [map_mul, map_inv]

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount
