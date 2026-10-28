module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ExceptionalRestrictions.Conjugation
public import Theory.Representation.BinaryAlternatingNaturalCohomology
public import Theory.Representation.BinaryPermutationNaturalDuality

/-!
# The fixed layer of an ordinary A₇ block

The actual block module is the natural six-dimensional alternating module.
Self-duality and the odd-degree cohomology theorem make its dual H¹ vanish.
The genuine central covering U(L) → U(L)/C_U(L) therefore has zero kernel.
This retains the original action and the possible central layer until the
cohomology argument removes it.
Source: Aschbacher–Smith C.1.13(c), I.1.6(1), used in C.5.12, p.163.
-/
public section

open Subgroup Representation Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
open ExceptionalRestrictions
variable {L : Type*} [Group L]

theorem IsAlternatingBlock.seven_fixed_eq_bot (h : IsAlternatingBlock L 7) : blockFixed L = ⊥ := by
  let := h.2.1.finite
  let := h.2.1.elementary
  let := h.2.1.module_elementary
  obtain ⟨r,⟨m⟩,hm⟩ := h.2.2
  let σ := BinaryPermutation.alternatingNaturalRepresentation (Fin 7)
  let e : Additive (BlockModule L) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 7) :=
    { m.moduleIso.toAdditiveLeft with map_smul' := fun a v => ZMod.map_smul m.moduleIso.toAdditiveLeft a v }
  have he (g : L ⧸ pCore 2 L) (v : Additive (BlockModule L)) :
      e (moduleRepresentation h.2.1 g v) = σ (m.quotientIso g) (e v) := by
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) g
    obtain ⟨u,rfl⟩ := moduleProjection_surjective v
    rw [← moduleProjection_equivariant]
    change Multiplicative.toAdd (m.moduleIso (QuotientGroup.mk' _ (blockConjugate L l u.toMul))) = _
    rw [m.intertwining]
    exact hm _ _
  have hed (g : alternatingGroup (Fin 7)) (v : Module.Dual (ZMod 2) (BinaryPermutation.natural (Fin 7))) :
      e.dualMap (σ.dual g v) = (moduleRepresentation h.2.1).dual (m.quotientIso.symm g) (e.dualMap v) := by
    ext u
    change v (σ g⁻¹ (e u)) = v (e (moduleRepresentation h.2.1 ((m.quotientIso.symm g)⁻¹) u))
    rw [he,m.quotientIso.map_inv,m.quotientIso.apply_symm_apply]
  have hn := H1Congr σ σ.dual (MulEquiv.refl _) (BinaryPermutation.naturalDualEquiv (Fin 7))
    (fun g v => BinaryPermutation.naturalDualEquiv_equivariant (Fin 7) g.val v)
  have hd := H1Congr σ.dual (moduleRepresentation h.2.1).dual m.quotientIso.symm e.dualMap hed
  have hz : Module.finrank (ZMod 2) (H1 (moduleRepresentation h.2.1).dual) = 0 := by
    rw [← hd.finrank_eq,← hn.finrank_eq]
    exact BinaryPermutation.alternatingSeven_natural_finrank_H1
  have hb := finrank_ker_le_H1_of_cover (projection h.2.1) (projection_isCover h.2.1)
  rw [hz] at hb
  have hk : (moduleProjection (L := L)).ker = ⊥ :=
    Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero hb)
  apply bot_unique
  intro u hu
  have hv : Additive.ofMul u ∈ (moduleProjection (L := L)).ker :=
    (QuotientGroup.eq_one_iff _).mpr hu
  rw [hk] at hv
  exact hv
end CFSG.Quasithin.ChapterC
