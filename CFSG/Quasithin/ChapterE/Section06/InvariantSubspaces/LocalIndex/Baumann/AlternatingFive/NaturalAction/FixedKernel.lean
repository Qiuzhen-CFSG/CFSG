module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.Representation.BinaryAlternatingNaturalCohomology.Projective
public import Theory.Representation.ProjectiveCentralCover
public import Theory.Representation.ElementaryAbelianAction.Commutator
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# The fixed kernel of an actual alternating-five block is trivial

For a short group, two-perfection gives `[U,L] = U`. Its elementary abelian
commutator layer `U` is centralized by `O₂(L)`, so conjugation defines a binary
representation of the actual quotient `L/O₂(L)`. The block model identifies
`U/C_U(L)` equivariantly with the natural A₅ module. That module is projective,
and hence the commutator-generated central cover `U → U/C_U(L)` is injective.

Only the fixed kernel inside `U` is removed. The possible central extension
in `O₂(L)` remains unrestricted.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), C.1.13(c), printed pp.124–125/PDF pp.135–136,
using I.1.5–6, printed p.408/PDF p.419.
-/

public section

open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterC

open Representation Subgroup

variable {L : Type*} [Group L]

private theorem blockU_commutator_eq (h : IsShort L) : ⁅blockU L, (⊤ : Subgroup L)⁆ = blockU L := by
  let := h.finite
  exact Subgroup.commutator_isPPerfect_idempotent (⊤ : Subgroup L) (pCore 2 L)
    (h.twoPerfect.of_surjective (Subgroup.topEquiv (G := L)).symm.toMonoidHom
      (Subgroup.topEquiv (G := L)).symm.surjective)
    pCore_isPGroup (by rw [Subgroup.normalizer_eq_top])

/-- The original A₅ block hypotheses force `C_U(L)` to be trivial. -/
theorem IsAlternatingBlock.blockFixed_eq_bot (h : IsAlternatingBlock L 5) : blockFixed L = ⊥ := by
  let := h.2.1.elementary
  obtain ⟨ρ, ⟨m⟩, hρ⟩ := h.2.2
  let n : L →* normalizer (blockU L : Set L) :=
    { toFun l := ⟨l, by rw [normalizer_eq_top]; exact mem_top _⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  let c : L →* MulAut (blockU L) := (blockU L).normalizerMonoidHom.comp n
  have hc : pCore 2 L ≤ c.ker := by
    intro l hl
    apply MonoidHom.mem_ker.mpr
    ext w
    change l * (w : L) * l⁻¹ = (w : L)
    rw [mem_centralizer_iff.mp (h.2.1.central w.property) l hl, mul_inv_cancel_right]
  let q := QuotientGroup.lift (pCore 2 L) c hc
  let r := q.comp m.quotientIso.symm.toMonoidHom
  let a := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have ha : Function.Surjective a :=
    m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)
  have hr (l : L) (w : blockU L) : r (a l) w = blockConjugate L l w := by
    change q (m.quotientIso.symm (m.quotientIso _)) w = _
    rw [m.quotientIso.symm_apply_apply]
    rfl
  let : MulDistribMulAction (alternatingGroup (Fin 5)) (blockU L) :=
    MulDistribMulAction.compHom (blockU L) r
  let σ := ofElementaryAbelianAction (A := alternatingGroup (Fin 5)) (G := blockU L) (p := 2)
  let f₀ := m.moduleIso.toMonoidHom.comp (QuotientGroup.mk' (blockFixed L))
  let f : Additive (blockU L) →ₗ[ZMod 2] BinaryPermutation.natural (Fin 5) :=
    f₀.toAdditiveLeft.toZModLinearMap 2
  let f' : σ.IntertwiningMap (BinaryPermutation.alternatingNaturalRepresentation (Fin 5)) :=
    { toLinearMap := f
      isIntertwining' g := by
        apply LinearMap.ext
        intro w
        obtain ⟨l, rfl⟩ := ha g
        change Multiplicative.toAdd (m.moduleIso (QuotientGroup.mk' _ (r (a l) w.toMul))) = _
        rw [hr, m.intertwining]
        exact hρ (a l) (m.moduleIso (QuotientGroup.mk' _ w.toMul)) }
  have hf : Function.Surjective f' := by
    intro v
    obtain ⟨w, hw⟩ :=
      (m.moduleIso.surjective.comp (QuotientGroup.mk'_surjective (blockFixed L)))
        (Multiplicative.ofAdd v)
    exact ⟨Additive.ofMul w, congrArg Multiplicative.toAdd hw⟩
  have hk : ∀ w, f' w = 0 → ∀ g, σ g w = w := by
    intro w hw g
    obtain ⟨l, rfl⟩ := ha g
    have hwq : QuotientGroup.mk' (blockFixed L) w.toMul = 1 := by
      apply m.moduleIso.injective
      exact (Multiplicative.toAdd.injective hw).trans (map_one m.moduleIso).symm
    have hwc : (w.toMul : L) ∈ center L :=
      (QuotientGroup.eq_one_iff (N := blockFixed L) _).mp hwq
    change Additive.ofMul (r (a l) w.toMul) = w
    apply Additive.toMul.injective
    rw [hr]
    apply Subtype.ext
    change l * (w.toMul : L) * l⁻¹ = (w.toMul : L)
    rw [Subgroup.mem_center_iff.mp hwc l, mul_inv_cancel_right]
  have hgen : Coinvariants.ker σ = ⊤ :=
    coinvariants_ker_eq_top_of_commutator_eq (blockU L) σ a
      (fun l w => congrArg Subtype.val (hr l w.toMul)) (blockU_commutator_eq h.2.1)
  let := BinaryPermutation.alternatingFive_natural_projective
  have hinj := f'.injective_of_projective_of_fixed_kernel hf hk hgen
  apply bot_unique
  intro w hw
  apply Additive.ofMul.injective
  apply hinj
  change Multiplicative.toAdd (m.moduleIso (QuotientGroup.mk' _ w)) = _
  rw [show QuotientGroup.mk' (blockFixed L) w = 1 from
    (QuotientGroup.eq_one_iff _).mpr hw, map_one]
  exact (map_zero f').symm

end CFSG.Quasithin.ChapterC
