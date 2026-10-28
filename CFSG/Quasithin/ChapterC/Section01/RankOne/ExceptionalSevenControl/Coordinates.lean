module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ExceptionalRestrictions.A7
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.CoreAction
public import Theory.Representation.BinaryConjugationSection.FixedSplitting

/-!
# Cohomology and original coordinates for the exceptional A₇ layer

The central quotient of U is U itself. Its irreducible four-dimensional
A₇ action therefore has vanishing first cohomology. We retain the literal
quotient L → L/O₂(L) and identify the ambient image of U with its intrinsic
binary space, so cocycle correction acts on original group elements.

Source: Aschbacher–Smith C.1.22–23, pp.129–130, and I.1.6(8).
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.RankOne.ExceptionalSevenControl
open Subgroup Representation Representation.OneCohomology
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterC CFSG.Quasithin.ChapterC.ExceptionalRestrictions
variable {L : Type*} [Group L]

theorem u_H1_subsingleton (h : IsExceptionalA7Block L) :
    letI := h.1.elementary
    Subsingleton (H1 (uRepresentation h.1)) := by
  let := h.1.finite
  let := h.1.elementary
  let := h.1.module_elementary
  have hi : Function.Injective (moduleProjection (L := L)) := by
    apply LinearMap.ker_eq_bot.mp
    apply le_bot_iff.mp
    intro v hv
    have hv' : v.toMul ∈ blockFixed L := (QuotientGroup.eq_one_iff _).mp hv
    rw [h.fixed_eq_bot] at hv'
    exact hv'
  let e := LinearEquiv.ofBijective (moduleProjection (L := L))
    ⟨hi, moduleProjection_surjective⟩
  let E : (uRepresentation h.1) ≃ₗ (moduleRepresentation h.1) :=
    .mk e (by intro g; exact LinearMap.ext (moduleProjection_equivariant h.1 g))
  let : IsIrreducible (uRepresentation h.1) :=
    E.irreducible_euqiv.mpr (moduleRepresentation_irreducible h.1)
  have hd : Module.finrank (ZMod 2) (Additive (blockU L)) = 4 :=
    e.finrank_eq.trans h.module_finrank
  obtain ⟨a⟩ := h.2.1
  let σ := (uRepresentation h.1).comp a.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff a.symm.toMonoidHom a.symm.surjective _).mpr inferInstance
  have hz := binaryAlternatingSeven_finrank_H1_eq_zero_of_irreducible_four σ hd
  have he := H1Congr (uRepresentation h.1) σ a (LinearEquiv.refl (ZMod 2) _) (by
    intro g v
    change uRepresentation h.1 g v = uRepresentation h.1 (a.symm (a g)) v
    rw [a.symm_apply_apply])
  exact (Module.finrank_eq_zero_iff_of_free (ZMod 2) _).mp (he.finrank_eq.trans hz)


noncomputable section
variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)

def blockSection (h : IsShort L) :
    letI := h.elementary
    BinaryConjugationSection L ((blockU L).map L.subtype) ⊥
      ((uRepresentation h).comp (QuotientGroup.mk' (pCore 2 L))) := by
  let := h.elementary
  let U := (blockU L).map L.subtype
  let e : blockU L ≃* U := equivMapOfInjective _ _ L.subtype_injective
  refine {
    section_le := map_subtype_le _
    kernel_le := bot_le
    normalized := L.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image L (blockU L))
    coordinates := {
      toFun := fun u => Multiplicative.ofAdd (Additive.ofMul (e.symm u))
      map_one' := congrArg (fun u => Multiplicative.ofAdd (Additive.ofMul u)) e.symm.map_one
      map_mul' := fun u v => congrArg (fun u => Multiplicative.ofAdd (Additive.ofMul u)) (e.symm.map_mul u v) }
    onto := fun u => ⟨e u.toAdd.toMul, by exact congrArg (fun u => Multiplicative.ofAdd (Additive.ofMul u)) (e.symm_apply_apply _)⟩
    kernel_eq := ?_
    equivariant := ?_ }
  · ext u
    change e.symm u = 1 ↔ (u : G) = 1
    rw [map_eq_one_iff e.symm e.symm.injective]
    exact Subtype.ext_iff
  · intro l u
    change Additive.ofMul (e.symm _) = uRepresentation h (QuotientGroup.mk' (pCore 2 L) l)
      (Additive.ofMul (e.symm u))
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    have he (x : U) : (((e.symm x : blockU L) : L) : G) = x :=
      congrArg Subtype.val (e.apply_symm_apply x)
    change (((e.symm _ : blockU L) : L) : G) = _
    rw [he]
    rw [uRepresentation_apply]
    change (l : G) * u * (l : G)⁻¹ = (l : G) * (((e.symm u : blockU L) : L) : G) * (l : G)⁻¹
    rw [he]



end
end CFSG.Quasithin.ChapterC.RankOne.ExceptionalSevenControl
