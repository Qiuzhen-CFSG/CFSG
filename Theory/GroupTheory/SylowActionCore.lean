module
public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Transporting the two-core of an action image through a common Sylow

Two homomorphisms with the same kernel identify their image groups and
hence their two-cores. A prescribed Sylow two-subgroup maps onto the
image two-core, so the inverse image inside that Sylow has precisely the
required image under the second action. No condition on the full kernel
is needed.

This is the action-to-permutation transport for the literal R₁ of
Aschbacher--Smith Notation 13.2.1, printed p.877, including central covers.
-/

public noncomputable section
open Subgroup
namespace Subgroup

private theorem same_kernel_core_iff
    {P A B : Type*} [Group P] [Group A] [Group B]
    (f : P →* A) (g : P →* B) (h : f.ker = g.ker) (x : P) :
    f.rangeRestrict x ∈ pCore 2 f.range ↔ g.rangeRestrict x ∈ pCore 2 g.range := by
  let e : f.range ≃* g.range := (QuotientGroup.quotientKerEquivRange f).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq h).trans (QuotientGroup.quotientKerEquivRange g))
  have hfx : (QuotientGroup.quotientKerEquivRange f).symm (f.rangeRestrict x) =
      QuotientGroup.mk x := by
    apply (QuotientGroup.quotientKerEquivRange f).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  have he : e (f.rangeRestrict x) = g.rangeRestrict x := by
    change QuotientGroup.quotientKerEquivRange g
      (QuotientGroup.quotientMulEquivOfEq h
        ((QuotientGroup.quotientKerEquivRange f).symm (f.rangeRestrict x))) = _
    rw [hfx,QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  rw [←he,←pCore_map_iso 2 e]
  exact (mem_map_iff_mem e.injective).symm

theorem sylow_actionCore_image
    {P A B : Type*} [Group P] [Finite P] [Group A] [Group B]
    (f : P →* A) (g : P →* B) (h : f.ker = g.ker) (S : Sylow 2 P) :
    ((((pCore 2 f.range).comap (f.rangeRestrict.comp (S : Subgroup P).subtype)).map
      (S : Subgroup P).subtype).map g) = g.range.pCoreIn 2 := by
  have he : ((pCore 2 f.range).comap (f.rangeRestrict.comp (S : Subgroup P).subtype)).map
      (S : Subgroup P).subtype = (S : Subgroup P) ⊓ (pCore 2 g.range).comap g.rangeRestrict := by
    ext x
    constructor
    · rintro ⟨s,hs,rfl⟩
      exact ⟨s.property,(same_kernel_core_iff f g h s).mp hs⟩
    · rintro ⟨hs,hg⟩
      exact ⟨⟨x,hs⟩,(same_kernel_core_iff f g h x).mpr hg,rfl⟩
  rw [he]
  have hc : pCore 2 g.range ≤ (S : Subgroup P).map g.rangeRestrict :=
    pCore_isPGroup.le_sylow_of_normal (S.mapSurjective g.rangeRestrict_surjective)
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact mem_map_of_mem g.range.subtype (show g.rangeRestrict x ∈ pCore 2 g.range from hx.2)
  · rintro _ ⟨a,ha,rfl⟩
    obtain ⟨x,hx,hxa⟩ := hc ha
    refine ⟨x,⟨hx,?_⟩,?_⟩
    · change g.rangeRestrict x ∈ pCore 2 g.range
      rw [hxa]
      exact ha
    · exact congrArg Subtype.val hxa

end Subgroup
