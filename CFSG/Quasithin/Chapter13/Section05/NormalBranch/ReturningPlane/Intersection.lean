module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.ReturningPlane.Selection

/-!
# The returning quaternion cores meet in the source plane

The quotient images of U_H and its selected conjugate lie in the two
marked even point cores, whose intersection is trivial. Their original
intersection therefore lies in V. Intersecting each core with V gives the
two order-eight seeds, and their intersection is the original plane V₂.
All maps and conjugations refer to the original subgroups of G.

Source: Aschbacher–Smith,13.5.16, printed p.921. This proves the previously
implicit U ∩ Uʸ = V₂ step from the ordinary natural setup and13.5.15.
-/

@[expose] public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.ReturningPlane
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open PlaneGeometry.TwoBlocks
open Theory.GroupTheory.Recognition
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {V₂ M : Subgroup G} {g : G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)

include d

theorem core_intersection_le_module (h : D.Hypothesis) (b : Conclusions D M 6 g)
    (hM : M = D.L) (a : alternatingGroup (Fin 6))
    (ha : Section07.NaturalAction.image d D.V₁ = move a.val canonicalLine)
    (y : D.L) (hy : localMap d y = a.val * pairRotation⁻¹ * a.val⁻¹) :
    D.UH ⊓ UnitaryFourThree.conjugate D.UH y.val ≤ D.V := by
  intro x hx
  let xl : D.L := ⟨x, b.one.2.1 hx.1⟩
  have hi := closure_image_le_pointCore d h b a ha
  have hleft : localMap d xl ∈ pointCoreEven.map (MulAut.conj a.val).toMonoidHom :=
    hi (mem_map_of_mem (localMap d) hx.1)
  obtain ⟨u, hu, hux⟩ := hx.2
  let ul : D.L := ⟨u,b.one.2.1 hu⟩
  have hui := hi (mem_map_of_mem (localMap d) (show ul ∈ D.UH.subgroupOf D.L from hu))
  obtain ⟨v, hv, hvu⟩ := hui
  have hxl : xl = y⁻¹ * ul * y := by
    apply Subtype.ext
    change x = y.val⁻¹*u*y.val
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply, inv_inv] using hux.symm
  have hright : localMap d xl ∈
      pointCoreEven.map (MulAut.conj (a.val*pairRotation)).toMonoidHom := by
    refine ⟨v,hv,?_⟩
    have hq : localMap d xl = (localMap d y)⁻¹ * localMap d ul * localMap d y := by
      rw [hxl]
      simp only [map_mul, map_inv]
    rw [hq, hy, ← hvu]
    change (a.val*pairRotation)*v*(a.val*pairRotation)⁻¹ =
      (a.val*pairRotation⁻¹*a.val⁻¹)⁻¹*(a.val*v*a.val⁻¹)*(a.val*pairRotation⁻¹*a.val⁻¹)
    group
  have he : localMap d xl = 1 := by
    have hi' : localMap d xl ∈
        pointCoreEven.map (MulAut.conj a.val).toMonoidHom ⊓
        pointCoreEven.map (MulAut.conj (a.val*pairRotation)).toMonoidHom := ⟨hleft,hright⟩
    rw [ReturningPlane.marked_pointCore_intersection a.val] at hi'
    exact hi'
  have hcore : xl ∈ pCore 2 D.L := by
    rw [← localMap_kernel d (b.four.2 rfl)]
    exact he
  have hV : D.V = D.L.pCoreIn 2 := b.seven.2.trans (congrArg (fun X => X.pCoreIn 2) hM)
  rw [hV]
  exact mem_map_of_mem D.L.subtype hcore

theorem original_core_intersection (h : D.Hypothesis) (b : Conclusions D M 6 g)
    (hM : M = D.L) (a : alternatingGroup (Fin 6))
    (ha : Section07.NaturalAction.image d D.V₁ = move a.val canonicalLine)
    (y : D.L) (hy : localMap d y = a.val * pairRotation⁻¹ * a.val⁻¹)
    (hyP : y.val ∈ normalizer (V₂ : Set G)) (hyG : y.val ∉ D.Gz) :
    D.UH ⊓ UnitaryFourThree.conjugate D.UH y.val = V₂ := by
  have hV : UnitaryFourThree.conjugate D.V y.val = D.V :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (D.V : Set G)).inv_mem
      (d.normalizes_V (mem_sup_left y.property)))
  have hc := core_intersection_le_module d h b hM a ha y hy
  have hs := closure_intersection_module d h b hM
  have hsc : D.V ⊓ UnitaryFourThree.conjugate D.UH y.val =
      UnitaryFourThree.conjugate D.Vplus y.val := by
    rw [← hs]
    change D.V ⊓ D.UH.map (MulAut.conj y.val⁻¹).toMonoidHom =
      (D.V ⊓ D.UH).map (MulAut.conj y.val⁻¹).toMonoidHom
    rw [map_inf _ _ _ (MulAut.conj y.val⁻¹).injective]
    exact congrArg (· ⊓ D.UH.map (MulAut.conj y.val⁻¹).toMonoidHom) hV.symm
  have hi : D.UH ⊓ UnitaryFourThree.conjugate D.UH y.val =
      (D.V ⊓ D.UH) ⊓ (D.V ⊓ UnitaryFourThree.conjugate D.UH y.val) := by
    apply le_antisymm
    · exact le_inf (le_inf hc inf_le_left) (le_inf hc inf_le_right)
    · exact le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  rw [hi, hs, hsc]
  exact seed_intersection d h y hyP hyG

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.ReturningPlane
end
