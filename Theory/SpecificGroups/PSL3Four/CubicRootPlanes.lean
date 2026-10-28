module
public import Theory.SpecificGroups.PSL3Four.HyperbolicRootRecognition.ElementaryPlanes

/-!
# Cubic invariance of the two elementary root planes

UT₃(F₄) has exactly two elementary subgroups of order sixteen. An automorphism
whose cube is the identity preserves each: swapping them would give an action
of order two. The conclusion is transported to the original carrier through
an actual multiplicative equivalence.

Source application: the two invariant complements in Delgado--Goldschmidt--
Stellmacher, Groups and Graphs (1985), (10.9), p.163. The elementary-plane
calculation is Aschbacher, Sporadic Groups (1994), 45.3, pp.242--243.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.HyperbolicRecognition
variable {H : Type*} [Group H]

theorem cubic_preserves_transported_planes (e : H ≃* Matrix.PSL3Four.RootNormalizerModel.Root)
    (a : MulAut H) (ha : a ^ 3 = 1) :
    (transportedPlane₁ e).map a.toMonoidHom = transportedPlane₁ e ∧
      (transportedPlane₂ e).map a.toMonoidHom = transportedPlane₂ e := by
  let A := transportedPlane₁ e
  let B := transportedPlane₂ e
  have hA : IsElementaryAbelian 2 A ∧ Nat.card A = 16 := ⟨inferInstance,card_transportedPlane₁ e⟩
  have hB : IsElementaryAbelian 2 B ∧ Nat.card B = 16 := ⟨inferInstance,card_transportedPlane₂ e⟩
  have hne : A ≠ B := transportedPlanes_ne e
  have hmap (E : Subgroup H) (hE : IsElementaryAbelian 2 E ∧ Nat.card E = 16) :
      E.map a.toMonoidHom = A ∨ E.map a.toMonoidHom = B := by
    let := hE.1
    apply (transported_elementary_sixteen_iff e _).mp
    exact ⟨IsElementaryAbelian.map a.toMonoidHom,by rw [card_map_of_injective a.injective,hE.2]⟩
  have hcube (E : Subgroup H) :
      ((E.map a.toMonoidHom).map a.toMonoidHom).map a.toMonoidHom = E := by
    rw [map_map,map_map]
    have hh : (a.toMonoidHom.comp a.toMonoidHom).comp a.toMonoidHom = MonoidHom.id H := by
      ext x
      change a (a (a x)) = x
      have hc := congrArg (fun f : MulAut H => f x) ha
      simpa only [pow_succ,pow_zero,MulAut.mul_apply,MulAut.one_apply] using hc
    rw [hh,map_id]
  rcases hmap A hA with hAA | hAB
  · refine ⟨hAA,?_⟩
    rcases hmap B hB with hBA | hBB
    · exact (hne (map_injective a.injective (hAA.trans hBA.symm))).elim
    · exact hBB
  · rcases hmap B hB with hBA | hBB
    · have hh := hcube A
      rw [hAB,hBA,hAB] at hh
      exact (hne hh.symm).elim
    · exact (hne (map_injective a.injective (hAB.trans hBB.symm))).elim
end Theory.GroupTheory.HyperbolicRecognition
