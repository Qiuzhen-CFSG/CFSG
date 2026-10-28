module
public import CFSG.Quasithin.ChapterB.Section04.SmallRecognition.BinaryFourMarked.FourDimensional
public import CFSG.Quasithin.ChapterB.Section04.SmallRecognition.BinaryFourMarked.Support
public import Theory.Representation.BinaryFourExteriorCoordinates

/-!
# Fixed-marking classification of small quadratic binary L₄ modules

A faithful irreducible action with quadratic ratio at most two has a singleton
highest support. The endpoint supports have degree four, where inner/graph
recognition supplies the natural or dual action for the original marking.
Middle support constructs the six-coordinate exterior model; the canonical
minor-coordinate equivalence identifies it with the literal exterior power.
The same supplied group equivalence is used in all three alternatives.

Source: Aschbacher--Smith B.4.2(9--10), B.4.5, printed pp.86--87,
and their use in 13.8.25, printed pp.960--961. This proves the specialized
module classification, without extra ambient SQTK or degree hypotheses.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterB.SmallRecognition.BinaryFourMarked
open Representation Representation.BinaryOffender BinaryLinear.OuterCyclic
open ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
variable {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]
abbrev Exterior := ⋀[ZMod 2]^2 Four

/-- Exterior square of the natural action for the supplied marking. -/
def exterior (eH : H ≃* BinaryLinear.GL Four) : Representation (ZMod 2) H Exterior where
  toFun g := exteriorPower.map 2 (natural eH g)
  map_one' := by
    change exteriorPower.map 2 (natural eH 1) = LinearMap.id
    exact (congrArg (exteriorPower.map 2) (natural eH).map_one).trans exteriorPower.map_id
  map_mul' g h := by
    change exteriorPower.map 2 (natural eH (g * h)) =
      (exteriorPower.map 2 (natural eH g)).comp (exteriorPower.map 2 (natural eH h))
    exact (congrArg (exteriorPower.map 2) ((natural eH).map_mul g h)).trans
      (exteriorPower.map_comp _ _)

/-- The marked binary L₄ alternatives: genuine natural, dual or exterior-square
intertwiners, all using the same group equivalence and independent universes. -/
theorem marked_alternatives [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V) (eH : H ≃* BinaryLinear.GL Four)
    (hf : Function.Injective ρ) (hi : IsIrreducible ρ) (hq : quadraticRatio ρ ≤ 2) :
    ((∃ e : V ≃ₗ[ZMod 2] Four, ∀ g v, e (ρ g v) = eH g (e v)) ∨
      (∃ e : V ≃ₗ[ZMod 2] Module.Dual (ZMod 2) Four,
        ∀ g v, e (ρ g v) = (natural eH).dual g (e v))) ∨
      (∃ e : V ≃ₗ[ZMod 2] Exterior, ∀ g v, e (ρ g v) = exterior eH g (e v)) := by
  let eG : H ≃* Group := eH.trans (slEquivLinear 4).symm
  let σ := ρ.comp eG.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff eG.symm.toMonoidHom eG.symm.surjective ρ).mpr hi
  have hfσ : Function.Injective σ := hf.comp eG.symm.injective
  have hqσ : quadraticRatio σ ≤ 2 := by
    apply (quadraticRatio_le_of_injective_equivariant ρ σ eG.toMonoidHom eG.injective
      (LinearEquiv.refl _ _) (fun g v => ?_)).trans hq
    change ρ g v = ρ (eG.symm (eG g)) v
    rw [eG.symm_apply_apply]
  obtain ⟨i, v, hv, h⟩ := exists_singleton_highest σ hfσ hqσ
  have endpoint (hi : i = 0 ∨ i = 2) :=
    natural_or_dual_of_finrank_four ρ eH hf
      (le_antisymm (h.finrank_le_four_of_endpoint hv hi) (four_le_finrank_of_faithful σ hfσ))
  fin_cases i
  · exact Or.inl (endpoint (Or.inl rfl))
  · right
    let f := h.middleRootExteriorEquiv hv
    let c := BinaryFourExteriorCoordinates.equiv
    let e : V ≃ₗ[ZMod 2] Exterior := f.toLinearEquiv.symm.trans c.symm
    refine ⟨e, fun g w => ?_⟩
    apply c.injective
    change c (c.symm (f.toLinearEquiv.symm (ρ g w))) =
      c (exterior eH g (c.symm (f.toLinearEquiv.symm w)))
    rw [c.apply_symm_apply]
    have hσ : σ (eG g) w = ρ g w := by
      change ρ (eG.symm (eG g)) w = ρ g w
      rw [eG.symm_apply_apply]
    rw [← hσ]
    have hinter : f.toLinearEquiv.symm (σ (eG g) w) =
        MiddleRoot.exterior (eG g) (f.toLinearEquiv.symm w) :=
      LinearMap.congr_fun (f.symm.isIntertwining' (eG g)) w
    rw [hinter]
    have hmark : (natural eH g) = (eG g).val.toLin' := by
      apply LinearMap.ext
      intro x
      change eH g x = slEquivLinear 4 (eG g) x
      change eH g x = slEquivLinear 4 ((slEquivLinear 4).symm (eH g)) x
      rw [MulEquiv.apply_symm_apply]
    change MiddleRoot.exterior (eG g) (f.toLinearEquiv.symm w) =
      c (exteriorPower.map 2 (natural eH g) (c.symm (f.toLinearEquiv.symm w)))
    rw [hmark, BinaryFourExteriorCoordinates.equiv_map, c.apply_symm_apply]
    rfl
  · exact Or.inl (endpoint (Or.inr rfl))
end CFSG.Quasithin.ChapterB.SmallRecognition.BinaryFourMarked
