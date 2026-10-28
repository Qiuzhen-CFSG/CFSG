module

public import Theory.SpecificGroups.BinaryLinear.RadicalAction
public import Theory.Representation.BinaryPlaneSolvable
public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual
public import Theory.GroupTheory.PerfectSimpleImageOrder

/-!
# The two geometric rows for a perfect binary-five actor

A perfect actor fixes the two-dimensional diagonal factor of a 2+3 or 3+2
parabolic. The literal displacement coordinates then give two dual rows
or two natural columns. The three-dimensional diagonal marking is retained;
it is not silently identified with a separately chosen source marking.
-/

public noncomputable section
open Subgroup
namespace BinaryLinear
open SmallParabolicLevi OuterCyclic
variable {V E : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] [Group E] [Group.IsPerfect E]

private theorem perfect_hom_eq_one {F : Type*} [Group F] [Group.IsSolvable F]
    (f : E →* F) : f=1 := by
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hb : f.range=⊥ := by
    by_contra hb
    let : Nontrivial f.range := (nontrivial_iff_ne_bot _).mpr hb
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  exact MonoidHom.range_eq_bot_iff.mp hb

private def naturalCoordinates (W : Submodule (ZMod 2) V)
    (a : W ≃ₗ[ZMod 2] Space 3) (b : (V ⧸ W) ≃ₗ[ZMod 2] Space 2) :
    ((V ⧸ W) →ₗ[ZMod 2] W) ≃ₗ[ZMod 2] (Space 3 × Space 3) :=
  ((LinearEquiv.arrowCongr b a).trans
    (LinearEquiv.piRing (ZMod 2) (Space 3) (Fin 2) (ZMod 2))).trans
      (LinearEquiv.finTwoArrow (ZMod 2) (Space 3))

private def dualCoordinates (W : Submodule (ZMod 2) V)
    (a : W ≃ₗ[ZMod 2] Space 2) (b : (V ⧸ W) ≃ₗ[ZMod 2] Space 3) :
    ((V ⧸ W) →ₗ[ZMod 2] W) ≃ₗ[ZMod 2]
      (Module.Dual (ZMod 2) (Space 3) × Module.Dual (ZMod 2) (Space 3)) :=
  ((LinearEquiv.arrowCongr b a).trans
    (LinearEquiv.linearMapPi (ZMod 2)).symm).trans
      (LinearEquiv.finTwoArrow (ZMod 2) (Module.Dual (ZMod 2) (Space 3)))

/-- A perfect actor fixes the marked two-dimensional subspace pointwise. -/
theorem perfect_subspaceAction_eq_one (W : Submodule (ZMod 2) V)
    (f : E →* parabolic W) (hW : Module.finrank (ZMod 2) W=2) :
    (subspaceAction W).comp f=1 := by
  let : Group.IsSolvable (BinaryLinear.GL W) := linearGroup_solvable_of_finrank_two hW
  exact perfect_hom_eq_one _

/-- A perfect actor fixes the marked two-dimensional quotient pointwise. -/
theorem perfect_quotientAction_eq_one (W : Submodule (ZMod 2) V)
    (f : E →* parabolic W) (hW : Module.finrank (ZMod 2) (V ⧸ W)=2) :
    (quotientAction W).comp f=1 := by
  let : Group.IsSolvable (BinaryLinear.GL (V ⧸ W)) := linearGroup_solvable_of_finrank_two hW
  exact perfect_hom_eq_one _

/-- The 3+2 radical, with its literal action, consists of two natural columns
for the actual three-dimensional subspace action. -/
theorem perfect_radical_natural_rows (W : Submodule (ZMod 2) V)
    (f : E →* parabolic W)
    (a : W ≃ₗ[ZMod 2] Space 3) (b : (V ⧸ W) ≃ₗ[ZMod 2] Space 2) :
    ∃ e : radical W ≃* Multiplicative (Space 3 × Space 3),
      ∀ (g : E) (x y : radical W), y.val=(f g).val*x.val*(f g).val⁻¹ →
        (e y).toAdd =
          ((linearGroupCongr a (subspaceAction W (f g))) ((e x).toAdd.1),
           (linearGroupCongr a (subspaceAction W (f g))) ((e x).toAdd.2)) := by
  let c := naturalCoordinates W a b
  let e := (radicalDisplacementEquiv W).trans c.toAddEquiv.toMultiplicative
  have hd : Module.finrank (ZMod 2) (V ⧸ W)=2 := by
    simpa using b.finrank_eq
  have hf := perfect_quotientAction_eq_one W f hd
  refine ⟨e,?_⟩
  intro g x y hy
  have hh := radicalDisplacementEquiv_conjugation W (f g) x y hy
  have hq : quotientAction W (f g)⁻¹=1 := by
    have h := DFunLike.congr_fun hf g⁻¹
    simpa only [MonoidHom.comp_apply,map_inv,MonoidHom.one_apply,inv_one] using h
  rw [hq] at hh
  apply Prod.ext
  · change a ((radicalDisplacementEquiv W y).toAdd (b.symm (Pi.single 0 1))) = _
    rw [hh]
    change a (subspaceAction W (f g)
      ((radicalDisplacementEquiv W x).toAdd (b.symm (Pi.single 0 1)))) = _
    simp only [e,c,naturalCoordinates,linearGroupCongr_apply]
    simp
  · change a ((radicalDisplacementEquiv W y).toAdd (b.symm (Pi.single 1 1))) = _
    rw [hh]
    change a (subspaceAction W (f g)
      ((radicalDisplacementEquiv W x).toAdd (b.symm (Pi.single 1 1)))) = _
    simp only [e,c,naturalCoordinates,linearGroupCongr_apply]
    simp

/-- The 2+3 radical, with its literal action, consists of two dual rows
for the actual three-dimensional quotient action. -/
theorem perfect_radical_dual_rows (W : Submodule (ZMod 2) V)
    (f : E →* parabolic W)
    (a : W ≃ₗ[ZMod 2] Space 2) (b : (V ⧸ W) ≃ₗ[ZMod 2] Space 3) :
    ∃ e : radical W ≃* Multiplicative
        (Module.Dual (ZMod 2) (Space 3) × Module.Dual (ZMod 2) (Space 3)),
      ∀ (g : E) (x y : radical W), y.val=(f g).val*x.val*(f g).val⁻¹ →
        (e y).toAdd =
          (((e x).toAdd.1).comp
            (linearGroupCongr b (quotientAction W (f g))⁻¹).toLinearMap,
           ((e x).toAdd.2).comp
            (linearGroupCongr b (quotientAction W (f g))⁻¹).toLinearMap) := by
  let c := dualCoordinates W a b
  let e := (radicalDisplacementEquiv W).trans c.toAddEquiv.toMultiplicative
  have hd : Module.finrank (ZMod 2) W=2 := by simpa using a.finrank_eq
  have hf := perfect_subspaceAction_eq_one W f hd
  refine ⟨e,?_⟩
  intro g x y hy
  have hh := radicalDisplacementEquiv_conjugation W (f g) x y hy
  have hs : subspaceAction W (f g)=1 := DFunLike.congr_fun hf g
  rw [hs] at hh
  apply Prod.ext
  · apply LinearMap.ext
    intro v
    change a ((radicalDisplacementEquiv W y).toAdd (b.symm v)) 0 = _
    rw [hh]
    change a ((radicalDisplacementEquiv W x).toAdd
      (quotientAction W (f g)⁻¹ (b.symm v))) 0 = _
    change a ((radicalDisplacementEquiv W x).toAdd
      (quotientAction W (f g)⁻¹ (b.symm v))) _ =
      a ((radicalDisplacementEquiv W x).toAdd
        (b.symm (b (quotientAction W (f g)⁻¹ (b.symm v))))) _
    rw [b.symm_apply_apply]
  · apply LinearMap.ext
    intro v
    change a ((radicalDisplacementEquiv W y).toAdd (b.symm v)) 1 = _
    rw [hh]
    change a ((radicalDisplacementEquiv W x).toAdd
      (quotientAction W (f g)⁻¹ (b.symm v))) 1 = _
    change a ((radicalDisplacementEquiv W x).toAdd
      (quotientAction W (f g)⁻¹ (b.symm v))) _ =
      a ((radicalDisplacementEquiv W x).toAdd
        (b.symm (b (quotientAction W (f g)⁻¹ (b.symm v))))) _
    rw [b.symm_apply_apply]

end BinaryLinear
