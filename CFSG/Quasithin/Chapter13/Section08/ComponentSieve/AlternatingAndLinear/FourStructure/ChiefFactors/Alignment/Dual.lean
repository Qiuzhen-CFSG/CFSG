module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# A common actor identification for the dual orientation

The contragredient action, expressed in dual-basis coordinates, is an
injective endomorphism of GL₄(2), hence an automorphism by finiteness. A module
identified with the dual for eH is consequently natural for one specified
new actor identification eH.trans dualActor. The same change works for all
quotients; no quotient is allowed its own independent change of orientation.

Source: the alignment of four-dimensional heads in Aschbacher–Smith,
*The Classification of Quasithin Groups*, 13.8.25, printed p.961.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment
open Representation
noncomputable def dualCoordinates : Module.Dual (ZMod 2) NaturalSpace ≃ₗ[ZMod 2] NaturalSpace :=
  (Pi.basisFun (ZMod 2) (Fin 4)).dualBasis.equivFun

noncomputable def dualActorHom : BinaryLinear.GL NaturalSpace →* BinaryLinear.GL NaturalSpace where
  toFun g := dualCoordinates.symm.trans (g.symm.dualMap.trans dualCoordinates)
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change dualCoordinates (dualCoordinates.symm v) = v
    exact dualCoordinates.apply_symm_apply v
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    apply dualCoordinates.symm.injective
    apply LinearMap.ext
    intro x
    simp only [LinearEquiv.trans_apply, LinearEquiv.mul_apply,
      LinearEquiv.symm_apply_apply, LinearEquiv.dualMap_apply]
    change (dualCoordinates.symm v) ((g * h)⁻¹ x) =
      (dualCoordinates.symm v) (h⁻¹ (g⁻¹ x))
    rw [mul_inv_rev]
    rfl

theorem dualActorHom_injective : Function.Injective dualActorHom := by
  intro g h he
  apply inv_injective
  apply LinearEquiv.ext
  intro v
  funext i
  let l : Module.Dual (ZMod 2) NaturalSpace := LinearMap.proj i
  have hh := congrArg (fun k : BinaryLinear.GL NaturalSpace =>
    (dualCoordinates.symm (k (dualCoordinates l))) v) he
  simpa [dualActorHom, l] using hh

noncomputable def dualActor : MulAut (BinaryLinear.GL NaturalSpace) := by
  let : Finite (BinaryLinear.GL NaturalSpace) := Finite.of_injective
    (fun g : BinaryLinear.GL NaturalSpace => (g : NaturalSpace → NaturalSpace))
    DFunLike.coe_injective
  exact MulEquiv.ofBijective dualActorHom
    (Finite.injective_iff_bijective.mp dualActorHom_injective)

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
theorem dual_is_natural (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* BinaryLinear.GL NaturalSpace)
    (e : U ≃ₗ[ZMod 2] Module.Dual (ZMod 2) NaturalSpace)
    (he : ∀ g u, e (ρ g u) = (naturalAction eH).dual g (e u)) :
    IsNatural ρ (eH.trans dualActor) := by
  refine ⟨e.trans dualCoordinates, ?_⟩
  intro g u
  change dualCoordinates (e (ρ g u)) =
    dualCoordinates ((eH g).symm.dualMap (dualCoordinates.symm (dualCoordinates (e u))))
  rw [LinearEquiv.symm_apply_apply, he]
  congr 1
  apply LinearMap.ext
  intro v
  change (e u) (eH g⁻¹ v) = (e u) ((eH g).symm v)
  rw [map_inv]
  rfl

/-- The marked plane after applying contragredient coordinates. -/
noncomputable def dualPlane (P : Submodule (ZMod 2) NaturalSpace) :
    Submodule (ZMod 2) NaturalSpace := P.dualAnnihilator.map dualCoordinates.toLinearMap

theorem dualPlane_mem (P : Submodule (ZMod 2) NaturalSpace) (v : NaturalSpace) :
    v ∈ dualPlane P ↔ dualCoordinates.symm v ∈ P.dualAnnihilator :=
  Submodule.mem_map_equiv _

theorem dualActor_apply_coordinates (g : BinaryLinear.GL NaturalSpace)
    (f : Module.Dual (ZMod 2) NaturalSpace) :
    dualActor g (dualCoordinates f) = dualCoordinates (g.symm.dualMap f) := by
  change dualCoordinates (g.symm.dualMap (dualCoordinates.symm (dualCoordinates f))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem dualActor_mem_parabolic_iff (P : Submodule (ZMod 2) NaturalSpace)
    (g : BinaryLinear.GL NaturalSpace) :
    dualActor g ∈ BinaryLinear.parabolic (dualPlane P) ↔ g ∈ BinaryLinear.parabolic P := by
  have stable (k : BinaryLinear.GL NaturalSpace) (hk : k ∈ BinaryLinear.parabolic P)
      (f : Module.Dual (ZMod 2) NaturalSpace) (hf : f ∈ P.dualAnnihilator) :
      k.symm.dualMap f ∈ P.dualAnnihilator := by
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro v hv
    exact (Submodule.mem_dualAnnihilator _).mp hf _
      ((BinaryLinear.parabolic P).inv_mem hk v |>.mpr hv)
  constructor
  · intro hg
    have hstable (k : BinaryLinear.GL NaturalSpace)
        (hk : dualActor k ∈ BinaryLinear.parabolic (dualPlane P)) :
        ∀ v ∈ P, k v ∈ P := by
      intro v hv
      rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := P)]
      apply (Submodule.mem_dualCoannihilator _).mpr
      intro f hf
      have hm : dualCoordinates f ∈ dualPlane P := by
        rw [dualPlane_mem, LinearEquiv.symm_apply_apply]
        exact hf
      have he : k.symm.dualMap (k.dualMap f) = f := by
        ext x
        simp
      have hh := (hk (dualCoordinates (k.dualMap f))).mp (by
        rw [dualActor_apply_coordinates, he]
        exact hm)
      rw [dualPlane_mem, LinearEquiv.symm_apply_apply] at hh
      exact (Submodule.mem_dualAnnihilator _).mp hh v hv
    intro v
    constructor
    · intro hv
      have hi : dualActor g⁻¹ ∈ BinaryLinear.parabolic (dualPlane P) := by
        rw [map_inv]
        exact (BinaryLinear.parabolic (dualPlane P)).inv_mem hg
      simpa using hstable g⁻¹ hi (g v) hv
    · exact hstable g hg v
  · intro hg v
    obtain ⟨f, rfl⟩ := dualCoordinates.surjective v
    rw [dualActor_apply_coordinates]
    rw [dualPlane_mem, dualPlane_mem]
    simp only [LinearEquiv.symm_apply_apply]
    constructor
    · intro hf
      have hh := stable g⁻¹ ((BinaryLinear.parabolic P).inv_mem hg) _ hf
      have he : (g⁻¹).symm.dualMap (g.symm.dualMap f) = f := by
        apply LinearMap.ext
        intro v
        change f (g.symm (g v)) = f v
        rw [LinearEquiv.symm_apply_apply]
      exact he ▸ hh
    · exact stable g hg _

/-- Contragredience transports the full marked parabolic, not just its isomorphism type. -/
theorem dualActor_map_parabolic (P : Submodule (ZMod 2) NaturalSpace) :
    (BinaryLinear.parabolic P).map dualActor.toMonoidHom =
      BinaryLinear.parabolic (dualPlane P) := by
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact (dualActor_mem_parabolic_iff P k).mpr hk
  · intro hg
    obtain ⟨k, rfl⟩ := dualActor.surjective g
    exact ⟨k, (dualActor_mem_parabolic_iff P k).mp hg, rfl⟩

theorem dualPlane_finrank (P : Submodule (ZMod 2) NaturalSpace)
    (hP : Module.finrank (ZMod 2) P = 2) :
    Module.finrank (ZMod 2) (dualPlane P) = 2 := by
  rw [dualPlane, LinearEquiv.finrank_map_eq]
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq P
  have hfour : Module.finrank (ZMod 2) NaturalSpace = 4 := by simp [NaturalSpace]
  omega

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment
