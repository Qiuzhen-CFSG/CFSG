module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Basic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.CentralExclusion.Cohomology
public import Theory.Representation.SLHigherNaturalFirstCohomology
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model

/-!
# Cohomology of the identified natural and dual L₄(2) modules

The matrix-to-linear-automorphism isomorphism transports I.1.6(6) to the
specified actor. Contragredience, expressed in dual coordinates, is an
injective endomorphism of the finite general linear group and hence an
automorphism. It transports natural H¹ vanishing to the dual. Coefficient
isomorphisms and double-dual evaluation then cover both alternatives in
`IsNaturalOrDual`, without changing the given identification of the actor.

Source: Aschbacher–Smith, I.1.6(6), printed p.408, applied in 13.8.25,
printed p.961. The underlying natural H¹ calculation is proved in
`Theory.Representation.SLHigherNaturalFirstCohomology`.
-/

@[expose] public section

open Representation Representation.OneCohomology
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.CentralExclusion
open ChiefFactors

noncomputable def dualCoordinates : Module.Dual (ZMod 2) NaturalSpace ≃ₗ[ZMod 2] NaturalSpace :=
  (Module.finBasis (ZMod 2) NaturalSpace).toDualEquiv.symm

noncomputable def graphHom : BinaryLinear.GL NaturalSpace →* BinaryLinear.GL NaturalSpace where
  toFun g := (dualCoordinates.symm.trans g.symm.dualMap).trans dualCoordinates
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change dualCoordinates (dualCoordinates.symm v) = v
    exact dualCoordinates.apply_symm_apply v
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    change dualCoordinates ((g * h).symm.dualMap (dualCoordinates.symm v)) =
      dualCoordinates (g.symm.dualMap (dualCoordinates.symm
        (dualCoordinates (h.symm.dualMap (dualCoordinates.symm v)))))
    rw [dualCoordinates.symm_apply_apply]
    rfl

lemma graphHom_injective : Function.Injective graphHom := by
  intro g h he
  have hd : g.symm.dualMap = h.symm.dualMap := by
    apply LinearEquiv.ext
    intro f
    apply dualCoordinates.injective
    have heval := congrArg (fun e : BinaryLinear.GL NaturalSpace => e (dualCoordinates f)) he
    change dualCoordinates (g.symm.dualMap (dualCoordinates.symm (dualCoordinates f))) =
      dualCoordinates (h.symm.dualMap (dualCoordinates.symm (dualCoordinates f))) at heval
    simpa only [dualCoordinates.symm_apply_apply] using heval
  have hi : g.symm = h.symm := by
    apply LinearEquiv.ext
    intro x
    apply sub_eq_zero.mp
    apply (Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).mp
    intro f
    have hf := LinearMap.congr_fun (LinearEquiv.congr_fun hd f) x
    simpa only [map_sub, LinearEquiv.dualMap_apply] using sub_eq_zero.mpr hf
  exact congrArg LinearEquiv.symm hi

lemma finite_GL : Finite (BinaryLinear.GL NaturalSpace) :=
  Finite.of_injective (fun g : BinaryLinear.GL NaturalSpace => (g : NaturalSpace → NaturalSpace))
    (fun _ _ h => LinearEquiv.ext (congrFun h))

noncomputable def graph : MulAut (BinaryLinear.GL NaturalSpace) := by
  let : Finite (BinaryLinear.GL NaturalSpace) := finite_GL
  exact MulEquiv.ofBijective graphHom ⟨graphHom_injective,
    Finite.surjective_of_injective graphHom_injective⟩

lemma natural_H1 (H : Type*) [Group H] (eH : H ≃* BinaryLinear.GL NaturalSpace) :
    Module.finrank (ZMod 2) (H1 (naturalAction eH)) = 0 := by
  let eG := (BinaryLinear.OuterCyclic.slEquivLinear 4).trans eH.symm
  let e := H1Congr (specialLinearNatural (k := ZMod 2) 4) (naturalAction eH)
    eG (LinearEquiv.refl (ZMod 2) NaturalSpace) (by
      intro g v
      change specialLinearNatural 4 g v = eH (eH.symm _) v
      rw [eH.apply_symm_apply]
      rfl)
  rw [← e.finrank_eq]
  exact SLHigherNatural.finrank_H1_sl4_two

lemma natural_dual_H1 (H : Type*) [Group H] (eH : H ≃* BinaryLinear.GL NaturalSpace) :
    Module.finrank (ZMod 2) (H1 (naturalAction eH).dual) = 0 := by
  let e := H1Congr (naturalAction eH).dual
    (naturalAction (MulEquiv.refl (BinaryLinear.GL NaturalSpace)))
    (eH.trans graph) dualCoordinates (by
      intro g f
      change dualCoordinates (((eH g⁻¹).toLinearMap).dualMap f) =
        dualCoordinates ((eH g).symm.dualMap (dualCoordinates.symm (dualCoordinates f)))
      rw [map_inv, dualCoordinates.symm_apply_apply]
      rfl)
  rw [e.finrank_eq]
  exact natural_H1 _ _

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]

lemma naturalOrDual_dual_H1 (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (h : IsNaturalOrDual ρ eH) :
    Module.finrank (ZMod 2) (H1 ρ.dual) = 0 := by
  rcases h with ⟨e, he⟩ | ⟨e, he⟩
  · let c := H1Congr ρ.dual (naturalAction eH).dual (MulEquiv.refl H)
      e.symm.dualMap (dual_equivariant e he)
    rw [c.finrank_eq]
    exact natural_dual_H1 H eH
  · let c := H1Congr ρ.dual (naturalAction eH).dual.dual (MulEquiv.refl H)
      e.symm.dualMap (dual_equivariant e he)
    let d := H1Congr (naturalAction eH).dual.dual (naturalAction eH) (MulEquiv.refl H)
      (Module.evalEquiv (ZMod 2) NaturalSpace).symm
      (fun g f => LinearMap.congr_fun
        ((evaluationIntertwining (naturalAction eH)).isIntertwining' g) f)
    rw [c.finrank_eq, d.finrank_eq]
    exact natural_H1 H eH

lemma naturalOrDual_finrank (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (h : IsNaturalOrDual ρ eH) :
    Module.finrank (ZMod 2) U = 4 := by
  rcases h with ⟨e, _⟩ | ⟨e, _⟩
  · rw [e.finrank_eq]
    simp [NaturalSpace]
  · rw [e.finrank_eq, Subspace.dual_finrank_eq]
    simp [NaturalSpace]

lemma natural_not_trivial (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (h : IsNatural ρ eH) :
    ¬ ∀ g u, ρ g u = u := by
  rintro hf
  obtain ⟨e, he⟩ := h
  let s : BinaryLinear.GL NaturalSpace :=
    LinearEquiv.piCongrLeft (ZMod 2) (fun _ : Fin 4 => ZMod 2) (Equiv.swap 0 1)
  have hs : ∀ v, s v = v := by
    intro v
    obtain ⟨u, rfl⟩ := e.surjective v
    have ht := he (eH.symm s) u
    rw [eH.apply_symm_apply, hf] at ht
    exact ht.symm
  have ht := congrFun (hs (Pi.single 0 1)) 0
  norm_num [s, LinearEquiv.piCongrLeft] at ht

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.CentralExclusion
