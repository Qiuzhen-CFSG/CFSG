module

public import Theory.Representation.HexacodeAction.SecondaryEvenMarking
public import Theory.Representation.HexacodeAction.SecondaryOddMarking
public import Theory.Representation.AlternatingSixSecondaryRecognition
public import Theory.Representation.BinaryAlternatingSixModels.DuadCoreQuadratic

/-!
# The secondary natural module in the original six-coordinate marking

The original whole-product cubic bound supplies an even equality actor,
including when the initial actor is odd. Fixed-free full movement gives the
two literal natural models. The second model costs three dimensions on this
same even actor, contradicting its exact cost two. Thus the entire secondary
module is the first natural module in the original marking, and its literal
duad eight-core cannot act quadratically.

Source: Aschbacher--Smith 12.7.20, printed p.846.
-/

public section
open Subgroup Representation Representation.BinaryOffender Atlas.Codes
open Theory.SpecificGroups.SymmetricSix BinaryAlternatingSix
namespace Representation.Hexacode.SecondaryMarkedNatural

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The whole secondary module is the first natural module for the original
coordinate quotient. No group automorphism or untracked module quotient is used. -/
theorem natural_of_cubic_product
    (σ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) V)
    (hf : Function.Injective σ)
    (hz : fixedSpace σ (alternatingGroup (Fin 6)) = ⊥)
    (hm : subspaceCommutator σ ⊤ (alternatingGroup (Fin 6)) = ⊤)
    (hb : cubicRatio (action.prod (σ.comp hexCoordinateSixHom)) ≤ 2) :
    Nonempty (σ.Equiv firstNatural) := by
  obtain ⟨B,hBe,hB,_,_,_,hs,hBo,hso⟩ :=
    SecondaryOddMarking.cubic_product_even_actor σ hf hb
  let E := B.map hexCoordinateSixHom
  have hE : IsElementaryTwo E := hso.1
  have hr : 2 ≤ rank E := hs ▸ hso.2
  have hcard : 2 < Nat.card E := by
    rw [hE.card_eq_two_pow_rank]
    have hh : 2^2 ≤ 2 ^ rank E := Nat.pow_le_pow_right (by decide) hr
    omega
  obtain ⟨t,htE,hte,ht1⟩ :=
    AlternatingSixInvolutionDisplacement.even_element_of_card_gt_two E hcard
  let : IsElementaryAbelian 2 E := hE.2
  have ht : orderOf t = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian t htE) ht1
  rcases AlternatingSixSecondaryRecognition.natural_models_of_even_actor
      σ hf hz hm E t ht hte htE hs.le with hfirst | hsecond
  · exact hfirst
  · obtain ⟨e⟩ := hsecond
    have hcost := SecondaryEvenMarking.full_even_offender_second_cost B hBe hBo
    have heq : fixedCodim σ E = fixedCodim secondNatural E := by
      simpa only [Subgroup.map_id] using
        (fixedCodim_map_equivariant σ secondNatural (MonoidHom.id _) e.toLinearEquiv
          (fun g v => IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v) E)
    change fixedCodim σ E = 2 at hs
    change 3 ≤ fixedCodim secondNatural E at hcost
    omega

/-- The actual whole-product bound excludes quadraticity of the eight actor
in its retained duad-core marking, including the specified inner relabeling. -/
theorem not_quadratic_of_cubic_product_duad_marking
    (σ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) V)
    (hf : Function.Injective σ)
    (hz : fixedSpace σ (alternatingGroup (Fin 6)) = ⊥)
    (hm : subspaceCommutator σ ⊤ (alternatingGroup (Fin 6)) = ⊤)
    (hb : cubicRatio (action.prod (σ.comp hexCoordinateSixHom)) ≤ 2)
    (A : Subgroup (Equiv.Perm (Fin 6))) (g : Equiv.Perm (Fin 6))
    (hA : A.map (MulAut.conj g).toMonoidHom =
      DuadCalculation.productCore.map duadProductHom) :
    ¬ IsQuadratic σ A := by
  obtain ⟨e⟩ := natural_of_cubic_product σ hf hz hm hb
  exact not_quadratic_of_equiv_firstNatural_of_conjugate_duadCore σ e A g hA

end Representation.Hexacode.SecondaryMarkedNatural
