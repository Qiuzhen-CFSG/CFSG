module

public import Theory.Representation.CentralizerField
public import Theory.Representation.BinaryOffender.IrreducibleSection

/-!
# Faithful descent of an Irr⁺ centralizer

Every X-endomorphism of I preserves C_I(X), and therefore induces an
endomorphism of the literal quotient I/C_I(X). If I = [I,X], this ring
homomorphism is injective: a map whose image is fixed by X vanishes on
each action difference and thus on its span I.

Passing to units gives the specified injective homomorphism from the
centralizer of the actual action image on I into the quotient endomorphism
ring's units. Equivalently it embeds in the quotient linear centralizer.
When the quotient is irreducible, its actual endomorphism ring is a finite
field of characteristic two; the embedded centralizer is cyclic of odd order.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, A.1.41, printed p.31. The direct kernel argument
uses only full commutator generation, so does not require the source's
additional residual and two-core hypotheses.
-/

@[expose] public section

open Representation Representation.CentralizerField
namespace Representation.BinaryOffender.CentralizerField
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (X : Subgroup G) (I : Submodule (ZMod 2) V)
  (hI : X ≤ subspaceStabilizer ρ I)
local notation "σ" => (Subrepresentation.toRepresentation (invariantSubspace ρ X I hI) :
  Representation (ZMod 2) X I)
local notation "τ" => centralQuotientRepresentation ρ X I hI
local notation "C" => Submodule.comap (Submodule.subtype I) (fixedSpace ρ X)

/-- An equivariant endomorphism preserves the literal fixed subspace C_I(X). -/
theorem end_preserves_centralSubspace (f : IntertwiningMap σ σ) :
    C ≤ (C).comap f.toLinearMap := by
  intro v hv
  change ∀ x : X, ρ x (f v) = f v
  intro x
  have hx : σ x v = v := Subtype.ext (hv x)
  exact congrArg Subtype.val ((IntertwiningMap.isIntertwining σ σ f x v).symm.trans (congrArg f hx))

/-- The ring homomorphism induced on the literal quotient I/C_I(X). -/
noncomputable def quotientEndHom : IntertwiningMap σ σ →+* IntertwiningMap τ τ where
  toFun f :=
    { toLinearMap := (C).mapQ C f.toLinearMap (end_preserves_centralSubspace ρ X I hI f)
      isIntertwining' x := by
        apply LinearMap.ext
        intro q
        induction q using Submodule.Quotient.induction_on with
        | _ v =>
          exact congrArg (C).mkQ (IntertwiningMap.isIntertwining σ σ f x v) }
  map_one' := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ v => rfl
  map_mul' f g := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ v => rfl
  map_zero' := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ v => exact (C).mkQ.map_zero
  map_add' f g := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ v => exact (C).mkQ.map_add (f v) (g v)

/-- The quotient endomorphism sends the class of v to the class of f(v). -/
@[simp] theorem quotientEndHom_mk (f : IntertwiningMap σ σ) (v : I) :
    quotientEndHom ρ X I hI f ((C).mkQ v) = (C).mkQ (f v) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Full commutator generation makes descent of endomorphisms injective. -/
theorem quotientEndHom_injective (hfull : subspaceCommutator ρ I X = I) :
    Function.Injective (quotientEndHom ρ X I hI) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro f hf
  have hfix (v : I) : (f v : V) ∈ fixedSpace ρ X := by
    have he : (C).mkQ (f v) = 0 :=
      congrArg (fun e : IntertwiningMap τ τ => e ((C).mkQ v)) hf
    exact (Submodule.Quotient.mk_eq_zero C).mp he
  have hcomm : subspaceCommutator ρ I X ≤ f.toLinearMap.ker.map I.subtype := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, v, hv, rfl⟩
    let v' : I := ⟨v, hv⟩
    let w : I := σ ⟨x, hx⟩ v'
    refine ⟨w - v', ?_, rfl⟩
    change f (w - v') = 0
    rw [map_sub]
    change f (σ ⟨x, hx⟩ v') - f v' = 0
    rw [IntertwiningMap.isIntertwining σ σ f]
    apply sub_eq_zero.mpr
    apply Subtype.ext
    exact hfix v' ⟨x, hx⟩
  rw [hfull] at hcomm
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  obtain ⟨w, hw, he⟩ := hcomm v.property
  have hwe : w = v := Subtype.ext he
  subst w
  exact hw

/-- The original linear centralizer acts by units of the actual quotient endomorphism ring. -/
noncomputable def centralizerToQuotientUnits :
    linearCentralizer σ →* (IntertwiningMap τ τ)ˣ :=
  (Units.map (quotientEndHom ρ X I hI).toMonoidHom).comp
    (centralizerUnitsEquiv σ).toMonoidHom

/-- The centralizer homomorphism is the action on quotient classes. -/
@[simp] theorem centralizerToQuotientUnits_mk (c : linearCentralizer σ) (v : I) :
    (centralizerToQuotientUnits ρ X I hI c).val ((C).mkQ v) = (C).mkQ (c.val.val v) := rfl

/-- The action on quotient classes faithfully represents the original centralizer. -/
theorem centralizerToQuotientUnits_injective (hfull : subspaceCommutator ρ I X = I) :
    Function.Injective (centralizerToQuotientUnits ρ X I hI) := by
  intro c d he
  apply (centralizerUnitsEquiv σ).injective
  apply Units.ext
  apply quotientEndHom_injective ρ X I hI hfull
  exact congrArg Units.val he

/-- The original centralizer mapped into the centralizer of the quotient action image. -/
noncomputable def centralizerQuotientHom :
    linearCentralizer σ →* linearCentralizer τ :=
  (centralizerUnitsEquiv τ).symm.toMonoidHom.comp
    (centralizerToQuotientUnits ρ X I hI)

/-- The homomorphism into the quotient linear centralizer has the expected action on classes. -/
@[simp] theorem centralizerQuotientHom_mk (c : linearCentralizer σ) (v : I) :
    (centralizerQuotientHom ρ X I hI c).val.val ((C).mkQ v) =
      (C).mkQ (c.val.val v) := rfl

/-- The centralizer homomorphism into the quotient linear centralizer is injective. -/
theorem centralizerQuotientHom_injective (hfull : subspaceCommutator ρ I X = I) :
    Function.Injective (centralizerQuotientHom ρ X I hI) :=
  (centralizerUnitsEquiv τ).symm.injective.comp
    (centralizerToQuotientUnits_injective ρ X I hI hfull)

/-- The original centralizer is isomorphic to the specified subgroup of the quotient centralizer. -/
noncomputable def centralizerQuotientRangeEquiv (hfull : subspaceCommutator ρ I X = I) :
    linearCentralizer σ ≃* (centralizerQuotientHom ρ X I hI).range :=
  MonoidHom.ofInjective (centralizerQuotientHom_injective ρ X I hI hfull)

variable [FiniteDimensional (ZMod 2) V]

/-- An Irr⁺ section has a cyclic linear centralizer of odd order. -/
theorem centralizer_cyclic_odd (hfull : subspaceCommutator ρ I X = I)
    (hirr : IsIrreducible τ) :
    IsCyclic (linearCentralizer σ) ∧ Odd (Nat.card (linearCentralizer σ)) := by
  let := hirr
  let := units_isCyclic τ
  have hi := centralizerToQuotientUnits_injective ρ X I hI hfull
  exact ⟨isCyclic_of_injective (centralizerToQuotientUnits ρ X I hI) hi,
    (units_odd_card τ).of_dvd_nat
      (Subgroup.card_dvd_of_injective (centralizerToQuotientUnits ρ X I hI) hi)⟩
end Representation.BinaryOffender.CentralizerField
