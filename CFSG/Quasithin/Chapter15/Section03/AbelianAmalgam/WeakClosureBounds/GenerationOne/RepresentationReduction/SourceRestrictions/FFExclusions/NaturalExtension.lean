module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.ModuleIdentifications

/-!
# Constructing the nonsplit natural extension

If an invariant submodule W supplements C_V(D), inclusion induces the
canonical equivariant isomorphism W/C_W(D) ≃ V/C_V(D). Its injectivity uses
the literal fixed spaces, and surjectivity uses the supplement identity.
A natural identification of W/C_W(D) consequently constructs the required
central extension of V, with invariant kernel exactly C_V(D).

In the source SL2 application, W is the commutator submodule supplied by
B.5.1. The supplement identity and its natural central quotient still have
to be deduced from that theorem, including for an exchanged component.
The final helper combines these inputs with the first natural quotient and
the existing two-layer Borel calculation. It assumes neither the second
extension nor the desired fixed-space conclusion, and never assumes splitting.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), B.5.1(1),(5),
printed pp.99--100, and the exceptional extension in 15.3.65, p.1152.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions
variable {D E V X : Type*} [Group D] [Group E]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) D V)

/-- The invariant submodule of vectors fixed by the entire acting group. -/
noncomputable abbrev fixedKernel : Subrepresentation ρ where
  toSubmodule := fixedSpace ρ ⊤
  apply_mem_toSubmodule g v hv := by
    have hg : ρ g v = v := hv ⟨g, Subgroup.mem_top g⟩
    rw [hg]
    exact hv

/-- The literal quotient map induced by inclusion W into V. -/
noncomputable def fixedQuotientInclusion (W : Subrepresentation ρ) :
    (W ⧸ fixedSpace W.toRepresentation ⊤) →ₗ[ZMod 2] (V ⧸ fixedSpace ρ ⊤) :=
  (fixedSpace W.toRepresentation ⊤).liftQ
    ((fixedSpace ρ ⊤).mkQ.comp W.toSubmodule.subtype) (by
      intro w hw
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      intro g
      exact congrArg (fun x : W => (x : V)) (hw g))

/-- On quotient representatives the induced map is the original inclusion. -/
@[simp] theorem fixedQuotientInclusion_mk (W : Subrepresentation ρ) (w : W) :
    fixedQuotientInclusion ρ W ((fixedSpace W.toRepresentation ⊤).mkQ w) =
      (fixedSpace ρ ⊤).mkQ w := rfl

/-- No nonzero coset becomes zero: the two fixed spaces are compatible with inclusion. -/
theorem fixedQuotientInclusion_injective (W : Subrepresentation ρ) :
    Function.Injective (fixedQuotientInclusion ρ W) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro a ha
  obtain ⟨w, rfl⟩ := (fixedSpace W.toRepresentation ⊤).mkQ_surjective a
  change (fixedSpace ρ ⊤).mkQ (w : V) = 0 at ha
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  have hw := (Submodule.Quotient.mk_eq_zero _).mp ha
  intro g
  exact Subtype.ext (hw g)

/-- A supplement to the fixed space surjects onto the quotient by fixed vectors. -/
theorem fixedQuotientInclusion_surjective (W : Subrepresentation ρ)
    (hspan : W.toSubmodule ⊔ fixedSpace ρ ⊤ = ⊤) :
    Function.Surjective (fixedQuotientInclusion ρ W) := by
  intro a
  obtain ⟨v, rfl⟩ := (fixedSpace ρ ⊤).mkQ_surjective a
  have hv : v ∈ W.toSubmodule ⊔ fixedSpace ρ ⊤ := by rw [hspan]; trivial
  obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.mp hv
  refine ⟨(fixedSpace W.toRepresentation ⊤).mkQ ⟨w, hw⟩, ?_⟩
  have hc0 : (fixedSpace ρ ⊤).mkQ c = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hc
  rw [fixedQuotientInclusion_mk, map_add, hc0, add_zero]

/-- The quotient inclusion intertwines the original induced actions. -/
theorem fixedQuotientInclusion_equivariant (W : Subrepresentation ρ) (g : D)
    (v : W ⧸ fixedSpace W.toRepresentation ⊤) :
    fixedQuotientInclusion ρ W ((fixedKernel W.toRepresentation).quotientRepresentation g v) =
      (fixedKernel ρ).quotientRepresentation g (fixedQuotientInclusion ρ W v) := by
  obtain ⟨w, rfl⟩ := (fixedSpace W.toRepresentation ⊤).mkQ_surjective v
  rfl

/-- A supplement to fixed vectors gives the canonical equivalence of central quotients. -/
noncomputable def fixedQuotientEquiv (W : Subrepresentation ρ)
    (hspan : W.toSubmodule ⊔ fixedSpace ρ ⊤ = ⊤) :
    (W ⧸ fixedSpace W.toRepresentation ⊤) ≃ₗ[ZMod 2] (V ⧸ fixedSpace ρ ⊤) :=
  LinearEquiv.ofBijective (fixedQuotientInclusion ρ W)
    ⟨fixedQuotientInclusion_injective ρ W, fixedQuotientInclusion_surjective ρ W hspan⟩

/-- Construct the central extension from a natural central quotient of a supplement; no splitting is imposed. -/
noncomputable def centralExtensionOfFixedQuotient (W : Subrepresentation ρ)
    (hspan : W.toSubmodule ⊔ fixedSpace ρ ⊤ = ⊤)
    (σ : Representation (ZMod 2) E X) (φ : D →* E)
    (e : (W ⧸ fixedSpace W.toRepresentation ⊤) ≃ₗ[ZMod 2] X)
    (he : ∀ g v, e ((fixedKernel W.toRepresentation).quotientRepresentation g v) =
      σ (φ g) (e v)) : CentralExtensionIdentification ρ σ φ where
  kernel := fixedKernel ρ
  centralized := le_rfl
  linearEquiv := (fixedQuotientEquiv ρ W hspan).symm.trans e
  equivariant g v := by
    let j := fixedQuotientEquiv ρ W hspan
    have hj : j ((fixedKernel W.toRepresentation).quotientRepresentation g (j.symm v)) =
        (fixedKernel ρ).quotientRepresentation g v := by
      change fixedQuotientInclusion ρ W _ = _
      rw [fixedQuotientInclusion_equivariant]
      change (fixedKernel ρ).quotientRepresentation g (j (j.symm v)) = _
      rw [j.apply_symm_apply]
    have hi := congrArg j.symm hj
    rw [j.symm_apply_apply] at hi
    change e (j.symm ((fixedKernel ρ).quotientRepresentation g v)) = σ (φ g) (e (j.symm v))
    rw [← hi]
    exact he g (j.symm v)

/-- The first natural quotient and the second supplement quotient suffice for the SL2 Borel calculation. -/
theorem slTwo_fixedSpace_le_of_natural_fixed_quotient
    [Finite D] {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
    (I : Subrepresentation ρ) (φ : D →* Matrix.SpecialLinearGroup (Fin 2) F)
    (e₀ : (I ⧸ fixedSpace I.toRepresentation ⊤) ≃ₗ[ZMod 2] (Fin 2 → F))
    (he₀ : ∀ g v, e₀ ((fixedKernel I.toRepresentation).quotientRepresentation g v) =
      specialLinearNatural 2 (φ g) (e₀ v))
    (W : Subrepresentation I.quotientRepresentation)
    (hspan : W.toSubmodule ⊔ fixedSpace I.quotientRepresentation ⊤ = ⊤)
    (e : (W ⧸ fixedSpace W.toRepresentation ⊤) ≃ₗ[ZMod 2] (Fin 2 → F))
    (he : ∀ g v, e ((fixedKernel W.toRepresentation).quotientRepresentation g v) =
      specialLinearNatural 2 (φ g) (e v))
    (B : Subgroup D) (hindex : Odd B.index)
    (hB : B.map φ = Matrix.SpecialLinearGroup.rankOneBorel F)
    (hF : 2 < Nat.card F) : fixedSpace ρ B ≤ fixedSpace ρ ⊤ := by
  let d₀ : CentralExtensionIdentification I.toRepresentation
      (restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 2)) φ :=
    ⟨fixedKernel I.toRepresentation, le_rfl, e₀, he₀⟩
  let d₁ := centralExtensionOfFixedQuotient I.quotientRepresentation W hspan
    (restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 2)) φ e he
  exact slTwo_fixedSpace_le_of_two_identifications ρ I φ d₀ d₁ B hindex hB hF

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions
