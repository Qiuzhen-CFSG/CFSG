module

public import Theory.Representation.G2NaturalTransport.Layer
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing

/-!
# The I.2.3 natural-quotient interface in B.4.6

The source hypotheses supply a full G₂-model isomorphism, its natural
module on the literal V/C_V(L), and F*(G)=E(L). The theorem below derives
the normal layer, the actual derived marking and invariance of C_V(L),
then applies the proved commutant and semilinear transport to the original
ambient action. This supplies the commutant assertion of B.4.6(1), its
nonzero orbit assertion (2), and the change of model for fixed spaces and
best offenders on the natural quotient.

The covering dimension, Weyl geometry and the remaining clauses of B.4.6
are separate assertions. Source: Aschbacher--Smith, combined manuscript
of 1 March 2004, I.2.3, printed p.413, and B.4.6, pp.88--90.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterB.Section04.G2.Transport
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Atlas.G2.Natural Atlas.G2.Natural.Transport
noncomputable section
variable {F G V : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The natural-quotient consequences needed from I.2.3 in B.4.6. The input
is the full natural L-module marking on the literal quotient and F*(G)=E(L).
Normality of E(L), its marked derived action, and stability of C_V(L) are derived.
This supplies the commutant of part (1), part (2), and transport for the later
fixed-space and offender calculations. -/
theorem natural_quotient_interface (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
    (e : L ≃* Atlas.G2.Model F)
    (E : (V ⧸ fixedSpace ρ L) ≃ₗ[ZMod 2] Space F)
    (hE : ∀ l : L, ∀ v, E ((fixedSpace ρ L).mkQ (ρ l v)) =
      action F (e l) (E ((fixedSpace ρ L).mkQ v)))
    (hF : generalizedFitting G = layerIn L) :
    fixedSpace ρ L = fixedSpace ρ (layerIn L) ∧
    ∃ η : Representation (ZMod 2) G (V ⧸ fixedSpace ρ L),
      (∀ g v, η g ((fixedSpace ρ L).mkQ v) = (fixedSpace ρ L).mkQ (ρ g v)) ∧
      (∀ g, ∃ s : F ≃+* F, ∀ c x,
        E (η g (E.symm (c • E x))) = s c • E (η g x)) ∧
      (∀ f : (V ⧸ fixedSpace ρ L) →+ (V ⧸ fixedSpace ρ L),
        (∀ l : L, ∀ x, f (η l x) = η l (f x)) ↔
          ∃ c : F, ∀ x, E (f x) = c • E x) ∧
      (∀ x y : V ⧸ fixedSpace ρ L, x ≠ 0 → y ≠ 0 → ∃ l : L, η l x = y) ∧
      (∀ A : Subgroup L,
        (fixedSpace η (A.map L.subtype)).map E.toLinearMap =
          fixedSpace (restrictScalars (k := ZMod 2) (action F)) (A.map e.toMonoidHom)) ∧
      (∀ A : Subgroup L, fixedCodim η (A.map L.subtype) =
        fixedCodim (restrictScalars (k := ZMod 2) (action F)) (A.map e.toMonoidHom)) ∧
      (∀ A : Subgroup L, IsOffender (η.comp L.subtype) A ↔
        IsOffender (restrictScalars (k := ZMod 2) (action F)) (A.map e.toMonoidHom)) ∧
      (∀ A : Subgroup L, IsBestOffender (η.comp L.subtype) A ↔
        IsBestOffender (restrictScalars (k := ZMod 2) (action F)) (A.map e.toMonoidHom)) := by
  let : (layerIn L).Normal := by rw [← hF]; infer_instance
  let d := marking ρ L e E hE
  refine ⟨d.fixedSpace_eq, d.quotientAction, d.quotientAction_mk, d.semilinear,
    d.commutes_iff_scalar, ?_, d.fixedSpace_map, d.fixedCodim_eq,
    d.offender_iff, d.bestOffender_iff⟩
  intro x y hx hy
  exact d.transitive hx hy
end
end CFSG.Quasithin.ChapterB.Section04.G2.Transport
