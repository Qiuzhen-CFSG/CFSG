module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair.Setup
public import Theory.Representation.SymplecticConjugatePair.OddOrder.Residual

/-!
# SQTK covers and the field-actor step of H.7

Hypothesis (!) is an actual surjection from a finite group satisfying the
genuine SQTK definition. The H.0.1 premise states its exact dimension
formula, with an actual field automorphism and semilinear action. Its
proof belongs to the earlier chapter development. Here that formula
excludes field actors from the small-displacement case of H.7.

Source: Aschbacher–Smith, standing setup and H.0.1 on printed p.377,
and H.7 on p.389, combined manuscript of 1 March 2004.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair
open SymplecticConjugatePair SymplecticConjugatePair.OddOrder
open Representation.BinaryOffender Theory.SpecificGroups.SymplecticFour
universe cu cv

/-- Hypothesis (!) as an actual finite SQTK cover. -/
def IsSQTKImage (K : CFSG.Quasithin.GroupClass.{cu}) (M : Type cv) [Group M] : Prop :=
  ∃ (G : Type cu) (_ : Group G) (_ : Finite G), CFSG.Quasithin.IsSQTK K G ∧
    ∃ π : G →* M, Function.Surjective π

variable {F M V : Type*} [Field F] [Algebra (ZMod 2) F] [Group M]
  [AddCommGroup V] [Module F V] [Module (ZMod 2) V]

/-- The equality in H.0.1, with semilinearity and the nontrivial field
 automorphism specified on the actual vector space. -/
def FieldAutomorphismFormula (ρ : Representation (ZMod 2) M V) : Prop :=
  ∀ (p : ℕ) (x : M), p.Prime → Odd p → orderOf x = p →
    ∀ σ : F ≃+* F, orderOf σ = p →
      (∀ (a : F) (v : V), ρ x (a • v) = σ a • ρ x v) →
      p * fixedCodim ρ (Subgroup.zpowers x) =
        (p - 1) * Module.finrank (ZMod 2) F * Module.finrank F V

variable [Finite F]

/-- H.0.1 excludes small displacement for a genuine field actor. -/
theorem Setup.fieldActor_bounds (s : Setup F M) {n : ℕ} (hF : Nat.card F = 2^n)
    (hH01 : FieldAutomorphismFormula (F := F) s.action)
    {p : ℕ} {x : M} (hp : p.Prime) (ho : Odd p) (hx : orderOf x = p)
    (σ : F ≃+* F) (hσ : orderOf σ = p)
    (hsemi : ∀ (a : F) (v : Space F), s.action x (a • v) = σ a • s.action x v) :
    4*n ≤ fixedCodim s.action (Subgroup.zpowers x) ∧
      (n = 1 → 6 ≤ fixedCodim s.action (Subgroup.zpowers x)) := by
  have he := hH01 p x hp ho hx σ hσ hsemi
  rw [coefficient_finrank hF] at he
  have hd : Module.finrank F (Space F) = 8 := by
    simp [Space, Theory.SpecificGroups.SymplecticFour.Vector, Module.finrank_prod]
  rw [hd] at he
  have hp3 : 3 ≤ p := by
    obtain ⟨k, hk⟩ := ho
    have := hp.two_le
    omega
  have hs : p - 1 + 1 = p := by omega
  constructor
  · nlinarith
  · intro hn
    subst n
    nlinarith

/-- The field-automorphism case cannot occur below the H.7 threshold. -/
theorem Setup.not_fieldActor_of_small_fixedCodim (s : Setup F M) {n : ℕ}
    (hF : Nat.card F = 2^n) (hH01 : FieldAutomorphismFormula (F := F) s.action)
    {p : ℕ} {x : M} (hp : p.Prime) (ho : Odd p) (hx : orderOf x = p)
    (hsmall : fixedCodim s.action (Subgroup.zpowers x) < 4*n)
    (σ : F ≃+* F) (hσ : orderOf σ = p) :
    ¬ ∀ (a : F) (v : Space F), s.action x (a • v) = σ a • s.action x v := by
  intro hsemi
  exact (Nat.not_le_of_lt hsmall) (s.fieldActor_bounds hF hH01 hp ho hx σ hσ hsemi).1
end CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair

namespace CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair
universe u v w
variable {K : CFSG.Quasithin.GroupClass.{u}} {M : Type v} [Group M]

/-- A local subgroup is still an image of a finite SQTK group: take its
literal preimage in the original cover. -/
theorem IsSQTKImage.subgroup (h : IsSQTKImage K M) (J : Subgroup M) :
    IsSQTKImage K J := by
  obtain ⟨G, hG, hfin, hsq, π, hπ⟩ := h
  exact ⟨J.comap π, inferInstance, inferInstance, hsq.subgroup (J.comap π),
    π.subgroupComap J, π.subgroupComap_surjective_of_surjective J hπ⟩

/-- Composition of actual surjections preserves the cover formulation of (!). -/
theorem IsSQTKImage.of_surjective {N : Type w} [Group N]
    (h : IsSQTKImage K M) (f : M →* N) (hf : Function.Surjective f) :
    IsSQTKImage K N := by
  obtain ⟨G, hG, hfin, hsq, π, hπ⟩ := h
  exact ⟨G, hG, hfin, hsq, f.comp π, hf.comp hπ⟩
end CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair
