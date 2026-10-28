module

public import Theory.Representation.QuadraticFourGroup.Models
public import Theory.Representation.QuadraticFourGroup.CubicSections.Descent
public import Theory.Representation.QuadraticFourGroup.CubicSections.Dihedral
public import Theory.Representation.QuadraticFourGroup.CubicSections.FixedSpace
public import Theory.Representation.QuadraticFourGroup.CubicSections.Swapped
public import Theory.Representation.QuadraticFourGroup.CubicSections.SplitSection
public import Theory.Representation.QuadraticFourGroup.CubicSections.SectionReduction
public import Theory.Representation.QuadraticFourGroup.CubicSections.SplitAction
public import Theory.Representation.QuadraticFourGroup.CubicSections.FactorInvolutions

/-!
# Cubic actions on quadratic four-group sections

The current results prove descent of all irreducible orbit sections through
`O₂(E)`, cubic fixed-space transfer to actual subquotients, and the corrected
swapped-dihedral calculation from GLS, volume 2, Theorem 25.14, Steps 2–4.
The two-factor model remains an explicit input. The faithful split-action
reduction and the concrete-factor inverters are now assembled below; the
recognition consumer supplies the model.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace Representation.QuadraticFourGroup

universe u v w

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) G V} {L B : Subgroup G} {a : G}

/-!
The final Step 2--4 assembly is stated for an arbitrary irreducible section.
The model is deliberately an explicit input: recognition supplies it at the
consumer, while this theorem discharges the representation-theoretic part.
-/

/-- The descended action of every nontrivial orbit section is cubic-fixed-free
on either concrete factor. The section kernel contains the intrinsic two-core,
and the descended action is realized as an actual section of a faithful split
ambient action.

This is GLS, volume 2, Theorem 25.14, Steps 2--4. -/
theorem exists_cubic_fixed_free_section
    [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) W]
    (h : Hypotheses ρ L B a) (M : TwoFactorModel (componentOrbit L B))
    (σ : Representation (ZMod 2) (componentOrbit L B) W)
    (hs : IsIrreducibleSection (ρ.comp (componentOrbit L B).subtype) σ)
    (hn : ¬ σ.IsTrivial) :
    let _ := hs.1
    ∃ σbar : Representation (ZMod 2) (Factor M.n × Factor M.n) W,
      σbar.comp M.projection = σ ∧ σbar.IsIrreducible ∧ ¬ σbar.IsTrivial ∧
      pCore 2 (componentOrbit L B) ≤ σ.ker ∧
      (∀ x : Factor M.n, orderOf x = 3 →
        ∀ w, σbar (x, 1) w = w → w = 0) ∧
      (∀ x : Factor M.n, orderOf x = 3 →
        ∀ w, σbar (1, x) w = w → w = 0) := by
  let _ := hs.1
  let σbar := TwoFactorModel.sectionRepresentation M σ
  have hcomp : σbar.comp M.projection = σ :=
    M.sectionRepresentation_comp σ
  have hirr : σbar.IsIrreducible := M.sectionRepresentation_irreducible σ
  have htriv : σbar.IsTrivial ↔ σ.IsTrivial :=
    M.sectionRepresentation_isTrivial_iff σ
  have hnbar : ¬ σbar.IsTrivial := by
    intro hσbar
    exact hn (htriv.mp hσbar)
  have hcore : pCore 2 (componentOrbit L B) ≤ σ.ker :=
    twoCore_le_ker σ
  obtain ⟨witness⟩ := SectionReduction.exists_splitSectionWitness h M σ hs hn
  have hInv : HasCubicInverters (Factor M.n) :=
    factor_hasCubicInverters M.n M.one_lt
  have hfirst : ∀ (x : Factor M.n), orderOf x = 3 →
      ∀ w, σbar (x, 1) w = w → w = 0 := by
    intro x hx w hw
    have hxpow : ((x, 1) : Factor M.n × Factor M.n) ^ 3 = 1 := by
      rw [Prod.pow_mk, ← hx, pow_orderOf_eq_one, one_pow]
      rfl
    have hfix : ∀ v,
        (witness.action.comp witness.split.embedding) (x, 1) v = v →
          ∀ g, (witness.action.comp witness.split.embedding) g v = v := by
      intro v hv g
      exact witness.split.cubic_fixed_all_of_first hInv hx v hv g
    exact cubic_fixed_free_irreducibleSection hxpow hfix
      witness.isSection hnbar w hw
  have hsecond : ∀ (x : Factor M.n), orderOf x = 3 →
      ∀ w, σbar (1, x) w = w → w = 0 := by
    intro x hx w hw
    have hxpow : ((1, x) : Factor M.n × Factor M.n) ^ 3 = 1 := by
      rw [Prod.pow_mk, one_pow, ← hx, pow_orderOf_eq_one]
      rfl
    have hfix : ∀ v,
        (witness.action.comp witness.split.embedding) (1, x) v = v →
          ∀ g, (witness.action.comp witness.split.embedding) g v = v := by
      intro v hv g
      exact witness.split.cubic_fixed_all_of_second hInv hx v hv g
    exact cubic_fixed_free_irreducibleSection hxpow hfix
      witness.isSection hnbar w hw
  exact ⟨σbar, hcomp, hirr, hnbar, hcore, hfirst, hsecond⟩

end Representation.QuadraticFourGroup

end
