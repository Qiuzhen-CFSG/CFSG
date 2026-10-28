module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowSieveModels
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic
public import Theory.Representation.SymplecticConjugatePair.Ambient.Transport
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic

/-!
# Automorphism types of the non-SL₃ constituent models

The natural A₆ module extends to the index-two symmetric automorphism
subgroup. Every A₇ representation is invariant under inner automorphisms,
and the full automorphism group has just two such cosets. Inner-field
intertwiners leave two types for natural symplectic four-space. For binary
SL₄ and SL₅, inner/graph coverage gives the same bound, transported through
the actual matrix-to-linear-group equivalence.

All conclusions are literal representation equivalences for one fixed model
actor. `SeedAlternativesMovedSylowTwoTypes` applies them to the original
chosen action and derives the two-conjugate Sylow orbit.

Source: Aschbacher--Smith D.3.5(4), combined manuscript of 1 March 2004,
printed pp.195--196, using the standard automorphism descriptions.
-/

public noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {P W : Type*} [Group P] [AddCommGroup W] [Module (ZMod 2) W]

private def innerTwistEquiv (τ : Representation (ZMod 2) P W) (g : P) :
    Representation.Equiv (τ.comp (MulAut.conj g).toMonoidHom) τ :=
  Representation.Equiv.mk (LinearEquiv.ofBijective (τ g⁻¹) (τ.apply_bijective g⁻¹)) (by
    intro x; apply LinearMap.ext; intro v
    change τ g⁻¹ (τ (g*x*g⁻¹) v) = τ x (τ g⁻¹ v)
    simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel_left])

/-- An index-two subgroup of model automorphisms preserving the module leaves at most two literal twists. -/
theorem two_twists_of_index_two {H : Type*} [Group H]
    (τ : Representation (ZMod 2) P W)
    (π : H →* MulAut P) (hπ : Function.Surjective π)
    (K : Subgroup H) (hK : K.index = 2)
    (hk : ∀ k ∈ K, Nonempty (Representation.Equiv (τ.comp (π k).toMonoidHom) τ)) :
    ∃ τ₁ : Representation (ZMod 2) P W, ∀ a : MulAut P,
      Nonempty (Representation.Equiv (τ.comp a.toMonoidHom) τ) ∨
      Nonempty (Representation.Equiv (τ.comp a.toMonoidHom) τ₁) := by
  obtain ⟨r,_,hr⟩ := index_eq_two_iff_exists_notMem_and.mp hK
  refine ⟨τ.comp (π r⁻¹).toMonoidHom,?_⟩
  intro a
  obtain ⟨s,rfl⟩ := hπ a
  rcases hr s with hs | hs
  · obtain ⟨e⟩ := hk (s*r) hs
    refine Or.inr ⟨Representation.Equiv.mk e.toLinearEquiv ?_⟩
    intro x; apply LinearMap.ext; intro v
    have he := IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap ((π r⁻¹) x) v
    change e (τ ((π (s*r)) ((π r⁻¹) x)) v) = τ ((π r⁻¹) x) (e v) at he
    have hx : (π (s*r)) ((π r⁻¹) x) = π s x := by
      change ((π (s*r)) * π r⁻¹) x = π s x
      rw [←map_mul,mul_inv_cancel_right]
    rw [hx] at he
    exact he
  · exact Or.inl (hk s hs)

/-- The natural A₆ module has at most two types under its full automorphism group. -/
theorem alternating_six_two_twists :
    let τ := (BinaryPermutation.naturalRepresentation (Fin 6)).comp
      (alternatingGroup (Fin 6)).subtype
    ∃ τ₁ : Representation (ZMod 2) (alternatingGroup (Fin 6))
        (BinaryPermutation.natural (Fin 6)),
      ∀ a : MulAut (alternatingGroup (Fin 6)),
        Nonempty (Representation.Equiv (τ.comp a.toMonoidHom) τ) ∨
        Nonempty (Representation.Equiv (τ.comp a.toMonoidHom) τ₁) := by
  let τ := BinaryPermutation.naturalRepresentation (Fin 6)
  apply two_twists_of_index_two (τ.comp (alternatingGroup (Fin 6)).subtype)
    (MonoidHom.id _) Function.surjective_id
    GLS3.Chapter5.naturalAlternatingAutomorphismSubgroup
    GLS3.Chapter5.naturalAlternatingAutomorphismSubgroup_index
  rintro _ ⟨p,rfl⟩
  refine ⟨Representation.Equiv.mk
    (LinearEquiv.ofBijective (τ p⁻¹) (τ.apply_bijective p⁻¹)) ?_⟩
  intro x; apply LinearMap.ext; intro v
  change τ p⁻¹ (τ (p*x.val*p⁻¹) v) = τ x.val (τ p⁻¹ v)
  simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel_left]

/-- Every fixed A₇ action has at most two automorphism twists; this applies to either four-dimensional constituent. -/
theorem alternating_seven_two_twists
    (τ : Representation (ZMod 2) (alternatingGroup (Fin 7)) W) :
    ∃ τ₁ : Representation (ZMod 2) (alternatingGroup (Fin 7)) W,
      ∀ a : MulAut (alternatingGroup (Fin 7)),
        Nonempty (Representation.Equiv (τ.comp a.toMonoidHom) τ) ∨
        Nonempty (Representation.Equiv (τ.comp a.toMonoidHom) τ₁) := by
  apply two_twists_of_index_two τ MulAut.conjNormal
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
      7 (by decide) (by decide)).surjective
    (alternatingGroup (Fin 7)) alternatingGroup.index_eq_two
  intro p hp
  have he : MulAut.conjNormal p = MulAut.conj (⟨p,hp⟩ : alternatingGroup (Fin 7)) :=
    MulAut.conjNormal_val (h := (⟨p,hp⟩ : alternatingGroup (Fin 7)))
  rw [he]
  exact ⟨innerTwistEquiv τ _⟩

/-- Natural symplectic four-space has only its original and graph-twisted binary types. -/
theorem symplectic_four_two_twists {F : Type*} [Field F] [Finite F]
    [CharP F 2] [Algebra (ZMod 2) F] :
    let τ := Representation.restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)
    ∃ τ₁ : Representation (ZMod 2) (Theory.SpecificGroups.SymplecticFour.Sp F)
        (Theory.SpecificGroups.SymplecticFour.Vector F),
      ∀ a : MulAut (Theory.SpecificGroups.SymplecticFour.Sp F),
        Nonempty (Representation.Equiv (τ.comp a.toMonoidHom) τ) ∨
        Nonempty (Representation.Equiv (τ.comp a.toMonoidHom) τ₁) := by
  let τ := Representation.restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)
  let γ := Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph.graphAut (F := F)
  refine ⟨τ.comp γ.toMonoidHom,?_⟩
  intro a
  by_cases ha : Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.PreservesDiagram a
  · obtain ⟨g,σ,rfl⟩ :=
      Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram a ha
    refine Or.inl ⟨(Representation.Equiv.mk
      (SymplecticConjugatePair.Ambient.innerFieldVector g σ) ?_).symm⟩
    intro x; apply LinearMap.ext; intro v
    exact SymplecticConjugatePair.Ambient.innerFieldVector_intertwines g σ x v
  · obtain ⟨g,σ,rfl⟩ := SymplecticConjugatePair.Ambient.moving_eq_inner_field_graph a ha
    refine Or.inr ⟨(Representation.Equiv.mk
      (SymplecticConjugatePair.Ambient.innerFieldVector g σ) ?_).symm⟩
    intro x; apply LinearMap.ext; intro v
    exact SymplecticConjugatePair.Ambient.innerFieldVector_intertwines g σ (γ x) v

/-- Inner/graph coverage bounds the twists of any fixed representation by two. -/
theorem two_twists_of_inner_graph (τ : Representation (ZMod 2) P W)
    (γ : MulAut P)
    (hcover : ∀ a : MulAut P, ∃ g : P, a = MulAut.conj g ∨ a = γ * MulAut.conj g) :
    ∃ τ₁ : Representation (ZMod 2) P W, ∀ a : MulAut P,
      Nonempty (Representation.Equiv (τ.comp a.toMonoidHom) τ) ∨
      Nonempty (Representation.Equiv (τ.comp a.toMonoidHom) τ₁) := by
  refine ⟨τ.comp γ.toMonoidHom,?_⟩
  intro a
  obtain ⟨g,hg | hg⟩ := hcover a
  · subst a; exact Or.inl ⟨innerTwistEquiv τ g⟩
  · subst a; exact Or.inr ⟨innerTwistEquiv (τ.comp γ.toMonoidHom) g⟩

/-- A group equivalence transports the two-type bound without changing the original action. -/
theorem two_twists_transport {Q : Type*} [Group Q]
    (e : P ≃* Q) (τ : Representation (ZMod 2) P W)
    (h : ∃ τ₁ : Representation (ZMod 2) Q W, ∀ a : MulAut Q,
      Nonempty (Representation.Equiv ((τ.comp e.symm.toMonoidHom).comp a.toMonoidHom)
        (τ.comp e.symm.toMonoidHom)) ∨
      Nonempty (Representation.Equiv ((τ.comp e.symm.toMonoidHom).comp a.toMonoidHom) τ₁)) :
    ∃ τ₁ : Representation (ZMod 2) P W, ∀ a : MulAut P,
      Nonempty (Representation.Equiv (τ.comp a.toMonoidHom) τ) ∨
      Nonempty (Representation.Equiv (τ.comp a.toMonoidHom) τ₁) := by
  obtain ⟨τ₁,h⟩ := h
  refine ⟨τ₁.comp e.toMonoidHom,fun a => ?_⟩
  rcases h (MulAut.congr e a) with h | h
  · obtain ⟨d⟩ := h
    refine Or.inl ⟨Representation.Equiv.mk d.toLinearEquiv ?_⟩
    intro x; apply LinearMap.ext; intro v
    have he := IntertwiningMap.isIntertwining _ _ d.toIntertwiningMap (e x) v
    change d (τ (e.symm (e (a (e.symm (e x))))) v) = τ (e.symm (e x)) (d v) at he
    change d (τ (a x) v) = τ x (d v)
    simpa only [e.symm_apply_apply] using he
  · obtain ⟨d⟩ := h
    refine Or.inr ⟨Representation.Equiv.mk d.toLinearEquiv ?_⟩
    intro x; apply LinearMap.ext; intro v
    have he := IntertwiningMap.isIntertwining _ _ d.toIntertwiningMap (e x) v
    change d (τ (e.symm (e (a (e.symm (e x))))) v) = τ₁ (e x) (d v) at he
    change d (τ (a x) v) = τ₁ (e x) (d v)
    simpa only [e.symm_apply_apply] using he

/-- The actual binary SL₄ and SL₅ carriers have at most two twists of any fixed representation. -/
theorem binary_linear_two_twists {n : ℕ} (hn : n = 4 ∨ n = 5)
    (τ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) W) :
    ∃ τ₁ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) W,
      ∀ a : MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)),
        Nonempty (Representation.Equiv (τ.comp a.toMonoidHom) τ) ∨
        Nonempty (Representation.Equiv (τ.comp a.toMonoidHom) τ₁) :=
  two_twists_transport (BinaryLinear.OuterCyclic.slEquivLinear n) τ
    (two_twists_of_inner_graph _ (BinaryLinear.OuterCyclic.graphLinear n)
      (BinaryLinear.OuterCyclic.inner_graph hn))

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
