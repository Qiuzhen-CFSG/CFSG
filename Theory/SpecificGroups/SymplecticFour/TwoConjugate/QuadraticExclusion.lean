module
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.MovingPair
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Quadratic-form exclusion for a moving central-root subgroup

A central-root element preserving a quadratic form with the standard
symplectic polar form satisfies two equations obtained on the opposite
coordinate vectors. A nontrivial moving-actor stable subgroup cannot lie
on a root axis, so these equations place its parameters on a quadratic
curve s = beta t^2. The actor sends this curve to a fourth-power relation;
nonzero parameters are unique, forcing the subgroup to have order at most
two. Thus a subgroup of order greater than two, and its literal opposition
pair, preserve no such quadratic form.

This proves the orthogonal-case exclusion used in Aschbacher--Smith E.2.7,
printed pp.219--220, once the transvection recognition theorem supplies an
invariant quadratic form. No root element in the original subgroup is
assumed, and the quadratic form and polar form are the actual library objects.
-/

public section
noncomputable section
open Subgroup Theory.SpecificGroups.SymplecticFour
open DiagramAutomorphisms EvenBorelTorus CentralRootGeometry
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.TwoConjugate
variable {F : Type*} [Field F] [CharP F 2]
local notation "i₁" => (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "i₂" => (Sum.inl (1 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "j₁" => (Sum.inr (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "j₂" => (Sum.inr (1 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "e₁" => (Pi.single i₁ (1:F) : Vector F)
local notation "e₂" => (Pi.single i₂ (1:F) : Vector F)
local notation "f₁" => (Pi.single j₁ (1:F) : Vector F)
local notation "f₂" => (Pi.single j₂ (1:F) : Vector F)

private theorem central_coordinates {V : Subgroup (Sp F)}
    (hc : V ≤ (parameter (F:=F)).range) {g : Sp F} (hg : g∈V) :
    ∃s t:F,upper s t=g := by
  obtain ⟨x,hx⟩ := hc hg
  exact ⟨x.1.toAdd,x.2.toAdd,by simpa only [parameter_apply,upper] using hx⟩

/-- A central-root element preserving a quadratic form with the standard polar
form satisfies two explicit parameter equations. -/
theorem upper_quadratic_constraints (Q : QuadraticForm F (Vector F))
    (hQ : Q.polarBilin = form F) (s t : F)
    (hpres : ∀x : Vector F,Q (upper s t • x)=Q x) :
    Q e₁*t^2=0 ∧ s+Q e₁*s^2+Q e₂*t^2=0 := by
  have hadd (x y : Vector F) : Q (x+y)=Q x+Q y+form F x y := by
    rw [QuadraticMap.map_add Q,←QuadraticMap.polarBilin_apply_apply,hQ]
  have hv₂ : upper s t • f₂ = f₂+t•e₁ := by
    rw [upper_apply]
    ext i
    rcases i with i | i <;> fin_cases i <;> simp
  have hv₁ : upper s t • f₁ = f₁+(s•e₁+t•e₂) := by
    rw [upper_apply]
    ext i
    rcases i with i | i <;> fin_cases i <;> simp
  have h₂ := hpres f₂
  have h₁ := hpres f₁
  rw [hv₂,hadd] at h₂
  rw [hv₁,hadd,hadd] at h₁
  simp [QuadraticMap.map_smul,form_apply,Pi.single_apply,
    CharTwo.neg_eq] at h₁ h₂
  constructor
  · rcases h₂ with ht | hA <;> simp [*]
  · linear_combination h₁


/-- An actor-stable subgroup on a quadratic parameter curve has at most two
members. Squaring is injective in characteristic two. -/
theorem quadratic_curve_card_le_two (a : MulAut (Sp F))
    (σ : F ≃+* F) (c d : F) (hc : c≠0)
    (hcoord : ∀s t:F,a (upper s t)=upper (c*(σ t)^2) (d*σ s))
    (V : Subgroup (Sp F)) (hV : V.map a.toMonoidHom=V)
    (hcent : V≤(parameter (F:=F)).range) (β : F)
    (hcurve : ∀s t:F,upper s t∈V → s=β*t^2) : Nat.card V≤2 := by
  classical
  let C : F := β*d^2*(σ β)^2
  have rel (t:F) (ht:upper (β*t^2) t∈V) (ht0:t≠0) : c=C*(σ t)^2 := by
    have hm : a (upper (β*t^2) t)∈V := hV.le (mem_map_of_mem a.toMonoidHom ht)
    rw [hcoord] at hm
    have hh := hcurve _ _ hm
    simp only [map_mul,map_pow] at hh
    apply (mul_left_inj' (pow_ne_zero 2 ((map_ne_zero σ).mpr ht0))).mp
    dsimp [C]
    linear_combination hh
  have unique (t u:F) (ht:upper (β*t^2) t∈V) (hu:upper (β*u^2) u∈V)
      (ht0:t≠0) (hu0:u≠0) : t=u := by
    have ht' := rel t ht ht0
    have hu' := rel u hu hu0
    have hC : C≠0 := by intro h; apply hc; simpa [h] using ht'
    exact σ.injective (CharTwo.sq_injective (mul_left_cancel₀ hC (ht'.symm.trans hu')))
  let f : V → Bool := fun x => decide (x=1)
  have hf : Function.Injective f := by
    intro x y he
    by_cases hx:x=1
    · have hy:y=1 := by simpa [f,hx] using he.symm
      exact hx.trans hy.symm
    · have hy:y≠1 := by simpa [f,hx] using he
      obtain ⟨s,t,hs⟩ := central_coordinates hcent x.property
      obtain ⟨u,v,hu⟩ := central_coordinates hcent y.property
      have hst := hcurve s t (hs.symm ▸ x.property)
      have huv := hcurve u v (hu.symm ▸ y.property)
      subst s u
      have ht0:t≠0 := by
        intro ht
        apply hx
        apply Subtype.ext
        rw [←hs,ht]
        simp [upper,RootSubgroup.element_zero]
      have hv0:v≠0 := by
        intro hv
        apply hy
        apply Subtype.ext
        rw [←hu,hv]
        simp [upper,RootSubgroup.element_zero]
      have heq := unique t v (hs.symm ▸ x.property) (hu.symm ▸ y.property) ht0 hv0
      apply Subtype.ext
      exact hs.symm.trans ((congrArg (fun z:F=>upper (β*z^2) z) heq).trans hu)
  simpa using Nat.card_le_card_of_injective f hf

variable [Finite F]

/-- A noncyclic central subgroup fixed setwise by a diagram-moving actor
preserves no quadratic form with the standard symplectic polar form. -/
theorem not_preserves_quadratic_of_moving_actor (hq : 2<Nat.card F)
    (a : ActorReduction.stabilizer (F:=F)) (ha : ¬PreservesDiagram a.val)
    (V : Subgroup (Sp F)) (hV : V.map a.val.toMonoidHom=V)
    (hcent : V≤(parameter (F:=F)).range) (hr : 2<Nat.card V)
    (Q : QuadraticForm F (Vector F)) (hQ : Q.polarBilin=form F) :
    ¬∀g∈V,∀x : Vector F,Q (g•x)=Q x := by
  intro hpres
  have hne : V≠⊥ := by intro he; subst V; simp at hr
  have hlong := (not_root_axes_of_moving_actor hq a ha V hV hne).1
  have hA : Q e₁=0 := by
    by_contra hA
    apply hlong
    intro g hg
    obtain ⟨s,t,hst⟩ := central_coordinates hcent hg
    have hh := upper_quadratic_constraints Q hQ s t
      (hpres _ (hst.symm ▸ hg))
    have ht : t=0 := by
      apply CharTwo.sq_injective
      simpa using (mul_eq_zero.mp hh.1).resolve_left hA
    apply (RootSubgroup.mem_group_iff 0 g).mpr
    exact ⟨s,by simpa [ht,upper,RootSubgroup.element_zero] using hst⟩
  have hcurve (s t:F) (hst:upper s t∈V) : s=Q e₂*t^2 := by
    have hh := (upper_quadratic_constraints Q hQ s t (hpres _ hst)).2
    apply sub_eq_zero.mp
    simpa [hA,sub_eq_add_neg,CharTwo.neg_eq] using hh
  obtain ⟨σ,c,d,hc,_,hcoord⟩ := moving_actor_coordinates hq a ha
  exact (not_le_of_gt hr) (quadratic_curve_card_le_two a.val σ c d hc hcoord V hV
    hcent (Q e₂) hcurve)

/-- The literal opposition pair of the moving-actor source is contained in
no orthogonal group with the standard symplectic polar form. -/
theorem oppositePair_not_preserves_quadratic_of_moving_actor (hq : 2<Nat.card F)
    (a : ActorReduction.stabilizer (F:=F)) (ha : ¬PreservesDiagram a.val)
    (V : Subgroup (Sp F)) (hV : V.map a.val.toMonoidHom=V)
    (hcent : V≤(parameter (F:=F)).range) (hr : 2<Nat.card V)
    (Q : QuadraticForm F (Vector F)) (hQ : Q.polarBilin=form F) :
    ¬∀g∈oppositePair V,∀x : Vector F,Q (g•x)=Q x := by
  intro hpres
  apply not_preserves_quadratic_of_moving_actor hq a ha V hV hcent hr Q hQ
  exact fun g hg => hpres g ((show V≤oppositePair V from le_sup_left) hg)

end Theory.SpecificGroups.SymplecticFour.TwoConjugate
