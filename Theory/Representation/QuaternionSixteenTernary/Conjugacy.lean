module
public import Theory.Representation.QuaternionSixteenTernary.Cubic
public import Theory.Representation.QuaternionSixteenTernary.Form

/-!
# Aligning the four ternary cubic actions

Four explicit invertible coordinate changes carry the possible cubic actors to
one model. Each centralizes the marked reflection, normalizes the quaternion
subgroup and rescales its alternating form. The finite identities are checked
by kernel reduction; the actual-action consumer uses the prior cubic classifier.

Source: Aschbacher, *Sporadic Groups* (1994), 45.11, p.248.
-/

public section
namespace Theory.Representation.QuaternionSixteenTernary

@[expose] def cubicMatrix (i : Fin 4) : Mat := ![y0,y1,y2,y3] i

@[expose] def transportMatrix (i : Fin 4) : Mat :=
  ![((1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1)),
    ((0,0,1,0),(0,0,0,2),(2,0,0,0),(0,1,0,0)),
    ((2,0,0,0),(2,1,0,0),(0,0,2,0),(0,0,1,1)),
    ((0,0,1,1),(0,0,2,1),(0,2,0,0),(2,0,0,0))] i

@[expose] def inverseTransportMatrix (i : Fin 4) : Mat :=
  ![((1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1)),
    ((0,0,2,0),(0,0,0,1),(1,0,0,0),(0,2,0,0)),
    ((2,0,0,0),(2,1,0,0),(0,0,2,0),(0,0,1,1)),
    ((0,0,0,2),(0,0,2,0),(2,1,0,0),(2,2,0,0))] i

@[expose] def transportCode (i : Fin 4) (k : Fin 8) : Fin 8 :=
  ![![0,1,2,3,4,5,6,7],![0,1,2,3,5,4,7,6],![0,1,3,2,6,7,4,5],![0,1,3,2,7,6,5,4]] i k

@[expose] def transportMultiplier (i : Fin 4) : ZMod 3 := ![1,1,2,1] i

private theorem inverse_transport : ∀ (i : Fin 4) (v : V),
    lin (inverseTransportMatrix i) (lin (transportMatrix i) v)=v := by decide +kernel
private theorem transport_inverse : ∀ (i : Fin 4) (v : V),
    lin (transportMatrix i) (lin (inverseTransportMatrix i) v)=v := by decide +kernel

/-- The explicit coordinate change aligning the selected cubic with y₀. -/
def transport (i : Fin 4) : V ≃+ V where
  toFun := linHom (transportMatrix i)
  invFun := linHom (inverseTransportMatrix i)
  left_inv := by intro v; simpa only [linHom_apply] using inverse_transport i v
  right_inv := by intro v; simpa only [linHom_apply] using transport_inverse i v
  map_add' := map_add (linHom (transportMatrix i))

@[simp] theorem transport_apply (i : Fin 4) (v : V) :
    transport i v=lin (transportMatrix i) v := by
  change linHom (transportMatrix i) v=lin (transportMatrix i) v
  exact linHom_apply _ _

theorem transport_cubic : ∀ (i : Fin 4) (v : V),
    transport i (lin (cubicMatrix i) v)=lin y0 (transport i v) := by
  simp only [transport_apply]
  decide +kernel

theorem transport_reflection : ∀ (i : Fin 4) (v : V),
    transport i (r v)=r (transport i v) := by
  simp only [transport_apply]
  decide +kernel

theorem transport_quaternion : ∀ (i : Fin 4) (k : Fin 8) (v : V),
    transport i (q k v)=q (transportCode i k) (transport i v) := by
  simp only [transport_apply]
  decide +kernel

theorem transportCode_surjective : ∀ i : Fin 4, Function.Surjective (transportCode i) := by decide +kernel

theorem transport_form (i : Fin 4) (x y : V) :
    standardForm (transport i x) (transport i y)=transportMultiplier i*standardForm x y := by
  fin_cases i <;> simp [transport_apply,transportMatrix,transportMultiplier,standardForm,lin,show (2 : ZMod 3)= -1 from rfl] <;> ring_nf
  simp [show (2 : ZMod 3)= -1 from rfl]
  ring

theorem transportMultiplier_ne_zero : ∀ i : Fin 4, transportMultiplier i≠0 := by decide +kernel

/-- An actual cubic/reflection/quaternion action has a similitude carrying its
cubic to the common model, fixing the reflection and normalizing Q₈. -/
theorem exists_cubic_transport (f : V →+ V)
    (hc : ∀ v, f (f (f v))=v) (hr : ∀ v, r (f v)=f (f (r v)))
    (hne : ∃ v, f v≠v)
    (hn : ∀ k : Fin 8, ∃ j : Fin 8, ∀ v, f (q k v)=q j (f v)) :
    ∃ (E : V ≃+ V) (m : ZMod 3), m≠0 ∧
      (∀ v, E (f v)=lin y0 (E v)) ∧
      (∀ v, E (r v)=r (E v)) ∧
      (∀ k : Fin 8, ∃ j : Fin 8, ∀ v, E (q k v)=q j (E v)) ∧
      (∀ j : Fin 8, ∃ k : Fin 8, ∀ v, E (q k v)=q j (E v)) ∧
      (∀ x y, standardForm (E x) (E y)=m*standardForm x y) := by
  have cases := cubic_classification f hc hr hne hn
  have hex : ∃ i : Fin 4, f=linHom (cubicMatrix i) := by
    rcases cases with h | h | h | h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
    · exact ⟨3,h⟩
  obtain ⟨i,rfl⟩ := hex
  refine ⟨transport i,transportMultiplier i,transportMultiplier_ne_zero i,by simpa only [linHom_apply] using transport_cubic i,
    transport_reflection i,?_,?_,transport_form i⟩
  · exact fun k=>⟨transportCode i k,transport_quaternion i k⟩
  · intro j
    obtain ⟨k,hk⟩ := transportCode_surjective i j
    exact ⟨k,by simpa only [hk] using transport_quaternion i k⟩
end Theory.Representation.QuaternionSixteenTernary
