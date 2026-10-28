module
public import Theory.Representation.IrreduciblePairNormalizer

/-!
# Odd-order operators preserve the original two simple axes

An actual normalizing operator permutes the two inequivalent irreducible
summands. An exchanging operator has every odd power exchanging them,
so no odd power can be the identity. The conclusion keeps the literal
operator and its same-actor intertwining equation, over any field.
Source application: Aschbacher--Smith H.4.1, printed pp.383--385.
-/

public noncomputable section
namespace Representation
variable {k H U W : Type*} [Field k] [Group H]
  [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
  (ρ : Representation k H U) (σ : Representation k H W)
  [IsIrreducible ρ] [IsIrreducible σ]

/-- A normalizing operator annihilated by an odd power preserves both original
inequivalent irreducible axes. No semilinear or outer-action classification
is assumed. -/
theorem irreducible_pair_odd_power_preserves_axes
    (hne : ¬ Nonempty (ρ.Equiv σ)) (α : MulAut H)
    (f : (U × W) ≃ₗ[k] (U × W))
    (hf : ∀ h v, f ((ρ.prod σ) h v) = (ρ.prod σ) (α h) (f v))
    {n : ℕ} (hn : Odd n) (hpow : f^n=1) :
    (∀ u, (f (u,0)).2=0) ∧ (∀ w, (f (0,w)).1=0) := by
  rcases irreducible_pair_normalizer_axes ρ σ hne α f hf with hp | hx
  · exact hp
  · have hfirst (u : U) : f (u,0)=(0,(f (u,0)).2) := Prod.ext (hx.1 u) rfl
    have htwo (u : U) : ((f^2) (u,0)).2=0 := by
      rw [pow_two,LinearEquiv.mul_apply,hfirst]
      exact hx.2 _
    have heven (j : ℕ) (u : U) : (((f^2)^j) (u,0)).2=0 := by
      induction j generalizing u with
      | zero => rfl
      | succ j ih =>
        rw [pow_succ,LinearEquiv.mul_apply]
        have he : (f^2) (u,0)=(((f^2) (u,0)).1,0) := Prod.ext rfl (htwo u)
        rw [he]
        exact ih _
    obtain ⟨j,hj⟩ := hn
    let : Nontrivial U := Subrepresentation.irreducible_module_nontrivial ρ
    obtain ⟨u,hu⟩ := exists_ne (0 : U)
    have he : ((f^2)^j) (u,0)=((((f^2)^j) (u,0)).1,0) := Prod.ext rfl (heven j u)
    have hz : ((f^(2*j+1)) (u,0)).1=0 := by
      rw [pow_succ',pow_mul,LinearEquiv.mul_apply,he]
      exact hx.1 _
    rw [←hj,hpow] at hz
    exact (hu hz).elim

/-- In particular every odd-order normalizing operator preserves the axes. -/
theorem irreducible_pair_odd_order_preserves_axes
    (hne : ¬ Nonempty (ρ.Equiv σ)) (α : MulAut H)
    (f : (U × W) ≃ₗ[k] (U × W))
    (hf : ∀ h v, f ((ρ.prod σ) h v) = (ρ.prod σ) (α h) (f v))
    (ho : Odd (orderOf f)) :
    (∀ u, (f (u,0)).2=0) ∧ (∀ w, (f (0,w)).1=0) :=
  irreducible_pair_odd_power_preserves_axes ρ σ hne α f hf ho (pow_orderOf_eq_one f)

/-- A literal representation preserving both coordinate axes is a product of
representations of the same original group. Restricting any marked actor or
normalizing intertwining equation therefore gives the two actual block actions. -/
theorem pair_preserving_block_representations
    {X : Type*} [Group X] (π : Representation k X (U × W))
    (hpres : ∀ x, (∀ u, (π x (u,0)).2=0) ∧
      (∀ w, (π x (0,w)).1=0)) :
    ∃ β : Representation k X U, ∃ γ : Representation k X W, π=β.prod γ := by
  have he (x : X) (v : U × W) :
      π x v=((π x (v.1,0)).1,(π x (0,v.2)).2) := by
    have hv : v=(v.1,0)+(0,v.2) := by simp
    calc
      π x v=π x (v.1,0)+π x (0,v.2) := by rw [←map_add,←hv]
      _=_ := Prod.ext (by simpa using (hpres x).2 v.2)
        (by simpa using (hpres x).1 v.1)
  let β : Representation k X U := {
    toFun x := (LinearMap.fst _ _ _).comp ((π x).comp (LinearMap.inl _ _ _))
    map_one' := by
      apply LinearMap.ext
      intro u
      change (π 1 (u,0)).1=u
      rw [map_one]; rfl
    map_mul' x y := by
      apply LinearMap.ext
      intro u
      change (π (x*y) (u,0)).1=(π x ((π y (u,0)).1,0)).1
      rw [map_mul,Module.End.mul_apply]
      simpa only using congrArg (fun v : U × W => v.1) (he x (π y (u,0))) }
  let γ : Representation k X W := {
    toFun x := (LinearMap.snd _ _ _).comp ((π x).comp (LinearMap.inr _ _ _))
    map_one' := by
      apply LinearMap.ext
      intro w
      change (π 1 (0,w)).2=w
      rw [map_one]; rfl
    map_mul' x y := by
      apply LinearMap.ext
      intro w
      change (π (x*y) (0,w)).2=(π x (0,(π y (0,w)).2)).2
      rw [map_mul,Module.End.mul_apply]
      simpa only using congrArg (fun v : U × W => v.2) (he x (π y (0,w))) }
  refine ⟨β,γ,?_⟩
  apply MonoidHom.ext
  intro x
  apply LinearMap.ext
  intro v
  exact he x v

end Representation
