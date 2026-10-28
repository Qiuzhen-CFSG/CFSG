module
public import Theory.Representation.NormalPairSupport

/-!
# Exact exchange coordinates between the two canonical supports

An actual ambient factor exchange restricts to a linear equivalence of the
factor-fixed support spaces. No involution condition is required on the actor;
its arbitrary twists on both factors are retained. This is the source exchange
used to identify the multiplicities in the separated A₅ full module.
-/

public noncomputable section
namespace Representation.NormalPairSupport
variable {k S Q V : Type*} [Field k] [Group S] [Group Q]
  [AddCommGroup V] [Module k V]
  (ρ : Representation k Q V) (i : S × S →* Q)
  (g : Q) (α β : MulAut S)
  (h : ∀ x y, g * i (x,y) * g⁻¹ = i (α y,β x))

include h

private theorem exchange_covariance (s : S) (v : V) :
    ρ g (ρ (i (1,s)) v) = ρ (i (α s,1)) (ρ g v) := by
  have he := h 1 s
  rw [map_one] at he
  rw [←he]
  simp only [←Module.End.mul_apply, ←map_mul, mul_assoc, inv_mul_cancel, mul_one]

private theorem exchange_maps_left {v : V} (hv : v ∈ left ρ i) :
    ρ g v ∈ right ρ i := by
  intro s
  obtain ⟨s,rfl⟩ := α.surjective s
  change ρ (i (α s,1)) (ρ g v) = ρ g v
  rw [←exchange_covariance ρ i g α β h]
  exact congrArg (ρ g) (hv s)

/-- Restrict the actual exchanging operator to its canonical support spaces. -/
def exchangeEquiv : left ρ i ≃ₗ[k] right ρ i := by
  let f : left ρ i →ₗ[k] right ρ i :=
    ((ρ g).comp (left ρ i).subtype).codRestrict (right ρ i)
      (fun v => exchange_maps_left ρ i g α β h v.property)
  apply LinearEquiv.ofBijective f
  constructor
  · intro v w he
    apply Subtype.ext
    exact (ρ.apply_bijective g).injective (congrArg Subtype.val he)
  · intro w
    obtain ⟨v,hv⟩ := (ρ.apply_bijective g).surjective w.val
    have hvl : v ∈ left ρ i := by
      intro s
      apply (ρ.apply_bijective g).injective
      change ρ g (ρ (i (1,s)) v) = ρ g v
      rw [exchange_covariance ρ i g α β h,hv]
      exact w.property (α s)
    exact ⟨⟨v,hvl⟩,Subtype.ext hv⟩

/-- The exchange equivalence is the original ambient action on every vector. -/
theorem exchangeEquiv_apply (v : left ρ i) :
    (exchangeEquiv ρ i g α β h v : V) = ρ g v := by
  unfold exchangeEquiv
  rfl

/-- A separated nonzero support is nonzero in both orientations. -/
theorem left_ne_bot_of_exchange
    (hsep : left ρ i ≠ ⊥ ∨ right ρ i ≠ ⊥) : left ρ i ≠ ⊥ := by
  rcases hsep with hleft | hright
  · exact hleft
  intro hleft
  apply hright
  apply bot_unique
  intro w hw
  obtain ⟨v,hv⟩ := (exchangeEquiv ρ i g α β h).surjective ⟨w,hw⟩
  have hz : v.val = 0 := by
    have hv0 : v.val ∈ (⊥ : Submodule k V) := hleft ▸ v.property
    exact hv0
  have hv0 : v = 0 := Subtype.ext hz
  rw [hv0,map_zero] at hv
  exact congrArg Subtype.val hv.symm
omit h in
/-- In finite dimension, every ambient operator permutes the actual supports
by equality, even before their multiplicities have been computed. -/
theorem support_map_eq_or_exchanged [Finite S] [Theory.GroupTheory.IsQuasisimple S]
    [FiniteDimensional k V] (hi : Function.Injective i) [i.range.Normal]
    (hZ : Subgroup.center S = ⊥) (a : Q) :
    ((left ρ i).map (ρ a) = left ρ i ∧ (right ρ i).map (ρ a) = right ρ i) ∨
      ((left ρ i).map (ρ a) = right ρ i ∧ (right ρ i).map (ρ a) = left ρ i) := by
  have hd (U : Submodule k V) : Module.finrank k (U.map (ρ a)) = Module.finrank k U :=
    (Submodule.equivMapOfInjective (ρ a) (ρ.apply_bijective a).injective U).finrank_eq.symm
  rcases support_stable_or_exchanged ρ i hi hZ a with h | h
  · exact Or.inl ⟨Submodule.eq_of_le_of_finrank_eq h.1 (hd _),
      Submodule.eq_of_le_of_finrank_eq h.2 (hd _)⟩
  · have hl : Module.finrank k (left ρ i) ≤ Module.finrank k (right ρ i) := by
      rw [←hd (left ρ i)]
      exact Submodule.finrank_mono h.1
    have hr : Module.finrank k (right ρ i) ≤ Module.finrank k (left ρ i) := by
      rw [←hd (right ρ i)]
      exact Submodule.finrank_mono h.2
    have he := Nat.le_antisymm hl hr
    exact Or.inr ⟨Submodule.eq_of_le_of_finrank_eq h.1 ((hd _).trans he),
      Submodule.eq_of_le_of_finrank_eq h.2 ((hd _).trans he.symm)⟩
end Representation.NormalPairSupport
