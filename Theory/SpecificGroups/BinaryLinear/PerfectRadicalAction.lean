module

public import Theory.SpecificGroups.BinaryLinear.PerfectRadicalMarking

/-!
# The actual natural-or-dual action of a perfect binary-five cover

The geometric marking is compared with the prescribed original quotient
marking. Inner automorphisms preserve each module, and the graph coset
exchanges them. Consequently the literal radical is doubled natural or
doubled dual for that same original actor, without choosing an orientation.
-/

public noncomputable section
open Subgroup Representation
namespace BinaryLinear
open SmallParabolicLevi OuterCyclic BinaryLinearThree BinaryLinearThree.AutomorphismAction

private def doubleEquiv {X Y : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    {ρ : Representation (ZMod 2) BinaryLinearThree.Group X}
    {σ : Representation (ZMod 2) BinaryLinearThree.Group Y}
    (α : MulAut BinaryLinearThree.Group) (e : Representation.Equiv (ρ.comp α.toMonoidHom) σ) :
    Representation.Equiv ((ρ.prod ρ).comp α.toMonoidHom) (σ.prod σ) where
  toLinearEquiv := e.toLinearEquiv.prodCongr e.toLinearEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · exact LinearMap.congr_fun (e.isIntertwining' g) x.1
    · exact LinearMap.congr_fun (e.isIntertwining' g) x.2

private theorem natural_twist_dichotomy (α : MulAut BinaryLinearThree.Group) :
    Nonempty (Representation.Equiv ((W.prod W).comp α.toMonoidHom) (W.prod W)) ∨
      Nonempty (Representation.Equiv ((W.prod W).comp α.toMonoidHom) (W.dual.prod W.dual)) := by
  by_cases hi : α ∈ MulAut.innerSubgroup BinaryLinearThree.Group
  · obtain ⟨e⟩ := (natural_stabilizer α).mpr hi
    exact Or.inl ⟨doubleEquiv α e⟩
  · exact Or.inr ⟨doubleEquiv α (naturalOuterEquiv α hi)⟩

private theorem dual_twist_dichotomy (α : MulAut BinaryLinearThree.Group) :
    Nonempty (Representation.Equiv ((W.dual.prod W.dual).comp α.toMonoidHom) (W.prod W)) ∨
      Nonempty (Representation.Equiv ((W.dual.prod W.dual).comp α.toMonoidHom) (W.dual.prod W.dual)) := by
  by_cases hi : α ∈ MulAut.innerSubgroup BinaryLinearThree.Group
  · obtain ⟨e⟩ := (dual_stabilizer α).mpr hi
    exact Or.inr ⟨doubleEquiv α e⟩
  · exact Or.inl ⟨doubleEquiv α (dualOuterEquiv α hi)⟩

private theorem transport {E V X Y : Type*} [Group E]
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    (π : E →* BinaryLinearThree.Group) (U : Submodule (ZMod 2) V)
    (f : E →* parabolic U) (α : MulAut BinaryLinearThree.Group)
    (ρ : Representation (ZMod 2) BinaryLinearThree.Group X)
    (σ : Representation (ZMod 2) BinaryLinearThree.Group Y)
    (e : radical U ≃* Multiplicative X)
    (he : ∀ (g : E) (x y : radical U), y.val=(f g).val*x.val*(f g).val⁻¹ →
      (e y).toAdd=ρ (α (π g)) (e x).toAdd)
    (a : Representation.Equiv (ρ.comp α.toMonoidHom) σ) :
    ∃ e : radical U ≃* Multiplicative Y,
      ∀ (g : E) (x y : radical U), y.val=(f g).val*x.val*(f g).val⁻¹ →
        (e y).toAdd=σ (π g) (e x).toAdd := by
  refine ⟨e.trans a.toLinearEquiv.toAddEquiv.toMultiplicative,?_⟩
  intro g x y hy
  change a.toLinearEquiv (e y).toAdd=σ (π g) (a.toLinearEquiv (e x).toAdd)
  rw [he g x y hy]
  exact LinearMap.congr_fun (a.isIntertwining' (π g)) (e x).toAdd

/-- Under one specified original SL3 quotient marking, every nontrivial
perfect actor in a binary 2+3 or 3+2 parabolic acts on its literal radical
as two natural copies or two dual copies. Both geometric orientations and
the graph automorphism are allowed. -/
theorem perfect_radical_original_actor_dichotomy
    {E V : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (π : E →* BinaryLinearThree.Group) (hπ : Function.Surjective π)
    (hk : IsPGroup 2 π.ker) (U : Submodule (ZMod 2) V)
    (f : E →* parabolic U) (hf : f≠1)
    (hdim : (Module.finrank (ZMod 2) U=2 ∧ Module.finrank (ZMod 2) (V ⧸ U)=3) ∨
      (Module.finrank (ZMod 2) U=3 ∧ Module.finrank (ZMod 2) (V ⧸ U)=2)) :
    (∃ e : radical U ≃* Multiplicative (Vector × Vector),
      ∀ (g : E) (x y : radical U), y.val=(f g).val*x.val*(f g).val⁻¹ →
        (e y).toAdd=(W.prod W) (π g) (e x).toAdd) ∨
    (∃ e : radical U ≃* Multiplicative
        (Module.Dual (ZMod 2) Vector × Module.Dual (ZMod 2) Vector),
      ∀ (g : E) (x y : radical U), y.val=(f g).val*x.val*(f g).val⁻¹ →
        (e y).toAdd=(W.dual.prod W.dual) (π g) (e x).toAdd) := by
  rcases hdim with ⟨hU,hV⟩ | ⟨hU,hV⟩
  · let a : U ≃ₗ[ZMod 2] Space 2 := LinearEquiv.ofFinrankEq _ _ (by simpa using hU)
    let b : (V ⧸ U) ≃ₗ[ZMod 2] Space 3 := LinearEquiv.ofFinrankEq _ _ (by simpa using hV)
    obtain ⟨α,e,he⟩ := perfect_radical_dual_marked π hπ hk U f hf a b
    rcases dual_twist_dichotomy α with ha | ha
    · obtain ⟨ea⟩ := ha
      exact Or.inl (transport π U f α _ _ e he ea)
    · obtain ⟨ea⟩ := ha
      exact Or.inr (transport π U f α _ _ e he ea)
  · let a : U ≃ₗ[ZMod 2] Space 3 := LinearEquiv.ofFinrankEq _ _ (by simpa using hU)
    let b : (V ⧸ U) ≃ₗ[ZMod 2] Space 2 := LinearEquiv.ofFinrankEq _ _ (by simpa using hV)
    obtain ⟨α,e,he⟩ := perfect_radical_natural_marked π hπ hk U f hf a b
    rcases natural_twist_dichotomy α with ha | ha
    · obtain ⟨ea⟩ := ha
      exact Or.inl (transport π U f α _ _ e he ea)
    · obtain ⟨ea⟩ := ha
      exact Or.inr (transport π U f α _ _ e he ea)

end BinaryLinear
