module
public import Theory.Representation.ScalarMultiplicity.Semilinear
public import Theory.Representation.SL2.NaturalIrrPlus

/-!
# Multiplicity coefficients of two natural SL₂ copies

The canonical semilinear natural action of Aut(SL₂) removes the component
action from each block. The scalar commutant then constructs a representation
on the two coefficient coordinates. Its faithful image retains a field action,
and every diagonal component operator has trivial coefficient image.

Source: Aschbacher--Smith D.3.21, printed pp.206--207.
-/

public noncomputable section
open scoped MatrixGroups
namespace Representation.SL2AutomorphismNatural
variable {F A : Type*} [Field F] [Finite F] [CharP F 2] [Group A]
local instance : Algebra (ZMod 2) F := ZMod.algebra _ 2

/-- The coefficient action, its descended field action, and its diagonal kernel
are constructed from the literal normalizer action on two natural copies. -/
theorem exists_two_copy_coefficients
    (ρ : Representation (ZMod 2) A (Fin 2 → (Fin 2 → F)))
    (α : A →* MulAut (SL(2,F)))
    (hcov : ∀ a g x, ρ a (fun i => g.val.mulVec (x i)) =
      fun i => (α a g).val.mulVec (ρ a x i)) :
    ∃ μ : Representation (ZMod 2) A (Fin 2 → F),
      (∀ a c v, ρ a (fun i => c i • v) =
        fun i => μ a c i • action (α a) v) ∧
      (∀ a (g : SL(2,F)), (∀ x, ρ a x = fun i => g.val.mulVec (x i)) → μ.asGroupHom a = 1) ∧
      ∃ τ : μ.asGroupHom.range →* (F ≃+* F),
        ∀ a c v, (a.val.val : Module.End (ZMod 2) (Fin 2 → F)) (c • v) =
          τ a c • (a.val.val : Module.End (ZMod 2) (Fin 2 → F)) v := by
  let β := Representation.SL2AutomorphismNatural.action.comp α
  let τ := Representation.SL2AutomorphismNatural.fieldAction.comp α
  let σ := Representation.SL2AutomorphismNatural.action.comp (MulAut.conj : SL(2,F) →* _)
  have hσ (g : SL(2,F)) (v : Fin 2 → F) : σ g v = g.val.mulVec v :=
    Representation.SL2AutomorphismNatural.action_conj g v
  have hs : ∀ f : (Fin 2 → F) →ₗ[ZMod 2] (Fin 2 → F),
      (∀ g v, f (σ g v) = σ g (f v)) → ∃ b : F, ∀ v, f v = b • v := by
    intro f hf
    exact Representation.SL2NaturalOffenders.centralizer_scalar f.toAddMonoidHom
      (by intro g v; change f (g.val.mulVec v) = g.val.mulVec (f v); simpa only [hσ] using hf g v)
  obtain ⟨μ,hμ,hsemi⟩ := Representation.ScalarMultiplicity.exists_semilinear_multiplicity
    σ hs ρ β (fun n g => α n g)
    (by simpa only [hσ] using hcov)
    (by intro n g v; simp only [hσ]; exact
      Representation.SL2AutomorphismNatural.action_intertwines (α n) g v)
    τ (fun n b v => Representation.SL2AutomorphismNatural.action_semilinear
      (α n) b v)
  let q := μ.asGroupHom.rangeRestrict
  obtain ⟨τ',hτ',hsemi'⟩ := Representation.ScalarMultiplicity.exists_fieldAction_on_image μ τ hsemi
  have hdiag (n : A) (g : SL(2,F))
      (hn : ∀ x, ρ n x = fun i => g.val.mulVec (x i)) : q n = 1 := by
    have ha : α n = MulAut.conj g :=
      Representation.SL2AutomorphismNatural.automorphism_eq_conj_of_diagonal
        _ g (by intro d x; simpa only [hn] using hcov n d x)
    have hb (v : Fin 2 → F) : β n v = g.val.mulVec v := by
      change Representation.SL2AutomorphismNatural.action (α n) v = _
      rw [ha,Representation.SL2AutomorphismNatural.action_conj]
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro v
    funext i
    change μ n v i = v i
    let z : Fin 2 → F := ![1,0]
    have hz : z ≠ 0 := by intro h; have hh := congrFun h 0; simp [z] at hh
    have hg : g.val.mulVec z ≠ 0 := by
      intro h
      apply hz
      exact (Matrix.SpecialLinearGroup.toLin' g).injective (h.trans (map_zero _).symm)
    apply smul_left_injective F hg
    have hh := congrFun (hμ n v z) i
    rw [hn,hb] at hh
    simpa only [Matrix.mulVec_smul] using hh.symm
  refine ⟨μ,hμ,?_,τ',hsemi'⟩
  intro n g hn
  exact congrArg Subtype.val (hdiag n g hn)
end Representation.SL2AutomorphismNatural
