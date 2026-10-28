module
public import Theory.Representation.SL2CentralExtensionFixedSpace

/-!
# Commutators of the upper-Sylow fixed space

Adjoining a pointwise fixed subspace leaves the span of displacements
unchanged. Applied to the natural central extension and its marked complement,
this gives both equalities in Aschbacher–Smith, Lemma 14.7.65, printed p.1070
(combined manuscript of 1 March 2004). The complement's own commutator generation
is the earlier natural L₁-action input; generation of the full fixed space is
proved here.
-/

@[expose] public section
namespace Representation.SL2CentralExtension
open Matrix Matrix.SpecialLinearGroup
variable {F W : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]
  [AddCommGroup W] [Module (ZMod 2) W]

omit [CharP F 2] [Algebra (ZMod 2) F] in
/-- Adding a pointwise fixed subspace does not change a moved space. -/
theorem movedSpace_sup_fixed
    (ρ : Representation (ZMod 2) (SpecialLinearGroup (Fin 2) F) W)
    (B : Subgroup (SpecialLinearGroup (Fin 2) F))
    (V C : Submodule (ZMod 2) W) (hC : ∀ c ∈ C, ∀ b : B, ρ b.val c = c) :
    movedSpace ρ B (V ⊔ C) = movedSpace ρ B V := by
  apply le_antisymm
  · apply iSup_le
    intro b
    rintro _ ⟨w, rfl⟩
    obtain ⟨v, hv, c, hc, he⟩ := Submodule.mem_sup.mp w.property
    have hw : ρ b.val w - w = ρ b.val v - v := by
      rw [← he, map_add, hC c hc b]
      abel
    change ρ b.val w - w ∈ movedSpace ρ B V
    rw [hw]
    apply Submodule.mem_iSup_of_mem b
    exact ⟨⟨v, hv⟩, rfl⟩
  · apply iSup_le
    intro b
    rintro _ ⟨v, rfl⟩
    apply Submodule.mem_iSup_of_mem b
    exact ⟨⟨v, (le_sup_left : V ≤ V ⊔ C) v.property⟩, rfl⟩

/-- The two equalities in the upper-Sylow fixed-space calculation. -/
theorem upperFixed_and_movedSpace [FiniteDimensional (ZMod 2) F]
    (ρ : Representation (ZMod 2) (SpecialLinearGroup (Fin 2) F) W)
    (p : W →ₗ[ZMod 2] (Fin 2 → F)) (hp : Function.Surjective p)
    (he : ∀ g w, p (ρ g w) = g • p w)
    (hk : ∀ w, p w = 0 → ∀ g, ρ g w = w)
    (B : Subgroup (SpecialLinearGroup (Fin 2) F)) (V : Submodule (ZMod 2) W)
    (hfix : V ≤ upperFixed ρ)
    (hdim : Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) F)
    (hdisj : Disjoint V p.ker) (hgen : movedSpace ρ B V = V) :
    upperFixed ρ = V ⊔ p.ker ∧ movedSpace ρ B (upperFixed ρ) = V := by
  have h := upperFixed_decomposition ρ p hp he hk V hfix hdim hdisj
  refine ⟨h, ?_⟩
  rw [h, movedSpace_sup_fixed ρ B V p.ker (fun c hc b => hk c hc b), hgen]

end Representation.SL2CentralExtension
