module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearLocalKernel

/-!
# Diagram-preserving rigidity and the actual local actions

Semilinear classification eliminates the field contribution over the binary
field, giving innerness and collapse of every faithful normal extension with
diagram-preserving conjugation. In the nonbinary case it gives explicit
inner-field formulas on the two local SL₂ quotients. The linear conjugating
matrix lies in the corresponding actual parabolic. A two-element acting
trivially on either quotient is conjugation by an element of that local factor.

Source: Aschbacher--Smith F.1.12, printed pp.263--264 of `refs/quasithin.pdf`.
-/

public noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Binary automorphisms preserving both actual parabolic classes are inner. -/
theorem inner_of_preservesDiagram_of_card_two (hF : Nat.card F = 2)
    (a : MulAut (Sp F)) (ha : PreservesDiagram a) :
    ∃ g : Sp F, a = MulAut.conj g := by
  obtain ⟨g, σ, rfl⟩ := SemilinearClassification.inner_field_of_preservesDiagram a ha
  exact ⟨g, by rw [fieldAutomorphism_eq_one_of_card_two hF σ, mul_one]⟩

/-- A faithful normal binary overgroup preserving the diagram has no proper extension. -/
theorem extension_eq_top_of_card_two (hF : Nat.card F = 2)
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (e : Sp F ≃* N)
    (hC : Subgroup.centralizer (N : Set G) = ⊥)
    (hdiagram : ∀ g : G, PreservesDiagram (extensionAction N e g)) : N = ⊤ :=
  extension_eq_top_of_inner N e hC
    (fun g => inner_of_preservesDiagram_of_card_two hF _ (hdiagram g))

variable {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)

/-- The point-local quotient action is inner-field, with its actual parabolic representative. -/
theorem pointSL2Action_inner_field (a : MulAut (Sp F)) (ha : PreservesDiagram a)
    (hL : pointLocal.map a.toMonoidHom = pointLocal) :
    ∃ (g : pointParabolic (F := F)) (σ : F ≃+* F),
      a = (MulAut.conj g.val) * fieldAutomorphism σ ∧
      ∀ A : Matrix.SpecialLinearGroup (Fin 2) F,
        pointSL2Action hcard hn a hL A = pointParabolicQuotient g *
          Matrix.SpecialLinearGroup.map σ.toRingHom A * (pointParabolicQuotient g)⁻¹ := by
  obtain ⟨g, σ, rfl⟩ := SemilinearClassification.inner_field_of_preservesDiagram a ha
  exact ⟨⟨g, point_semilinear_mem_parabolic hcard hn g σ hL⟩, σ, rfl,
    pointSL2Action_semilinear hcard hn g σ hL⟩

/-- The plane-local action includes conjugation by the full GL₂ plane restriction. -/
theorem planeSL2Action_inner_field (a : MulAut (Sp F)) (ha : PreservesDiagram a)
    (hL : planeLocal.map a.toMonoidHom = planeLocal) :
    ∃ (g : planeParabolic (F := F)) (σ : F ≃+* F),
      a = (MulAut.conj g.val) * fieldAutomorphism σ ∧
      ∀ A : Matrix.SpecialLinearGroup (Fin 2) F,
        (planeSL2Action hcard hn a hL A).val = Plane.upperLeft g *
          (Matrix.SpecialLinearGroup.map σ.toRingHom A).val * Plane.upperLeft g⁻¹ := by
  obtain ⟨g, σ, rfl⟩ := SemilinearClassification.inner_field_of_preservesDiagram a ha
  exact ⟨⟨g, plane_semilinear_mem_parabolic hcard hn g σ hL⟩, σ, rfl,
    planeSL2Action_semilinear hcard hn g σ hL⟩

/-- A diagram-preserving two-element in the point quotient kernel is point-local inner. -/
theorem pointSL2Action_kernel_of_preservesDiagram (a : MulAut (Sp F))
    (ha : PreservesDiagram a) (hL : pointLocal.map a.toMonoidHom = pointLocal)
    (htwo : ∃ k : ℕ, a ^ (2 ^ k) = 1)
    (hact : pointSL2Action hcard hn a hL = 1) :
    ∃ l : pointLocal (F := F), a = MulAut.conj l.val := by
  obtain ⟨g, σ, rfl⟩ := SemilinearClassification.inner_field_of_preservesDiagram a ha
  exact pointSL2Action_semilinear_kernel hcard hn g σ hL htwo hact

/-- A diagram-preserving two-element in the plane quotient kernel is plane-local inner. -/
theorem planeSL2Action_kernel_of_preservesDiagram (a : MulAut (Sp F))
    (ha : PreservesDiagram a) (hL : planeLocal.map a.toMonoidHom = planeLocal)
    (htwo : ∃ k : ℕ, a ^ (2 ^ k) = 1)
    (hact : planeSL2Action hcard hn a hL = 1) :
    ∃ l : planeLocal (F := F), a = MulAut.conj l.val := by
  obtain ⟨g, σ, rfl⟩ := SemilinearClassification.inner_field_of_preservesDiagram a ha
  exact planeSL2Action_semilinear_kernel hcard hn g σ hL htwo hact

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
