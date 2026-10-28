module
public import Theory.AlgebraicGroup.RootSystems.F4WeightAction.Stabilizer.Comparison
public import Theory.AlgebraicGroup.RootSystems.F4WeightAction.Stabilizer.Checks

/-!
# Point-dependent reflection generation in F4, characteristic two

A unit-valued evaluation on the full integral weight lattice is fixed by a
Weyl element precisely along its displacement lattice. For 1,136 Weyl elements,
checked doubled-root witnesses give a factorization into vanishing-root
reflections because field units have no nontrivial two-torsion. The remaining
sixteen elements are conjugates of a determinant-nine representative. Two
cubic coordinates satisfy one of four line relations, each with a checked
four-reflection factorization. Native simple-word comparison identifies all
certificate entries in the original F4 root pairing.

This discharges the Weyl-stabilizer input of the actual Ree-F4 semisimple
centralizer connectedness proof. No algebraic closedness, finite field,
abstract Weyl identification or stabilizer certificate is a hypothesis of
`mem_reflectionKernel_of_fixed`.

Source: Steinberg, semisimple centralizers; GLS3 Chapter 2, 8.2(6)–(7) and
8.3(c), retaining the full weight lattice and the cubic-torsion exceptional case.
-/

namespace Theory.AlgebraicGroup.StandardRootSystem.F4WeightAction.Stabilizer
public noncomputable section
open Comparison
variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
private theorem path_mem (c : Certificate) (ev : Weight →+ Additive Fˣ)
    (k : Fin 1152) (l : List (Fin 24 × Fin 1152 × Data.V))
    (hp : Data.pathValid k l) (hz : ∀x ∈ l, ev (Data.weights x.1) = 0) :
    representative k ∈ reflectionKernel ev := by
  induction l generalizing k with
  | nil =>
    change k = 0 at hp
    subst k
    rw [representative_zero c]
    exact Subgroup.one_mem _
  | cons x xs ih =>
    obtain ⟨hm,ht⟩ := hp
    have he := product_eq c k 0 (Data.refIndex x.1) x.2.1
      (by simpa only [c.matrix_zero, mul_one] using hm)
    rw [representative_zero c, mul_one] at he
    rw [he]
    apply Subgroup.mul_mem
    · rw [← root_reflection c]
      apply Subgroup.subset_closure
      refine ⟨root x.1, ?_, rfl⟩
      simpa only [Set.mem_ofPred_eq, root_weight c] using hz x (List.mem_cons_self ..)
    · exact ih _ ht (fun y hy => hz y (List.mem_cons_of_mem _ hy))

private theorem ordinary_mem (c : Certificate) (ev : Weight →+ Additive Fˣ)
    (k : Fin 1152) (hk : Data.kind k = none)
    (hw : ∀a, ev (representation (representative k) a) = ev a) :
    representative k ∈ reflectionKernel ev := by
  apply path_mem c ev k (Data.path k) (c.ordinary_path k hk)
  intro x hx
  rw [← root_weight c]
  apply doubled_root_zero ev (representative k) hw (root x.1) x.2.2
  rw [representation_representative c, root_weight c]
  exact c.ordinary_witness k x hx

private theorem exceptional_path_valid (k : Fin 1152)
    (l : List (Fin 24 × Fin 1152 × ℤ × Data.V)) (h : Data.exceptionPathValid k l) :
    Data.pathValid k (l.map fun x => (x.1, x.2.1, x.2.2.2)) := by
  induction l generalizing k with
  | nil => exact h
  | cons x xs ih => exact ⟨h.1, ih _ h.2⟩

omit [CharP F 2] in
private theorem exceptional_mem (c : Certificate) (ev : Weight →+ Additive Fˣ)
    (hw : ∀a, ev (representation (representative Data.exceptional) a) = ev a) :
    representative Data.exceptional ∈ reflectionKernel ev := by
  have hc (i : Fin 2) : (3:ℤ) • ev (Pi.single (i.castLE (by decide)) 1) = 0 := by
    have h := ev_displacement ev (representative Data.exceptional) hw (Data.cubeWitness i)
    rw [representation_representative c, c.cube, map_zsmul] at h
    exact h
  have he : ∃ i, ev (Data.line i) = 0 := by
    rcases additive_cube_cases (ev (Pi.single 0 1)) (ev (Pi.single 1 1)) (hc 0) (hc 1)
      with h | h | h | h
    · exact ⟨0, by simpa only [c.lines, Matrix.cons_val_zero] using h⟩
    · exact ⟨1, by simpa only [c.lines, Matrix.cons_val_one, Matrix.cons_val_zero] using h⟩
    · refine ⟨2, ?_⟩
      simpa [c.lines, map_sub] using h
    · refine ⟨3, ?_⟩
      rw [c.lines]
      change ev (Pi.single 1 1 - (2:ℤ) • Pi.single 0 1) = 0
      simpa only [map_sub, map_zsmul] using h
  obtain ⟨i,hi⟩ := he
  apply path_mem c ev Data.exceptional
    ((Data.exceptionPath i).map fun x => (x.1, x.2.1, x.2.2.2))
    (exceptional_path_valid _ _ (c.exceptional_path i))
  intro x hx
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
  have hd := ev_displacement ev (representative Data.exceptional) hw y.2.2.2
  rw [representation_representative c] at hd
  rw [← c.exceptional_witness i y hy, map_add, map_zsmul, hd, hi, smul_zero, add_zero]

omit [CharP F 2] in
private theorem exceptional_conjugate_mem (c : Certificate) (ev : Weight →+ Additive Fˣ)
    (j : Fin 16)
    (hw : ∀a, ev (representation (representative (Data.exceptionIndex j)) a) = ev a) :
    representative (Data.exceptionIndex j) ∈ reflectionKernel ev := by
  let g := representative (Data.exceptionConj j)
  let w := representative Data.exceptional
  have he : representative (Data.exceptionIndex j) * g = g * w :=
    product_eq c _ _ _ _ (c.exception_conjugate j)
  have hfix : ∀a, (ev.comp (representation g).toAddMonoidHom) (representation w a) =
      (ev.comp (representation g).toAddMonoidHom) a := by
    intro a
    change ev (representation g (representation w a)) = ev (representation g a)
    have he' := congrArg (fun v : Weyl => representation v a) he
    simp only [map_mul, LinearEquiv.mul_apply] at he'
    rw [← he', hw]
  have h := conjugate_mem_kernel ev g w (exceptional_mem c _ hfix)
  have heq : g * w * g⁻¹ = representative (Data.exceptionIndex j) := by
    rw [← he]
    group
  rwa [heq] at h

private theorem mem_reflectionKernel_of_fixed_of_certificate (c : Certificate)
    (ev : Weight →+ Additive Fˣ) (w : Weyl)
    (hw : ∀a, ev (representation w a) = ev a) : w ∈ reflectionKernel ev := by
  obtain ⟨k,rfl⟩ := exists_representative c w
  cases hk : Data.kind k with
  | none => exact ordinary_mem c ev k hk hw
  | some j =>
    have he := c.exception_index k j hk
    subst k
    exact exceptional_conjugate_mem c ev j hw

/-- In characteristic two, a Weyl element fixing a torus evaluation belongs
to the subgroup generated by the reflections in roots vanishing there. -/
theorem mem_reflectionKernel_of_fixed
    (ev : Weight →+ Additive Fˣ) (w : Weyl)
    (hw : ∀a, ev (representation w a) = ev a) : w ∈ reflectionKernel ev :=
  mem_reflectionKernel_of_fixed_of_certificate Checks.certificate ev w hw

end
end Theory.AlgebraicGroup.StandardRootSystem.F4WeightAction.Stabilizer
