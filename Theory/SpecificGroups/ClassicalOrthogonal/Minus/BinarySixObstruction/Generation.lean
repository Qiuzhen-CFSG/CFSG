module

public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.BinarySixObstruction.Generation.Elementary
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.BinarySixObstruction.Generation.Reflections
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.BinarySixObstruction.Iwasawa
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.ReflectionGeneration.SiegelReflections

/-!
# Generation of the binary minus-six commutator group

Every product of two nonsingular reflections is elementary: perpendicular
vectors give a single Siegel transformation, and a nonsingular common
perpendicular connects an arbitrary pair. Reflections generate the full
isometry group by reduction through its two hyperbolic pairs to the binary
anisotropic plane, so its quotient by the elementary subgroup is cyclic. Elementary
perfectness then identifies that subgroup with the actual full-group
commutator subgroup and proves that the latter is perfect.

`elementary_eq_commutator` and `omega_perfect` discharge both algebraic premises
of the literal Iwasawa consumer. The application `isSimpleGroup_of_geometry`
retains only primitivity of the singular-point action as an input. The earlier
conditional interfaces are preserved.

Source: GLS3 §2.7 (`refs/KGroup/GLS3/chapter2.tex`), used for the orthogonal
section in Table 5.3o and Aschbacher--Smith A.2.19. The literal forms and
commutator conventions are those in `BinarySixObstruction.Basic`.
-/

@[expose] public noncomputable section

open ClassicalOrthogonal.Quadratic ClassicalOrthogonal.ReflectionGeneration

namespace ClassicalOrthogonal.Minus.BinarySixObstruction

private theorem reflection_inv (a : NaturalSpace) (ha : naturalForm a ≠ 0) :
    (reflectionElement naturalForm a ha)⁻¹ = reflectionElement naturalForm a ha :=
  Subtype.ext (Module.reflection_inv (reflectionFunctional_self naturalForm a ha))

private theorem perpendicular_reflection_pair_mem (a b : NaturalSpace)
    (ha : naturalForm a ≠ 0) (hb : naturalForm b ≠ 0)
    (hab : naturalForm.polarBilin a b = 0) :
    reflectionElement naturalForm b hb * reflectionElement naturalForm a ha ∈
      elementarySubgroup naturalForm := by
  have hqa : naturalForm a = 1 := (by decide : ∀ c : F, c ≠ 0 → c = 1) _ ha
  have hqb : naturalForm b = 1 := (by decide : ∀ c : F, c ≠ 0 → c = 1) _ hb
  have hba : naturalForm.polarBilin b a = 0 := (polar_swap naturalForm b a).trans hab
  have hu : naturalForm (b+a) = 0 := by
    rw [QuadraticMap.map_add naturalForm]
    change naturalForm b + naturalForm a + naturalForm.polarBilin b a = 0
    rw [hqa, hqb, hba]
    decide
  have hua : naturalForm.polarBilin (b+a) a = 0 := by
    rw [map_add, LinearMap.add_apply, hba, polar_self, hqa]
    decide
  have hv : a + naturalForm a • (b+a) = b := by
    rw [hqa, one_smul]
    have haa : a+a = 0 := (by decide : ∀ x : NaturalSpace, x+x = 0) a
    calc a+(b+a) = b+(a+a) := by abel
         _ = b := by rw [haa, add_zero]
  have he := siegelElement_reflection_factor naturalForm (b+a) a hu hua ha
  have hm := siegelElement_mem naturalForm (b+a) a hu hua
  rw [he] at hm
  simpa only [hv] using hm

/-- Any two nonsingular reflections have elementary product in the six-space.
A nonsingular vector perpendicular to both connects them. -/
theorem reflection_pair_mem_elementary (a b : NaturalSpace)
    (ha : naturalForm a ≠ 0) (hb : naturalForm b ≠ 0) :
    reflectionElement naturalForm b hb * reflectionElement naturalForm a ha ∈
      elementarySubgroup naturalForm := by
  have hd : 5 ≤ Module.finrank F NaturalSpace := by rw [space_finrank]; decide
  obtain ⟨c, hc, hac, hbc⟩ := exists_anisotropic_perpendicular_pair naturalForm
    (quadraticForm_nonsingular F 3) hd a b
  have h1 := perpendicular_reflection_pair_mem c b hc hb
    ((polar_swap naturalForm c b).trans hbc)
  have h2 := perpendicular_reflection_pair_mem a c ha hc hac
  have hm := (elementarySubgroup naturalForm).mul_mem h1 h2
  have he : (reflectionElement naturalForm b hb * reflectionElement naturalForm c hc) *
      (reflectionElement naturalForm c hc * reflectionElement naturalForm a ha) =
      reflectionElement naturalForm b hb * reflectionElement naturalForm a ha := by
    have hc2 : reflectionElement naturalForm c hc * reflectionElement naturalForm c hc = 1 := by
      calc _ = reflectionElement naturalForm c hc * (reflectionElement naturalForm c hc)⁻¹ :=
             congrArg (fun x => reflectionElement naturalForm c hc * x) (reflection_inv c hc).symm
           _ = 1 := mul_inv_cancel _
    calc _ = reflectionElement naturalForm b hb *
               (reflectionElement naturalForm c hc * reflectionElement naturalForm c hc) *
               reflectionElement naturalForm a ha := by group
         _ = _ := by rw [hc2, mul_one]
  exact he ▸ hm

/-- Reflection generation makes the full group elementary-by-cyclic, so its
commutator subgroup is elementary. -/
theorem commutator_le_elementary_of_reflection_generation
    (hreflection : reflectionSubgroup naturalForm = ⊤) :
    commutator FullGroup ≤ elementarySubgroup naturalForm := by
  let a : NaturalSpace := (![(0,0),(0,0)], (1,0))
  have ha : naturalForm a ≠ 0 := by rw [naturalForm_eq]; decide
  let r := reflectionElement naturalForm a ha
  let H : Subgroup FullGroup := elementarySubgroup naturalForm ⊔ Subgroup.zpowers r
  have hr : reflectionSubgroup naturalForm ≤ H := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨b, hb, rfl⟩
    change reflectionElement naturalForm b hb ∈ H
    have hm : reflectionElement naturalForm b hb * r ∈ H :=
      (show elementarySubgroup naturalForm ≤ H from le_sup_left)
        (reflection_pair_mem_elementary a b ha hb)
    have hi : r⁻¹ ∈ H := H.inv_mem
      ((show Subgroup.zpowers r ≤ H from le_sup_right) (Subgroup.mem_zpowers r))
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using H.mul_mem hm hi
  have htop : elementarySubgroup naturalForm ⊔ Subgroup.zpowers r = ⊤ :=
    top_unique (hreflection ▸ hr)
  exact Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top htop inferInstance

/-- Reflection generation identifies the elementary and commutator subgroups. -/
theorem elementary_eq_commutator_of_reflection_generation
    (hreflection : reflectionSubgroup naturalForm = ⊤) :
    elementarySubgroup naturalForm = commutator FullGroup :=
  le_antisymm elementary_le_commutator
    (commutator_le_elementary_of_reflection_generation hreflection)

/-- Perfectness of the literal Omega carrier follows from elementary perfectness
and generation, without using simplicity. -/
theorem omega_perfect_of_reflection_generation
    (hreflection : reflectionSubgroup naturalForm = ⊤) : commutator OmegaGroup = ⊤ := by
  have he := elementary_eq_commutator_of_reflection_generation hreflection
  have hp : Group.IsPerfect OmegaGroup := by
    change Group.IsPerfect (commutator FullGroup)
    rw [← he]
    exact elementary_perfect
  exact hp.commutator_eq_top

/-- The algebraic inputs to the literal scalar-quotient Iwasawa theorem are
discharged by reflection generation; singular-point primitivity stays explicit. -/
theorem isSimpleGroup_of_geometry_and_reflection_generation
    [MulAction.IsPreprimitive OmegaGroup Point]
    (hreflection : reflectionSubgroup naturalForm = ⊤) :
    IsSimpleGroup (ClassicalGroup.POmegaMinus 3 F) :=
  isSimpleGroup_of_geometry_and_generation
    (elementary_eq_commutator_of_reflection_generation hreflection)
    (omega_perfect_of_reflection_generation hreflection)

/-- The Siegel transformations generate the literal full orthogonal group's
commutator subgroup for the binary six-dimensional minus form. -/
theorem elementary_eq_commutator :
    elementarySubgroup naturalForm = commutator FullGroup :=
  elementary_eq_commutator_of_reflection_generation reflectionSubgroup_eq_top

/-- The literal binary minus-six Omega group is perfect. -/
theorem omega_perfect : commutator OmegaGroup = ⊤ :=
  omega_perfect_of_reflection_generation reflectionSubgroup_eq_top

/-- With generation and perfectness proved intrinsically, the literal
scalar-quotient Iwasawa argument requires only singular-point primitivity. -/
theorem isSimpleGroup_of_geometry
    [MulAction.IsPreprimitive OmegaGroup Point] :
    IsSimpleGroup (ClassicalGroup.POmegaMinus 3 F) :=
  isSimpleGroup_of_geometry_and_generation elementary_eq_commutator omega_perfect

end ClassicalOrthogonal.Minus.BinarySixObstruction
