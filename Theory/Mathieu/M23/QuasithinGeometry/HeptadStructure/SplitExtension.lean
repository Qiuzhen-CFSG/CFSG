module

public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.BinaryKernel
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.AlternatingSection
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.Order
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The split heptad stabilizer in the concrete M23

The kernel has order sixteen and the stabilizer has order 40320. Together
with the explicit alternating section, this forces the labelled action image
to be exactly A7. Multiplication of a translation and a section element then
gives the isomorphism from the binary semidirect product to the stabilizer.
All maps retain the original inclusion into the design automorphism group.

The lifted three-cycle fixes exactly the complementary point 0. Any commuting
translation must fix that point, and hence is the identity. This proves the
exceptional conjugation property, independently of any order descriptor.

Source: Aschbacher--Smith, §5.2, printed p.655 (PDF p.672); Aschbacher,
*Sporadic Groups*, Chapter 6, Lemma 19.1 and its M23 specialization.
-/

@[expose] public section
namespace Sporadic.Mathieu.M23Geometry
open scoped Pointwise

/-- The image of the concrete heptad action is precisely the alternating group. -/
theorem heptadAction_range : heptadAction.range = alternatingGroup (Fin 7) := by
  have hle : alternatingGroup (Fin 7) ≤ heptadAction.range := by
    intro a ha
    exact ⟨AlternatingSection.s ⟨a, ha⟩, AlternatingSection.heptadAction_s _⟩
  symm
  apply Subgroup.eq_of_le_of_card_ge hle
  have hc : Nat.card heptadAction.range = 2520 := by
    rw [← Subgroup.index_ker heptadAction]
    have h := Subgroup.card_mul_index heptadKernel
    rw [heptadKernel_card, heptadStabilizer_card] at h
    change 16 * heptadAction.ker.index = 40320 at h
    omega
  rw [hc, nat_card_alternatingGroup]
  norm_num [Nat.factorial]

/-- The labelled quotient map, with its exact alternating codomain. -/
noncomputable def heptadAlternatingAction : heptadStabilizer →* alternatingGroup (Fin 7) :=
  heptadAction.codRestrict _ (fun g => by rw [← heptadAction_range]; exact ⟨g, rfl⟩)

@[simp] theorem heptadAlternatingAction_coe (g : heptadStabilizer) :
    (heptadAlternatingAction g : Equiv.Perm (Fin 7)) = heptadAction g := rfl

@[simp] theorem heptadAlternatingAction_section (a : alternatingGroup (Fin 7)) :
    heptadAlternatingAction (AlternatingSection.s a) = a :=
  Subtype.ext (AlternatingSection.heptadAction_s a)

/-- The actual conjugation action of the complement on the pointwise kernel. -/
noncomputable def heptadConjugation : alternatingGroup (Fin 7) →* MulAut heptadKernel :=
  MulAut.conjNormal.comp AlternatingSection.s

@[simp] theorem heptadConjugation_coe (a : alternatingGroup (Fin 7)) (u : heptadKernel) :
    (heptadConjugation a u : heptadStabilizer) =
      AlternatingSection.s a * u * (AlternatingSection.s a)⁻¹ :=
  MulAut.conjNormal_apply _ _

/-- Multiplication of the kernel and the explicit alternating complement. -/
noncomputable def heptadSplitHom :
    heptadKernel ⋊[heptadConjugation] alternatingGroup (Fin 7) →* heptadStabilizer :=
  SemidirectProduct.lift heptadKernel.subtype AlternatingSection.s (by
    intro a
    apply DFunLike.ext
    intro u
    exact heptadConjugation_coe a u)

@[simp] theorem heptadSplitHom_apply
    (z : heptadKernel ⋊[heptadConjugation] alternatingGroup (Fin 7)) :
    heptadSplitHom z = z.left * AlternatingSection.s z.right := rfl

@[simp] theorem heptadAction_split
    (z : heptadKernel ⋊[heptadConjugation] alternatingGroup (Fin 7)) :
    heptadAction (heptadSplitHom z) = (z.right : Equiv.Perm (Fin 7)) := by
  rw [heptadSplitHom_apply, map_mul, z.left.property,
    AlternatingSection.heptadAction_s, one_mul]

theorem heptadSplitHom_bijective : Function.Bijective heptadSplitHom := by
  constructor
  · intro z w h
    have hr : z.right = w.right := by
      apply Subtype.ext
      simpa only [heptadAction_split] using congrArg heptadAction h
    have hl : z.left = w.left := by
      apply Subtype.ext
      simpa only [heptadSplitHom_apply, hr, mul_left_inj] using h
    exact SemidirectProduct.ext hl hr
  · intro g
    let a := heptadAlternatingAction g
    let u : heptadKernel := ⟨g * (AlternatingSection.s a)⁻¹, by
      change heptadAction (g * (AlternatingSection.s a)⁻¹) = 1
      rw [map_mul, map_inv, AlternatingSection.heptadAction_s]
      exact mul_inv_cancel _⟩
    exact ⟨⟨u, a⟩, inv_mul_cancel_right g (AlternatingSection.s a)⟩

/-- The split extension, as an actual multiplicative equivalence. -/
noncomputable def heptadSplitEquiv :
    heptadKernel ⋊[heptadConjugation] alternatingGroup (Fin 7) ≃* heptadStabilizer :=
  MulEquiv.ofBijective heptadSplitHom heptadSplitHom_bijective

/-- Conjugation expressed on the four-dimensional binary space. -/
noncomputable def heptadBinaryAction :
    alternatingGroup (Fin 7) →* MulAut (Multiplicative (Fin 4 → ZMod 2)) :=
  (MulAut.congr heptadBinaryEquiv.symm).toMonoidHom.comp heptadConjugation

@[simp] theorem heptadBinaryAction_equivariant (a : alternatingGroup (Fin 7))
    (v : Multiplicative (Fin 4 → ZMod 2)) :
    heptadBinaryEquiv (heptadBinaryAction a v) =
      heptadConjugation a (heptadBinaryEquiv v) := by
  simp [heptadBinaryAction, MulAut.congr]

/-- The binary semidirect product identifies the concrete stabilizer. -/
noncomputable def heptadBinarySplitEquiv :
    Multiplicative (Fin 4 → ZMod 2) ⋊[heptadBinaryAction] alternatingGroup (Fin 7) ≃*
      heptadStabilizer :=
  (SemidirectProduct.congr heptadBinaryEquiv (MulEquiv.refl _) (by
    intro a
    apply DFunLike.ext
    intro v
    exact heptadBinaryAction_equivariant a v)).trans heptadSplitEquiv

@[simp] theorem heptadBinarySplitEquiv_apply
    (z : Multiplicative (Fin 4 → ZMod 2) ⋊[heptadBinaryAction] alternatingGroup (Fin 7)) :
    heptadBinarySplitEquiv z = heptadBinaryEquiv z.left * AlternatingSection.s z.right := rfl

/-- The source three-cycle fixes no nonidentity kernel element under conjugation. -/
theorem heptadConjugation_cycle_fixed_iff (u : heptadKernel) :
    heptadConjugation AlternatingSection.c u = u ↔ u = 1 := by
  constructor
  · intro h
    have hc : AlternatingSection.s AlternatingSection.c * u =
        u * AlternatingSection.s AlternatingSection.c := by
      have h' := congrArg (fun v : heptadKernel => (v : heptadStabilizer)) h
      rw [heptadConjugation_coe] at h'
      exact (mul_inv_eq_iff_eq_mul).mp h'
    apply heptadKernel_eq_one_of_fix u (by decide +kernel : (0 : Fin 23) ∉ omega)
    apply (AlternatingSection.s_c_fixed_iff _
      (heptadKernel_smul_mem_complement u (by decide +kernel : (0 : Fin 23) ∈ pairComplement omega))).mp
    have h' := congrArg (fun g : heptadStabilizer => (g : M23) • (0 : Fin 23)) hc
    simpa only [Subgroup.coe_mul, mul_smul, AlternatingSection.s_zero] using h'
  · rintro rfl
    exact map_one _

theorem heptadBinaryAction_cycle_fixed_iff (v : Multiplicative (Fin 4 → ZMod 2)) :
    heptadBinaryAction AlternatingSection.c v = v ↔ v = 1 := by
  rw [← heptadBinaryEquiv.injective.eq_iff, heptadBinaryAction_equivariant,
    heptadConjugation_cycle_fixed_iff, map_eq_one_iff _ heptadBinaryEquiv.injective]

/-- The alternating section is precisely the stabilizer of the binary origin. -/
theorem heptadSection_range : AlternatingSection.s.range = AlternatingSection.pointComplement := by
  apply le_antisymm
  · rintro g ⟨a, rfl⟩
    exact AlternatingSection.s_zero a
  · intro g hg
    exact ⟨heptadAlternatingAction g,
      AlternatingSection.s_eq_of_action _ g hg rfl⟩

/-- The alternating quotient has exactly the pointwise heptad kernel. -/
theorem heptadAlternatingAction_ker : heptadAlternatingAction.ker = heptadKernel :=
  MonoidHom.ker_codRestrict _ _ _

/-- The actual quotient of the heptad stabilizer by U is A7. -/
noncomputable def heptadQuotientAlternatingEquiv :
    heptadStabilizer ⧸ heptadKernel ≃* alternatingGroup (Fin 7) :=
  (QuotientGroup.quotientMulEquivOfEq heptadAlternatingAction_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective heptadAlternatingAction
      (fun a => ⟨AlternatingSection.s a, heptadAlternatingAction_section a⟩))

@[simp] theorem heptadQuotientAlternatingEquiv_mk (g : heptadStabilizer) :
    heptadQuotientAlternatingEquiv (QuotientGroup.mk g) = heptadAlternatingAction g := rfl

end Sporadic.Mathieu.M23Geometry
