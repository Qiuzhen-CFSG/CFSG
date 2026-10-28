module

public import Theory.SpecificGroups.PSL3.UniversalProjection.Faithfulness.Bruhat.Tori
public import Theory.SpecificGroups.PSL3.UniversalProjection.Faithfulness.Bruhat.Coverage
public import Theory.SpecificGroups.PSL3.UniversalProjection.Faithfulness.Bruhat.Weyl
public import Theory.SpecificGroups.PSL3.UniversalProjection.Faithfulness.Bruhat.Separation

/-!
# Assembling degree-three Bruhat kernel reduction

Bruhat coverage writes a kernel element as `u * w * v`. Upper/monomial
matrix separation forces the matrix of `w` to be the identity. Collection
of the Weyl kernel into the torus, followed by the proved simple-torus
factorization, kills `w`; faithfulness of the positive subgroup kills
`u * v`. This yields the exact kernel-torus conclusion consumed by the
existing faithfulness theorem.

The final theorem supplies the proved coverage, positive-subgroup
faithfulness, Weyl-kernel collection and matrix-separation inputs to the
conditional assembly. Only torus multiplicativity remains explicit; it
is the independent finite-field input retained by the parent faithfulness
task.

Source: Steinberg, *Lectures on Chevalley Groups*, §6, Lemmas 36–38 and
Theorem 8(b), printed pp.69–71; GLS3 §2.9, printed pp.97–98.
-/

@[expose] public section

namespace Matrix.PSL3.UniversalProjection.Faithfulness
open Theory.SpecificGroups.LinearHigher SteinbergWords
variable {F : Type*} [Field F]

/-- Conditional assembly of Bruhat coverage, both restricted kernel
calculations, and matrix separation. Each collection input remains explicit. -/
theorem kernelTorusReduction_of_bruhat_inputs (hC : TorusMultiplicative F)
    (hcover : BruhatCover F) (hU : UpperFaithful F)
    (hW : WeylKernelInTorus F) (hsep : UpperWeylSeparation F) :
    KernelTorusReduction F := by
  intro g hg
  obtain ⟨u, w, v, he⟩ := hcover g
  have hw : matrixMap w.val = matrixMap (u.val⁻¹ * v.val⁻¹) := by
    calc
      _ = (matrixMap u.val)⁻¹ * matrixMap g * (matrixMap v.val)⁻¹ := by
        rw [he, map_mul, map_mul]
        group
      _ = _ := by rw [hg]; simp only [map_mul, map_inv, mul_one]
  have hw1 : matrixMap w.val = 1 := hsep _ _
    ((upperSubgroup F).mul_mem ((upperSubgroup F).inv_mem u.property)
      ((upperSubgroup F).inv_mem v.property)) w.property hw.symm
  have hew : w.val = 1 := torusSubgroup_eq_one_of_matrixMap hC (hW _ w.property hw1) hw1
  have heuv : (u * v : upperSubgroup F) = 1 := by
    apply hU
    change matrixMap (u.val * v.val) = matrixMap 1
    rw [he, hew, mul_one] at hg
    simpa only [map_one] using hg
  have heg : g = 1 := by
    rw [he, hew, mul_one]
    exact congrArg Subtype.val heuv
  refine ⟨1, 1, ?_⟩
  simp [heg, torus, torusWord_one generator_relations]

/-- Assuming relation (C) for the literal torus words, every element of the
matrix kernel is a product of the two simple-root torus words. This discharges
the Bruhat input of `matrixMap_injective_of_kernel_torus`. -/
theorem kernelTorusReduction_of_torusMultiplicative (hC : TorusMultiplicative F) :
    KernelTorusReduction F :=
  kernelTorusReduction_of_bruhat_inputs hC bruhatCover upperFaithful
    (weylKernelInTorus_of_torusMultiplicative hC) upperWeylSeparation

end Matrix.PSL3.UniversalProjection.Faithfulness
