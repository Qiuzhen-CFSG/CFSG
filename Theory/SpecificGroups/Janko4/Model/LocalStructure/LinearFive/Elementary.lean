module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Relations
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Independence
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Projection

/-!
# The native elementary subgroup of order 1024

The ten literal generators commute and square to one. Their matrix first rows
distinguish all 1024 binary products, giving the exact order of their closure.
The whole subgroup lies in the actual standard-octad pullback Q, and its image
is the complete pointwise octad kernel. No splitting of max1 is assumed.
Source: Kleidman--Wilson (1988), Lemma 1.1.1 and Proposition 2.2.2.
-/

public noncomputable section
namespace Janko4.LocalStructure.LinearFive
open Cardinality KernelCount
open Subgroup
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
  localX localY localKernelSeed basis

theorem generators_square (i : Fin 10) : generators i * generators i = 1 := by
  refine Fin.addCases (m := 6) (n := 4) ?_ ?_ i
  · intro j
    simp only [generators, Fin.append_left]
    exact kernelValue_square (kernelMasks j)
  · intro j
    simp only [generators, Fin.append_right]
    exact lift_square j

theorem generators_commute (i j : Fin 10) : Commute (generators i) (generators j) := by
  refine Fin.addCases (m := 6) (n := 4) ?_ ?_ i <;> intro a
  · refine Fin.addCases (m := 6) (n := 4) ?_ ?_ j <;> intro b
    · simp only [generators, Fin.append_left]
      exact kernelValue_commute (kernelMasks a) (kernelMasks b)
    · simp only [generators, Fin.append_left, Fin.append_right]
      exact kernelGenerator_commute_lift a b
  · refine Fin.addCases (m := 6) (n := 4) ?_ ?_ j <;> intro b
    · simp only [generators, Fin.append_left, Fin.append_right]
      exact (kernelGenerator_commute_lift b a).symm
    · simp only [generators, Fin.append_right]
      exact lift_commute a b

theorem representation_generators (i : Fin 10) :
    representation matrixA_mul_self matrixB_pow_four (generators i) =
      decodeRows (NativeIndependence.generatorRows i) := by
  fin_cases i
  · exact representation_kernelGenerator 0
  · exact representation_kernelGenerator 1
  · exact representation_kernelGenerator 2
  · exact representation_kernelGenerator 3
  · exact representation_kernelGenerator 4
  · exact representation_kernelGenerator 5
  · exact representation_lift 0
  · exact representation_lift 1
  · exact representation_lift 2
  · exact representation_lift 3

theorem generators_binaryProduct_injective : Function.Injective (binaryProduct generators) := by
  intro v w h
  apply NativeIndependence.matrixProduct_injective
  have hh := congrArg (representation matrixA_mul_self matrixB_pow_four) h
  simpa only [map_binaryProduct, representation_generators, NativeIndependence.matrixProduct] using hh

theorem localF_card : Nat.card localF = 1024 :=
  card_closure_binaryProduct generators generators_square generators_commute
    generators_binaryProduct_injective

theorem F_card : Nat.card F = 1024 := by
  rw [F, Subgroup.card_map_of_injective M.subtype_injective, localF_card]

theorem localF_elementary : IsElementaryAbelian 2 localF := by
  refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
  · apply Subgroup.isMulCommutative_closure
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (generators_commute i j).eq
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply Subtype.ext
    obtain ⟨v, hv⟩ := (mem_closure_iff_binaryProduct generators generators_square
      generators_commute (x : M)).mp x.property
    change (x : M) ^ 2 = 1
    rw [← hv, pow_two, binaryProduct_mul generators generators_square generators_commute]
    simpa only [Bool.xor_self] using binaryProduct_zero generators

theorem F_elementary : IsElementaryAbelian 2 F := by
  let _ := localF_elementary
  exact IsElementaryAbelian.map_subtype

/-- Every element of the newly constructed native group is literally a binary
product of the ten native generators. -/
theorem mem_F_iff_binaryProduct (g : Model) :
    g ∈ F ↔ ∃ v : Fin 10 → Bool, ((binaryProduct generators v : M) : Model) = g := by
  constructor
  · intro hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨v, rfl⟩ := (mem_closure_iff_binaryProduct generators generators_square
      generators_commute x).mp hx
    exact ⟨v, rfl⟩
  · rintro ⟨v, rfl⟩
    exact Subgroup.mem_map.mpr ⟨binaryProduct generators v,
      binaryProduct_mem generators v localF generator_mem_localF, rfl⟩

end Janko4.LocalStructure.LinearFive
