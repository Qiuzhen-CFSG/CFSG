module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour.Dual
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.ReductionClassification.SimpleSupport.TraceSeries
public import Theory.Mathieu.M24.Generators

/-!
# Separation of the native degree-44 kernel and its dual

For the native word `g = (a*b)^3 * (a*b^2)^2`, the code traces at `g` and
`g⁻¹` are respectively one and zero, while both exterior-square traces are
one. The actual contraction exact sequence and code--cocode duality therefore
give kernel traces one and zero. Invariance of trace under equivalence and
the contragredient trace formula distinguish the kernel from its dual,
without any irreducibility assumption.

The code basis is the first eleven native Golay rows modulo constants.
Pivot differences certify its coordinates. The finite certificates compare
the literal native permutation with its table and then its two code matrices;
the exterior trace is computed as the sum of the 55 principal two-by-two
minors. Increasing pairs avoid computation through the abstract sorted-subset
index of the exterior basis. All finite identities are checked by the kernel.

This supplies `hneq` in `binaryFortyFourModelsExist_of_native_kernel`.
Source context: James, The modular characters of the Mathieu groups,
J. Algebra 27 (1973), 57--111; GM02, Proposition 5.1, manuscript p.17.
-/

public section

open Sporadic.Mathieu MathieuCode Representation
open Representation.MathieuM24Degree44.FiveSpace
open scoped BigOperators
noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour.DualSeparation

private abbrev Coordinates := Fin 11 → ZMod 2

private def reduce : Full →ₗ[ZMod 2] Coordinates where
  toFun v i := v (pivot i.castSucc) - v (pivot 11)
  map_add' v w := by ext i; simp; ring
  map_smul' c v := by ext i; simp [mul_sub]

private lemma line_le_ker : codeLine ≤ (reduce.comp golay.subtype).ker := by
  intro v hv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
  apply funext
  intro i
  change v.val (pivot i.castSucc) - v.val (pivot 11) = 0
  change c • BinaryPermutation.allOne (Fin 24) = v.val at hc
  rw [← hc]
  simp [BinaryPermutation.allOne]

private def coordinates : Code →ₗ[ZMod 2] Coordinates :=
  codeLine.liftQ (reduce.comp golay.subtype) line_le_ker

private lemma coordinates_mk (v : golay) : coordinates (codeLine.mkQ v) = reduce v.val := rfl

private lemma reduce_row : ∀ j : Fin 11, reduce (row j.castSucc) = Pi.single j 1 := by
  decide +kernel

private def sectionMap : Coordinates →ₗ[ZMod 2] Code :=
  ∑ j : Fin 11, (LinearMap.proj j).smulRight (codeLine.mkQ ⟨row j.castSucc, row_mem _⟩)

private lemma sectionMap_single (j : Fin 11) :
    sectionMap (Pi.single j 1) = codeLine.mkQ ⟨row j.castSucc, row_mem _⟩ := by
  simp [sectionMap, Pi.single_apply]

private lemma coordinates_sectionMap : coordinates.comp sectionMap = LinearMap.id := by
  apply LinearMap.pi_ext
  intro j c
  have he : Pi.single j c = c • (Pi.single j 1 : Coordinates) := by
    simp [← Pi.single_smul]
  change coordinates (sectionMap (Pi.single j c)) = Pi.single j c
  rw [he, map_smul, map_smul, sectionMap_single, coordinates_mk, reduce_row]

private lemma coordinates_surjective : Function.Surjective coordinates := by
  intro v
  exact ⟨sectionMap v, LinearMap.congr_fun coordinates_sectionMap v⟩

private def coordinateEquiv : Code ≃ₗ[ZMod 2] Coordinates :=
  LinearEquiv.ofBijective coordinates ⟨
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [finrank_code]; simp [Coordinates])).mpr coordinates_surjective,
    coordinates_surjective⟩

private def codeBasis : Module.Basis (Fin 11) (ZMod 2) Code :=
  (Pi.basisFun (ZMod 2) (Fin 11)).map coordinateEquiv.symm

private lemma codeBasis_apply (j : Fin 11) :
    codeBasis j = codeLine.mkQ ⟨row j.castSucc, row_mem _⟩ := by
  apply coordinateEquiv.injective
  simp only [codeBasis, Module.Basis.map_apply, Pi.basisFun_apply,
    LinearEquiv.apply_symm_apply]
  change Pi.single j 1 = reduce (row j.castSucc)
  exact (reduce_row j).symm

private lemma codeBasis_repr (v : Code) (j : Fin 11) : codeBasis.repr v j = coordinates v j := by
  simp only [codeBasis, Module.Basis.map_repr]
  rfl

private def codeMatrix (g : M24) : Matrix (Fin 11) (Fin 11) (ZMod 2) :=
  fun i j => reduce (fullRepresentation g (row j.castSucc)) i

private lemma codeMatrix_eq (g : M24) :
    LinearMap.toMatrix codeBasis codeBasis (codeRepresentation g) = codeMatrix g := by
  ext i j
  rw [LinearMap.toMatrix_apply, codeBasis_repr, codeBasis_apply,
    codeRepresentation_mk, coordinates_mk]
  rfl

private abbrev Pair := Set.powersetCard (Fin 11) 2

private def exteriorTrace (M : Matrix (Fin 11) (Fin 11) (ZMod 2)) : ZMod 2 :=
  ∑ s : Pair, let e := Set.powersetCard.ofFinEmbEquiv.symm s
    M (e 0) (e 0) * M (e 1) (e 1) - M (e 0) (e 1) * M (e 1) (e 0)

private abbrev IncreasingPair := {p : Fin 11 × Fin 11 // p.1 < p.2}

private def pairEmbedding (p : IncreasingPair) : Fin 2 ↪o Fin 11 :=
  OrderEmbedding.ofStrictMono ![p.val.1, p.val.2]
    (Fin.strictMono_iff_lt_succ.mpr (by intro i; fin_cases i; exact p.property))

private def pairEmbeddingEquiv : IncreasingPair ≃ (Fin 2 ↪o Fin 11) where
  toFun := pairEmbedding
  invFun f := ⟨(f 0, f 1), f.strictMono (by decide)⟩
  left_inv p := rfl
  right_inv f := by ext i; fin_cases i <;> rfl

private def pairEquiv : IncreasingPair ≃ Pair :=
  pairEmbeddingEquiv.trans Set.powersetCard.ofFinEmbEquiv

private def minorTrace (M : Matrix (Fin 11) (Fin 11) (ZMod 2)) : ZMod 2 :=
  ∑ p : IncreasingPair,
    (M p.val.1 p.val.1 * M p.val.2 p.val.2 - M p.val.1 p.val.2 * M p.val.2 p.val.1)

private lemma exteriorTrace_eq (M : Matrix (Fin 11) (Fin 11) (ZMod 2)) :
    exteriorTrace M = minorTrace M := by
  unfold exteriorTrace
  rw [← Equiv.sum_comp pairEquiv]
  unfold minorTrace
  apply Finset.sum_congr rfl
  intro p _
  have he : Set.powersetCard.ofFinEmbEquiv.symm (pairEquiv p) = pairEmbedding p :=
    Set.powersetCard.ofFinEmbEquiv.symm_apply_apply _
  dsimp only
  rw [he]
  rfl

private lemma code_trace (g : M24) : codeRepresentation.character g = (codeMatrix g).trace := by
  rw [character, LinearMap.trace_eq_matrix_trace (ZMod 2) codeBasis, codeMatrix_eq]

private lemma exterior_trace (g : M24) : codeExterior.character g = exteriorTrace (codeMatrix g) := by
  rw [character, LinearMap.trace_eq_matrix_trace (ZMod 2) (codeBasis.exteriorPower 2)]
  unfold Matrix.trace exteriorTrace
  apply Finset.sum_congr rfl
  intro s _
  simp only [Matrix.diag_apply]
  rw [LinearMap.toMatrix_apply, exteriorPower.basis_repr_apply,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family]
  change exteriorPower.ιMultiDual (ZMod 2) 2 codeBasis s
    (exteriorPower.map 2 (codeRepresentation g) (exteriorPower.ιMulti (ZMod 2) 2 _)) = _
  rw [exteriorPower.map_apply_ιMulti, exteriorPower.ιMultiDual_apply_ιMulti,
    Matrix.det_fin_two]
  simp only [Matrix.of_apply, Function.comp_apply, Module.Basis.coord_apply]
  have h (i j : Fin 11) : codeBasis.repr (codeRepresentation g (codeBasis j)) i =
      codeMatrix g i j := by
    simpa only [LinearMap.toMatrix_apply] using congrFun (congrFun (codeMatrix_eq g) i) j
  simp only [h]
  ring

/-- The native word separating the contraction kernel from its contragredient. -/
@[expose] def separator : M24 :=
  let a : M24 := ⟨m24GeneratorA, m24GeneratorA_mem⟩
  let b : M24 := ⟨m24GeneratorB, m24GeneratorB_mem⟩
  (a * b) ^ 3 * (a * b ^ 2) ^ 2

private def bitColumns (v : Fin 11 → BitVec 11) : Matrix (Fin 11) (Fin 11) (ZMod 2) :=
  fun i j => if (v j).getLsb i then 1 else 0

private def separatorMatrix := bitColumns ![1090,15,1537,201,1035,1015,72,67,1355,1089,18]
private def inverseMatrix := bitColumns ![81,592,194,705,1616,1343,641,25,913,133,208]

private def separatorPermutation : Fin 24 → Fin 24 :=
  ![20,2,9,7,15,13,17,18,8,19,0,4,21,5,11,1,14,22,12,3,6,16,23,10]
private def inversePermutation : Fin 24 → Fin 24 :=
  ![10,15,1,19,11,13,20,3,8,2,23,14,18,5,16,4,21,6,7,9,0,12,17,22]

private lemma separator_permutation : (separator.val : Fin 24 → Fin 24) = separatorPermutation := by
  decide +kernel

private lemma separator_inverse_permutation : (separator.val.symm : Fin 24 → Fin 24) = inversePermutation := by
  funext i
  apply separator.val.injective
  rw [_root_.Equiv.apply_symm_apply]
  change i = (separator.val : Fin 24 → Fin 24) (inversePermutation i)
  rw [separator_permutation]
  have h : ∀ i, i = separatorPermutation (inversePermutation i) := by decide +kernel
  exact h i

private lemma codeMatrix_of_inverse (g : M24) (p : Fin 24 → Fin 24)
    (hp : (g.val.symm : Fin 24 → Fin 24) = p) :
    codeMatrix g = Matrix.of (fun i j : Fin 11 =>
      row j.castSucc (p (pivot i.castSucc)) - row j.castSucc (p (pivot 11))) := by
  ext i j
  change row j.castSucc (g.val.symm (pivot i.castSucc)) - row j.castSucc (g.val.symm (pivot 11)) = _
  rw [hp]
  rfl

private lemma codeMatrix_inv_of_forward (g : M24) (p : Fin 24 → Fin 24)
    (hp : (g.val : Fin 24 → Fin 24) = p) :
    codeMatrix g⁻¹ = Matrix.of (fun i j : Fin 11 =>
      row j.castSucc (p (pivot i.castSucc)) - row j.castSucc (p (pivot 11))) :=
  codeMatrix_of_inverse g⁻¹ p hp

private lemma separatorMatrix_eq : codeMatrix separator = separatorMatrix := by
  have h : Matrix.of (fun i j : Fin 11 =>
      row j.castSucc (inversePermutation (pivot i.castSucc)) -
        row j.castSucc (inversePermutation (pivot 11))) = separatorMatrix := by decide +kernel
  exact (codeMatrix_of_inverse separator inversePermutation separator_inverse_permutation).trans h

private lemma inverseMatrix_eq : codeMatrix separator⁻¹ = inverseMatrix := by
  have h : Matrix.of (fun i j : Fin 11 =>
      row j.castSucc (separatorPermutation (pivot i.castSucc)) -
        row j.castSucc (separatorPermutation (pivot 11))) = inverseMatrix := by decide +kernel
  exact (codeMatrix_inv_of_forward separator separatorPermutation separator_permutation).trans h

private lemma code_trace_separator : (codeMatrix separator).trace = 1 := by
  rw [separatorMatrix_eq]
  decide +kernel
private lemma code_trace_separator_inv : (codeMatrix separator⁻¹).trace = 0 := by
  rw [inverseMatrix_eq]
  decide +kernel
private lemma exterior_trace_separator : exteriorTrace (codeMatrix separator) = 1 := by
  rw [separatorMatrix_eq, exteriorTrace_eq]
  decide +kernel
private lemma exterior_trace_separator_inv : exteriorTrace (codeMatrix separator⁻¹) = 1 := by
  rw [inverseMatrix_eq, exteriorTrace_eq]
  decide +kernel

private def quotientKerEquiv {F G V W : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    {ρ : Representation F G V} {σ : Representation F G W}
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) :
    f.ker.quotientRepresentation.Equiv σ :=
  .mk (f.toLinearMap.quotKerEquivOfSurjective hf) (by
    intro g
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | _ v =>
      change f (ρ g v) = σ g (f v)
      exact LinearMap.congr_fun (f.isIntertwining' g) v)

private lemma kernel_trace_add_cocode (g : M24) :
    codeExterior.character g = kernelRepresentation.character g + cocodeRepresentation.character g := by
  have h := congrFun (character_eq_subrepresentation_add_quotient codeExterior kernel) g
  have he := char_iso (quotientKerEquiv contraction contraction_surjective)
  change codeExterior.character g = kernelRepresentation.character g +
    kernel.quotientRepresentation.character g at h
  rw [show kernel.quotientRepresentation.character = cocodeRepresentation.character from he] at h
  exact h

private lemma cocode_trace (g : M24) : cocodeRepresentation.character g = codeRepresentation.character g⁻¹ := by
  rw [char_iso cocodeDuality, char_dual]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour.DualSeparation

namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour
/-- The separating word has trace one on the literal contraction kernel. -/
theorem kernel_trace_separator : kernelRepresentation.character DualSeparation.separator = 1 := by
  have h := DualSeparation.kernel_trace_add_cocode DualSeparation.separator
  rw [DualSeparation.exterior_trace, DualSeparation.exterior_trace_separator,
    DualSeparation.cocode_trace, DualSeparation.code_trace,
    DualSeparation.code_trace_separator_inv, add_zero] at h
  exact h.symm

/-- Its inverse has trace zero on the same native kernel. -/
theorem kernel_trace_separator_inv : kernelRepresentation.character DualSeparation.separator⁻¹ = 0 := by
  have h := DualSeparation.kernel_trace_add_cocode DualSeparation.separator⁻¹
  rw [DualSeparation.exterior_trace, DualSeparation.exterior_trace_separator_inv,
    DualSeparation.cocode_trace, inv_inv, DualSeparation.code_trace,
    DualSeparation.code_trace_separator] at h
  exact add_right_cancel (h.symm.trans (zero_add (1 : ZMod 2)).symm)

/-- The native degree-44 contraction kernel and its contragredient are inequivalent.
This argument uses traces and does not require irreducibility. -/
theorem kernel_dual_inequivalent : IsEmpty (kernelRepresentation.Equiv dualKernelRepresentation) := by
  refine ⟨fun e => ?_⟩
  have h := congrFun (char_iso e) DualSeparation.separator
  change kernelRepresentation.character DualSeparation.separator =
    kernelRepresentation.dual.character DualSeparation.separator at h
  rw [char_dual, kernel_trace_separator, kernel_trace_separator_inv] at h
  exact zero_ne_one h.symm

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour
