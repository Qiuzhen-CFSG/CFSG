module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.TensorGrading.SourceSupport.FiniteGrading
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.TensorGrading.SourceSupport.Spanning

/-!
# Source support and primitive tests for the actual basic tensor filtration

The genuine basic highest vectors mark degree zero. Actual coroot weight
spanning and degree independence give finite support. The proved source
primitive line excludes negative occupied degrees, identifies degree zero
with the highest tensor line, and gives the primitive test modulo the next
lower filtration layer. Universality of the literal F4 carrier is the sole
independent source input; no finite irreducibility or local certificate is
assumed.

Source: Steinberg (1963), Section 12, the positive filtration argument.
-/

public section
noncomputable section
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
open Theory.AlgebraicGroup StandardRootSystem AlgebraicTensor
universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]

/-- The actual integral highest weights of the source basic factors. -/
@[expose] def sourceTensorWeights (b : ℕ → BasicWeight) : ℕ → EndNode.Weight :=
  fun i j => (basicCoefficient (b i) j : ℤ)

omit [CharP F 2] in
private theorem source_highest_mem_zero (m : ℕ)
    (B : ZMod (2*m+1) → AlgebraicFactor F)
    (b : ℕ → BasicWeight) (v : ∀i, (basicFactor m B i).Space)
    (hv : ∀i, (basicFactor m B i).IsBasicHighestWeightVector (b i) (v i)) (n : ℕ) :
    Submodule.span F {highestTensor m B v n} ≤ tensorDegreeSpace m B (sourceTensorWeights b) n 0 := by
  apply (Submodule.span_singleton_le_iff_mem _ _).mpr
  exact highestTensor_mem_degree_zero m B _ v
    (fun i => EndNode.basicHighestWeightVector_mem_corootWeightSpace (hv i)) n

private def sourceCoordinate (m : ℕ) (B : ZMod (2*m+1) → AlgebraicFactor F)
    (p : ∀i, RootExpansion (basicFactor m B i).action) (n : ℕ)
    (q : Fin n × ShortPositiveRoot) : Module.End F (basicTensorSpace m B n) :=
  coordinateMap m B n q.1.val ((p q.1.val).coeff q.2.val 1)

private def sourceDegree {n : ℕ} (q : Fin n × ShortPositiveRoot) : ℤ :=
  weightDegree (rootWeight q.2.val)

private theorem sourceDegree_pos {n : ℕ} (q : Fin n × ShortPositiveRoot) :
    0 < sourceDegree q := weightDegree_rootWeight_pos q.2.property.2

omit [CharP F 2] in
private theorem sourceCoordinate_shift (m : ℕ)
    (B : ZMod (2*m+1) → AlgebraicFactor F)
    (p : ∀i, RootExpansion (basicFactor m B i).action) (b : ℕ → BasicWeight) (n : ℕ)
    (q : Fin n × ShortPositiveRoot) (k : ℤ) (x : basicTensorSpace m B n)
    (hx : x ∈ tensorDegreeSpace m B (sourceTensorWeights b) n k) :
    sourceCoordinate m B p n q x ∈
      tensorDegreeSpace m B (sourceTensorWeights b) n (k-sourceDegree q) :=
  coordinateCoefficient_degreeSpace m B _ n q.1.val q.1.isLt (p q.1.val) q.2.val k
    (Submodule.mem_map_of_mem hx)

private theorem sourceCoordinate_kernel (m : ℕ)
    (B : ZMod (2*m+1) → AlgebraicFactor F)
    (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    (p : ∀i, RootExpansion (basicFactor m B i).action)
    (b : ℕ → BasicWeight) (v : ∀i, (basicFactor m B i).Space)
    (hv : ∀i, (basicFactor m B i).IsBasicHighestWeightVector (b i) (v i))
    (n : ℕ) (x : basicTensorSpace m B n) :
    (∀q : Fin n × ShortPositiveRoot, sourceCoordinate m B p n q x = 0) ↔
      x ∈ Submodule.span F {highestTensor m B v n} := by
  simpa only [sourceCoordinate, Prod.forall, Fin.forall_iff] using
    source_prefix_primitive_iff m B hU p b v hv n x

/-- The filtration starts with exactly the tensor of the actual highest lines. -/
theorem source_tensorFiltration_zero (m : ℕ)
    (B : ZMod (2*m+1) → AlgebraicFactor F)
    (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    (p : ∀i, RootExpansion (basicFactor m B i).action)
    (b : ℕ → BasicWeight) (v : ∀i, (basicFactor m B i).Space)
    (hv : ∀i, (basicFactor m B i).IsBasicHighestWeightVector (b i) (v i)) (n : ℕ) :
    tensorFiltration m B (sourceTensorWeights b) n 0 =
      Submodule.span F {highestTensor m B v n} := by
  rw [tensorFiltration_eq_degree_iSup]
  exact SourceSupportTools.filtration_zero (tensorDegreeSpace_iSupIndep m B _ n)
    (sourceCoordinate m B p n) sourceDegree sourceDegree_pos
    (sourceCoordinate_shift m B p b n) _ (source_highest_mem_zero m B b v hv n)
    (sourceCoordinate_kernel m B hU p b v hv n)

/-- There is no negative-deficit part of the actual source tensor. -/
theorem source_tensorFiltration_neg_one (m : ℕ)
    (B : ZMod (2*m+1) → AlgebraicFactor F)
    (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    (p : ∀i, RootExpansion (basicFactor m B i).action)
    (b : ℕ → BasicWeight) (v : ∀i, (basicFactor m B i).Space)
    (hv : ∀i, (basicFactor m B i).IsBasicHighestWeightVector (b i) (v i)) (n : ℕ) :
    tensorFiltration m B (sourceTensorWeights b) n (-1) = ⊥ := by
  rw [tensorFiltration_eq_degree_iSup]
  apply bot_unique
  apply iSup_le
  intro k
  apply iSup_le
  intro hk
  rw [SourceSupportTools.negative_eq_bot (tensorDegreeSpace_iSupIndep m B _ n)
    (sourceCoordinate m B p n) sourceDegree sourceDegree_pos
    (sourceCoordinate_shift m B p b n)
    (fun x hx => source_highest_mem_zero m B b v hv n
      ((sourceCoordinate_kernel m B hU p b v hv n x).mp hx)) (by omega : k < 0)]

/-- Finite-dimensional weight spanning supplies a natural top layer. -/
theorem source_tensorFiltration_exists_top (m : ℕ)
    (B : ZMod (2*m+1) → AlgebraicFactor F)
    (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    (p : ∀i, RootExpansion (basicFactor m B i).action)
    (b : ℕ → BasicWeight) (v : ∀i, (basicFactor m B i).Space)
    (hv : ∀i, (basicFactor m B i).IsBasicHighestWeightVector (b i) (v i)) (n : ℕ) :
    ∃ N : ℕ, tensorFiltration m B (sourceTensorWeights b) n N = ⊤ := by
  have h := SourceSupportTools.filtration_exists_top (tensorDegreeSpace_iSupIndep m B _ n)
    (tensorDegreeSpace_iSup_eq_top m B (sourceTensorWeights b)
      (fun i => BasicSpaces.corootWeightSpace_iSup_eq_top hU (p i) (hv i)) n)
  simpa only [SourceSupportTools.filtration, ← tensorFiltration_eq_degree_iSup] using h

/-- If every actual positive short-root coordinate lowers one additional
layer, the vector was already in the next lower source layer. -/
theorem source_tensorFiltration_primitive (m : ℕ)
    (B : ZMod (2*m+1) → AlgebraicFactor F)
    (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    (p : ∀i, RootExpansion (basicFactor m B i).action)
    (b : ℕ → BasicWeight) (v : ∀i, (basicFactor m B i).Space)
    (hv : ∀i, (basicFactor m B i).IsBasicHighestWeightVector (b i) (v i))
    (n : ℕ) (k : ℤ) (hk : 0 < k) (x : basicTensorSpace m B n)
    (hx : x ∈ tensorFiltration m B (sourceTensorWeights b) n k)
    (hpx : ∀i<n, ∀r : ShortPositiveRoot,
      coordinateMap m B n i ((p i).coeff r.val 1) x ∈
        tensorFiltration m B (sourceTensorWeights b) n (k-weightDegree (rootWeight r.val)-1)) :
    x ∈ tensorFiltration m B (sourceTensorWeights b) n (k-1) := by
  have he (j : ℤ) : SourceSupportTools.filtration
      (tensorDegreeSpace m B (sourceTensorWeights b) n) j =
      tensorFiltration m B (sourceTensorWeights b) n j :=
    (tensorFiltration_eq_degree_iSup m B _ n j).symm
  rw [← he] at hx ⊢
  apply SourceSupportTools.primitive_mod_lower (tensorDegreeSpace_iSupIndep m B _ n)
    (sourceCoordinate m B p n) sourceDegree (sourceCoordinate_shift m B p b n)
    (fun x hx => source_highest_mem_zero m B b v hv n
      ((sourceCoordinate_kernel m B hU p b v hv n x).mp hx)) k (by omega) x hx
  intro q
  rw [he]
  exact hpx q.1.val q.1.isLt q.2

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
