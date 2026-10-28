module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex.SylowCandidate
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex.AmbientNormalizer.FixedSpace
public import Theory.SpecificGroups.Janko4.Model.Cardinality.Cosets.FixedVector

/-!
# Ambient fixed-vector control for the prescribed J₄ two-subgroup

The eleven kernel words already have a unique nonzero common fixed vector.
Every normalizer of their containing subgroup `twoSubgroup` fixes that vector.
The two-group fixed-point congruence also proves that its concrete ambient
vector orbit, and hence the index of its vector stabilizer, is odd.

These results concern the actual 112-dimensional binary matrix carrier.
They do not identify the full vector stabilizer with `max1Subgroup`; in
particular, containment of the ambient normalizer in `max1Subgroup` and odd
relative index in that normalizer remain unproved.

Source motivation: GLS3 Table 5.3i in
`refs/KGroup/GLS3/Chapter5(sec3-).tex`. Matrix and local-word provenance is
recorded in `Cardinality.Subgroup`, `OddIndex.SylowCandidate`, and the
`FixedSpace` certificate. No ambient order or automorphism table is assumed.
-/

public section

namespace Janko4.OuterReduction.OddIndex
open Cardinality GeneratorCertificates

attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel

/-- Every vector fixed by the prescribed two-subgroup lies on the already
specified local fixed line. The computation uses its eleven kernel words. -/
theorem twoSubgroup_fixed_row_eq (v : CosetVector)
    (hv : ∀ g ∈ twoSubgroup, vectorRight v g = v) :
    v = v 0 • cosetBaseVector := by
  apply FixedSpaceCertificate.fixed_row_eq
  intro i
  have h := hv (twoGenerator (Sum.inl i)) (twoGenerator_mem _)
  change Matrix.vecMul v (KernelCount.representation matrixA_mul_self matrixB_pow_four
    (KernelCount.basis matrixA_mul_self matrixB_pow_four i)) = v at h
  rwa [KernelCount.representation_basis] at h

/-- The nonzero fixed vector is unique over the binary field. -/
theorem twoSubgroup_fixed_row_eq_of_ne_zero (v : CosetVector) (hn : v ≠ 0)
    (hv : ∀ g ∈ twoSubgroup, vectorRight v g = v) : v = cosetBaseVector := by
  have he := twoSubgroup_fixed_row_eq v hv
  have htwo : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases htwo (v 0) with h | h
  · rw [h, zero_smul] at he
    exact (hn he).elim
  · simpa only [h, one_smul] using he

/-- Ambient normalizers preserve the unique nonzero fixed vector. This gives
containment in the actual vector stabilizer, not yet in `max1Subgroup`. -/
theorem normalizer_le_cosetVectorStabilizer :
    Subgroup.normalizer (twoSubgroup : Set Model) ≤ cosetVectorStabilizer := by
  intro g hg
  have hbase : ∀ s ∈ twoSubgroup, vectorRight cosetBaseVector s = cosetBaseVector :=
    fun s hs => max1Subgroup_le_cosetVectorStabilizer matrixA_mul_self matrixB_pow_four
      (twoSubgroup_le hs)
  change vectorRight cosetBaseVector g = cosetBaseVector
  apply twoSubgroup_fixed_row_eq_of_ne_zero
  · intro hz
    have he := congrArg (fun v => vectorRight v g⁻¹) hz
    rw [← vectorRight_mul, mul_inv_cancel, vectorRight_one] at he
    exact cosetBaseVector_ne_zero (he.trans (Matrix.zero_vecMul _))
  · intro s hs
    have hconj : g * s * g⁻¹ ∈ twoSubgroup :=
      (Subgroup.mem_normalizer_iff.mp hg s).mp hs
    calc
      vectorRight (vectorRight cosetBaseVector g) s =
          vectorRight (vectorRight cosetBaseVector (g * s * g⁻¹)) g := by
        simp only [← vectorRight_mul, inv_mul_cancel_right]
      _ = vectorRight cosetBaseVector g := by rw [hbase _ hconj]

attribute [local irreducible] cosetBaseVector

private def baseOrbitPoint : CosetVectorOrbit :=
  ⟨cosetBaseVector, 1, cosetOrbitMap_one⟩

private noncomputable instance vectorOrbitAction : MulAction Model CosetVectorOrbit where
  smul g v := ⟨vectorRight v.val g⁻¹, by
    change ∃ h, cosetOrbitMap h = vectorRight v.val g⁻¹
    have hv : ∃ h, cosetOrbitMap h = v.val := v.property
    obtain ⟨h, hh⟩ := hv
    exact ⟨h * g⁻¹, (vectorRight_mul _ _ _).trans (congrArg (fun w => vectorRight w g⁻¹) hh)⟩⟩
  one_smul v := Subtype.ext (by
    change vectorRight v.val (1 : Model)⁻¹ = v.val
    simp only [inv_one, vectorRight_one])
  mul_smul g h v := Subtype.ext (by
    change vectorRight v.val (g * h)⁻¹ = vectorRight (vectorRight v.val h⁻¹) g⁻¹
    simp only [mul_inv_rev, vectorRight_mul])

private theorem orbitPoint_ne_zero (v : CosetVectorOrbit) : (v : CosetVector) ≠ 0 := by
  obtain ⟨g, hg⟩ := v.property
  intro hz
  have he := congrArg (fun w => vectorRight w g⁻¹) (hg.trans hz)
  change vectorRight (vectorRight cosetBaseVector g) g⁻¹ = vectorRight 0 g⁻¹ at he
  rw [← vectorRight_mul, mul_inv_cancel, vectorRight_one] at he
  exact cosetBaseVector_ne_zero (he.trans (Matrix.zero_vecMul _))

/-- The concrete vector orbit has odd size. This counts fixed points of the
certified two-subgroup, without enumerating the orbit. -/
theorem cosetVectorOrbit_odd_card : ¬2 ∣ Nat.card CosetVectorOrbit := by
  let : MulAction twoSubgroup CosetVectorOrbit :=
    MulAction.compHom CosetVectorOrbit twoSubgroup.subtype
  have hbase : baseOrbitPoint ∈ MulAction.fixedPoints twoSubgroup CosetVectorOrbit := by
    intro s
    apply Subtype.ext
    exact max1Subgroup_le_cosetVectorStabilizer matrixA_mul_self matrixB_pow_four
      (twoSubgroup_le (twoSubgroup.inv_mem s.property))
  have hunique : ∀ v ∈ MulAction.fixedPoints twoSubgroup CosetVectorOrbit,
      v = baseOrbitPoint := by
    intro v hv
    apply Subtype.ext
    apply twoSubgroup_fixed_row_eq_of_ne_zero _ (orbitPoint_ne_zero v)
    intro s hs
    have he := congrArg Subtype.val (hv (⟨s⁻¹, twoSubgroup.inv_mem hs⟩ : twoSubgroup))
    change vectorRight (v : CosetVector) (s⁻¹)⁻¹ = (v : CosetVector) at he
    simpa only [inv_inv] using he
  have hc : Nat.card (MulAction.fixedPoints twoSubgroup CosetVectorOrbit) = 1 := by
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨baseOrbitPoint, hbase⟩, ?_⟩
    intro v
    exact Subtype.ext (hunique v.val v.property)
  have hm := twoSubgroup_isPGroup.card_modEq_card_fixedPoints CosetVectorOrbit
  rw [hc] at hm
  exact fun hd => (by decide : ¬2 ∣ 1) ((hm.dvd_iff dvd_rfl).mp hd)

private instance vectorOrbitPretransitive : MulAction.IsPretransitive Model CosetVectorOrbit where
  exists_smul_eq v w := by
    obtain ⟨g, hg⟩ := v.property
    obtain ⟨h, hh⟩ := w.property
    refine ⟨h⁻¹ * g, Subtype.ext ?_⟩
    change vectorRight v.val (h⁻¹ * g)⁻¹ = w.val
    rw [mul_inv_rev, inv_inv, ← hg]
    change vectorRight (vectorRight cosetBaseVector g) (g⁻¹ * h) = w.val
    rw [← vectorRight_mul, mul_inv_cancel_left]
    exact hh

/-- The actual vector stabilizer has odd ambient index. Its identification
with the ATLAS word subgroup is a separate obligation. -/
theorem cosetVectorStabilizer_odd_index : ¬2 ∣ cosetVectorStabilizer.index := by
  have he : MulAction.stabilizer Model baseOrbitPoint = cosetVectorStabilizer := by
    ext g
    change (g • baseOrbitPoint = baseOrbitPoint) ↔ g ∈ cosetVectorStabilizer
    rw [Subtype.ext_iff]
    change g⁻¹ ∈ cosetVectorStabilizer ↔ g ∈ cosetVectorStabilizer
    exact cosetVectorStabilizer.inv_mem_iff
  rw [← he, MulAction.index_stabilizer_of_transitive]
  exact cosetVectorOrbit_odd_card

end Janko4.OuterReduction.OddIndex
