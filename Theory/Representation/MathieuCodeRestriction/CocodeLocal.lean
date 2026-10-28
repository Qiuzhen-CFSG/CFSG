module

public import Theory.Representation.MathieuCodeRestriction
public import Theory.AtlasPort.OtherSporadic.Codes.GolayMinimum
public import Theory.Mathieu.M24.Properties.Transitivity

/-!
# Weight-two orbits in the native Mathieu cocode

The minimum distance of the Golay code, transported through the proved
coordinate equivalence, makes the classes of distinct two-element subsets
distinct and nonzero. Native double transitivity gives the 276-element M24
orbit. The 23 pairs through the distinguished fixed point form the M23
orbit. Equivariance identifies their vector stabilizers with actual pair
and point stabilizers; in M23 this gives an isomorphism with the native M22.

The support subspaces at the end are geometric inputs for the local flags;
no local fixed-space dimension, transvection action or residual action is
assumed. The minimum-distance theorem is reused from the licensed ATLAS
port `Theory.AtlasPort.OtherSporadic.Codes.GolayMinimum`; attribution and
license are recorded there and in `LICENSES/ATLAS.txt`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
H.15.1(1) and the preceding discussion, printed p.398.
-/

@[expose] public section

open Sporadic.Mathieu
open scoped BigOperators Pointwise
namespace MathieuCode
noncomputable section

lemma hammingNorm_atlasWordEquiv (w : Atlas.Codes.BinaryWord) :
    hammingNorm (atlasWordEquiv w) = hammingNorm w := by
  simp only [Atlas.Codes.hammingNorm_eq_sum, atlasWordEquiv_apply]
  exact Equiv.sum_comp atlasPointEquiv.symm (fun i => if w i = 0 then 0 else 1)

lemma native_golay_minimum {w : Full} (hw : w ∈ golay) (hw0 : w ≠ 0) :
    8 ≤ hammingNorm w := by
  have hc : atlasWordEquiv.symm w ∈ Atlas.Codes.golay := by
    apply (mem_atlas_golay_iff _).mpr
    simpa using hw
  have hn : atlasWordEquiv.symm w ≠ 0 := by
    intro h
    apply hw0
    simpa using congrArg atlasWordEquiv h
  simpa only [← hammingNorm_atlasWordEquiv, LinearEquiv.apply_symm_apply] using
    Atlas.Codes.golay_minimum _ hc hn

abbrev PointPair := {B : Finset (Fin 24) // B.card = 2}

lemma wordOfSet_mem_core (B : PointPair) : wordOfSet B.val ∈ Core := by
  change (∑ i : Fin 24, if i ∈ B.val then (1 : ZMod 2) else 0) = 0
  simp [B.property]

def pairVector (B : PointPair) : Cocode :=
  codeInCore.mkQ ⟨wordOfSet B.val, wordOfSet_mem_core B⟩

lemma wordOfSet_weight (B : Finset (Fin 24)) : hammingNorm (wordOfSet B) = B.card := by
  unfold hammingNorm
  congr 1
  ext i
  simp [wordOfSet]

lemma wordOfSet_sub_weight_le (B C : Finset (Fin 24)) :
    hammingNorm (wordOfSet B - wordOfSet C) ≤ B.card + C.card := by
  apply le_trans (Finset.card_le_card (t := B ∪ C) ?_) (Finset.card_union_le _ _)
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  by_contra hn
  simp only [Finset.mem_union, not_or] at hn
  simp [wordOfSet, hn.1, hn.2] at hi

lemma wordOfSet_injective : Function.Injective wordOfSet := by
  intro B C h
  ext i
  have he := congrFun h i
  by_cases hi : i ∈ B <;> by_cases hj : i ∈ C <;> simp_all [wordOfSet]

lemma pairVector_injective : Function.Injective pairVector := by
  intro B C h
  have hm : wordOfSet B.val - wordOfSet C.val ∈ golay := by
    have hq : codeInCore.mkQ
        (⟨wordOfSet B.val, wordOfSet_mem_core B⟩ -
          ⟨wordOfSet C.val, wordOfSet_mem_core C⟩ : Core) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr h
    exact (Submodule.Quotient.mk_eq_zero codeInCore).mp hq
  have hz : wordOfSet B.val - wordOfSet C.val = 0 := by
    by_contra hn
    have hl := native_golay_minimum hm hn
    have hu := wordOfSet_sub_weight_le B.val C.val
    rw [B.property, C.property] at hu
    omega
  exact Subtype.ext (wordOfSet_injective (sub_eq_zero.mp hz))

lemma pairVector_ne_zero (B : PointPair) : pairVector B ≠ 0 := by
  intro hz
  have hm : wordOfSet B.val ∈ golay :=
    (Submodule.Quotient.mk_eq_zero codeInCore).mp hz
  have hn : wordOfSet B.val ≠ 0 := by
    intro h
    have hw := wordOfSet_weight B.val
    rw [h, hammingNorm_zero, B.property] at hw
    omega
  have hl := native_golay_minimum hm hn
  rw [wordOfSet_weight, B.property] at hl
  omega

/-- The action on unordered pairs induced by the native M24 permutation. -/
def mapPair (g : M24) (B : PointPair) : PointPair :=
  ⟨g • B.val, by simpa using B.property⟩

lemma pairVector_equivariant (g : M24) (B : PointPair) :
    cocodeRepresentation g (pairVector B) = pairVector (mapPair g B) := by
  change codeInCore.mkQ (coreRepresentation g ⟨wordOfSet B.val, wordOfSet_mem_core B⟩) = _
  apply congrArg codeInCore.mkQ
  apply Subtype.ext
  exact permute_wordOfSet g.val B.val

lemma pairVector_fixed_iff (g : M24) (B : PointPair) :
    cocodeRepresentation g (pairVector B) = pairVector B ↔ g • B.val = B.val := by
  rw [pairVector_equivariant, pairVector_injective.eq_iff]
  exact Subtype.ext_iff

/-- The literal weight-two subset of the native cocode. -/
def weightTwoOrbit : Set Cocode := Set.range pairVector

lemma weightTwoOrbit_nonzero {v : Cocode} (hv : v ∈ weightTwoOrbit) : v ≠ 0 := by
  obtain ⟨B, rfl⟩ := hv
  exact pairVector_ne_zero B

lemma weightTwoOrbit_transitive (B C : PointPair) :
    ∃ g : M24, cocodeRepresentation g (pairVector B) = pairVector C := by
  obtain ⟨a, b, hab, hB⟩ := Finset.card_eq_two.mp B.property
  obtain ⟨c, d, hcd, hC⟩ := Finset.card_eq_two.mp C.property
  let := m24_isFivePretransitive
  have ht : MulAction.IsMultiplyPretransitive M24 (Fin 24) 2 :=
    MulAction.isMultiplyPretransitive_of_le (n := 5) (by decide) (by simp)
  obtain ⟨g, ha, hb⟩ := (MulAction.is_two_pretransitive_iff.mp ht) hab hcd
  refine ⟨g, ?_⟩
  rw [pairVector_equivariant]
  congr 1
  apply Subtype.ext
  change g • B.val = C.val
  simp [hB, hC, Finset.smul_finset_def, ha, hb]

lemma embeddedPoint_ne_zero (i : Fin 23) : m23PointEmbedding i ≠ (0 : Fin 24) :=
  (m23PointEquiv i).property

/-- The pairs containing the point fixed by the native M23. -/
def pointPair (i : Fin 23) : PointPair :=
  ⟨{0, m23PointEmbedding i}, by simp [Ne.symm (embeddedPoint_ne_zero i)]⟩

def m23PairVector (i : Fin 23) : Cocode := pairVector (pointPair i)

lemma pointPair_injective : Function.Injective pointPair := by
  intro i j h
  have he := congrArg Subtype.val h
  have hm : m23PointEmbedding i ∈ (pointPair i).val := by simp [pointPair]
  rw [he] at hm
  exact m23PointEmbedding.injective (by
    simpa [pointPair, embeddedPoint_ne_zero i] using hm)

lemma m23PairVector_injective : Function.Injective m23PairVector :=
  pairVector_injective.comp pointPair_injective

lemma m23PairVector_ne_zero (i : Fin 23) : m23PairVector i ≠ 0 :=
  pairVector_ne_zero _

lemma m23PairVector_equivariant (g : M23) (i : Fin 23) :
    m23CocodeRepresentation g (m23PairVector i) = m23PairVector (g • i) := by
  change cocodeRepresentation (pointEmbedding g) (pairVector (pointPair i)) = _
  rw [pairVector_equivariant]
  apply congrArg pairVector
  apply Subtype.ext
  change pointEmbedding g • {0, m23PointEmbedding i} = {0, m23PointEmbedding (g • i)}
  simp only [Finset.smul_finset_def, Finset.image_insert, Finset.image_singleton]
  have h0 : pointEmbedding g • (0 : Fin 24) = 0 := pointEmbedding_fixed g
  have hi : pointEmbedding g • m23PointEmbedding i = m23PointEmbedding (g • i) :=
    pointEmbedding_apply g i
  rw [h0, hi]

lemma m23PairVector_fixed_iff (g : M23) (i : Fin 23) :
    m23CocodeRepresentation g (m23PairVector i) = m23PairVector i ↔ g • i = i := by
  rw [m23PairVector_equivariant, m23PairVector_injective.eq_iff]

def m23WeightTwoOrbit : Set Cocode := Set.range m23PairVector

lemma m23WeightTwoOrbit_nonzero {v : Cocode} (hv : v ∈ m23WeightTwoOrbit) : v ≠ 0 := by
  obtain ⟨i, rfl⟩ := hv
  exact m23PairVector_ne_zero i

lemma m23WeightTwoOrbit_transitive (i j : Fin 23) :
    ∃ g : M23, m23CocodeRepresentation g (m23PairVector i) = m23PairVector j := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M23 i j
  exact ⟨g, (m23PairVector_equivariant g i).trans (congrArg m23PairVector hg)⟩

lemma m23WeightTwoOrbit_subset : m23WeightTwoOrbit ⊆ weightTwoOrbit := by
  rintro v ⟨i, rfl⟩
  exact ⟨pointPair i, rfl⟩

lemma wordOfSet_mem_core_of_even (B : Finset (Fin 24)) (hB : Even B.card) :
    wordOfSet B ∈ Core := by
  change (∑ i : Fin 24, if i ∈ B then (1 : ZMod 2) else 0) = 0
  simpa using hB.natCast_zmod_two

/-- The quotient class of any even subset of the native coordinate set. -/
def evenSetVector (B : Finset (Fin 24)) (hB : Even B.card) : Cocode :=
  codeInCore.mkQ ⟨wordOfSet B, wordOfSet_mem_core_of_even B hB⟩

/-- The geometric subspace generated by pairs inside a prescribed set. -/
def supportedPairSpace (B : Finset (Fin 24)) : Submodule (ZMod 2) Cocode :=
  Submodule.span (ZMod 2) {v | ∃ P : PointPair, P.val ⊆ B ∧ pairVector P = v}

lemma pairVector_mem_supportedPairSpace {B : Finset (Fin 24)}
    (P : PointPair) (hP : P.val ⊆ B) : pairVector P ∈ supportedPairSpace B :=
  Submodule.subset_span ⟨P, hP, rfl⟩

lemma supportedPairSpace_mono {B C : Finset (Fin 24)} (h : B ⊆ C) :
    supportedPairSpace B ≤ supportedPairSpace C := by
  apply Submodule.span_le.mpr
  rintro v ⟨P, hP, rfl⟩
  exact pairVector_mem_supportedPairSpace P (hP.trans h)

/-- The actual stabilizer of a vector in a cocode action. -/
def cocodeVectorStabilizer {G : Type*} [Group G]
    (ρ : Representation (ZMod 2) G Cocode) (v : Cocode) : Subgroup G where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    change ρ (g * h) v = v
    rw [map_mul, Module.End.mul_apply, hh, hg]
  inv_mem' {g} hg := by
    change ρ g⁻¹ v = v
    exact ρ.inv_apply_eq_iff.mpr hg.symm

lemma pairVector_stabilizer (B : PointPair) :
    cocodeVectorStabilizer cocodeRepresentation (pairVector B) =
      MulAction.stabilizer M24 B.val := by
  ext g
  exact pairVector_fixed_iff g B

lemma m23PairVector_stabilizer (i : Fin 23) :
    cocodeVectorStabilizer m23CocodeRepresentation (m23PairVector i) =
      MulAction.stabilizer M23 i := by
  ext g
  exact m23PairVector_fixed_iff g i

/-- H.15.1(1), M23: the stabilizer is genuinely isomorphic to the native M22. -/
lemma m23PairVector_stabilizer_equiv (i : Fin 23) :
    Nonempty (cocodeVectorStabilizer m23CocodeRepresentation (m23PairVector i) ≃* M22) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M23 (9 : Fin 23) i
  exact ⟨(MulEquiv.subgroupCongr (m23PairVector_stabilizer i)).trans
    ((MulAction.stabilizerEquivStabilizer hg.symm).symm.trans
      m23EquivM22PointStabilizer.symm)⟩

/-- The parametrized subset is exactly one orbit under the quotient action. -/
lemma weightTwoOrbit_eq (B : PointPair) :
    weightTwoOrbit = {v | ∃ g : M24, cocodeRepresentation g (pairVector B) = v} := by
  ext v
  constructor
  · rintro ⟨C, rfl⟩
    exact weightTwoOrbit_transitive B C
  · rintro ⟨g, rfl⟩
    exact ⟨mapPair g B, (pairVector_equivariant g B).symm⟩

lemma m23WeightTwoOrbit_eq (i : Fin 23) :
    m23WeightTwoOrbit = {v | ∃ g : M23, m23CocodeRepresentation g (m23PairVector i) = v} := by
  ext v
  constructor
  · rintro ⟨j, rfl⟩
    exact m23WeightTwoOrbit_transitive i j
  · rintro ⟨g, rfl⟩
    exact ⟨g • i, (m23PairVector_equivariant g i).symm⟩

lemma card_weightTwoOrbit : Nat.card weightTwoOrbit = 276 := by
  change Nat.card (Set.range pairVector) = 276
  rw [← Nat.card_congr (Equiv.ofInjective pairVector pairVector_injective),
    Nat.card_eq_fintype_card, Fintype.card_finset_len]
  decide

lemma card_m23WeightTwoOrbit : Nat.card m23WeightTwoOrbit = 23 := by
  change Nat.card (Set.range m23PairVector) = 23
  rw [← Nat.card_congr (Equiv.ofInjective m23PairVector m23PairVector_injective)]
  simp

lemma m23WeightTwoOrbit_stabilizer_equiv {v : Cocode} (hv : v ∈ m23WeightTwoOrbit) :
    Nonempty (cocodeVectorStabilizer m23CocodeRepresentation v ≃* M22) := by
  obtain ⟨i, rfl⟩ := hv
  exact m23PairVector_stabilizer_equiv i

end
end MathieuCode
