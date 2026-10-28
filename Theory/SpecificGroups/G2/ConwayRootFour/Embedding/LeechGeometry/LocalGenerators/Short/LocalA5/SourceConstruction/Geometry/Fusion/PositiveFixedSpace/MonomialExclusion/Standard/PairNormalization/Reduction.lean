module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.Reference

/-!
# Structural reduction of standard quaternion-pair normalization

A fixed-point-free involution on four rows is a nonzero translation of the
Kleinian alphabet. Applying this to every standard tetrad and using the actual
Golay preservation criterion puts both coordinate pullbacks in the hexacode.
The third negative-square relation makes their values distinct in every column.

An actual hexacode monomial automorphism lifts to the Golay monomial group.
The coordinate conjugation formula and the Golay sign coboundary formula then
separate normalization into two finite orbit calculations. Equality of their
matrix kernels is proved equivalent to equality in the literal quotient Λ/2Λ.
The two orbit contracts at the end remain unproved premises; the sign contract
is consumed by `reference_pair_of_signOrbit`, and both are consumed by the
parent normalization assembly.

Source context: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284,
and the root-four conventions on p.269. The alphabet, encoder and Golay actions
are the existing attributed ATLAS models; no further source is copied here.
-/

open Atlas.Conway Atlas.Codes Atlas.Lattices
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.PairNormalization

private theorem row_involution_translation
    (p : Fin 4 → Fin 4) (hs : ∀ k, p (p k) = k) (hn : ∀ k, p k ≠ k) :
      ∀ k, rowLabel (p k) = rowLabel k + rowLabel (p 0) := by
  have h : ∀ a b c d : Fin 4,
      (∀ k, (![a,b,c,d] : Fin 4 → Fin 4) (![a,b,c,d] k) = k) →
      (∀ k, (![a,b,c,d] : Fin 4 → Fin 4) k ≠ k) →
      ∀ k, rowLabel (![a,b,c,d] k) = rowLabel k + rowLabel a := by decide
  have he : p = ![p 0,p 1,p 2,p 3] := by funext k; fin_cases k <;> rfl
  simpa only [← he] using h (p 0) (p 1) (p 2) (p 3) (by rwa [← he]) (by rwa [← he])

theorem column_involution_translation (p : Equiv.Perm Omega)
    (hp : ∀ i, (p i).1 = i.1) (hs : Function.Involutive p)
    (hn : ∀ i, p i ≠ i) :
    ∀ i, p i = (i.1, rowLabel.symm
      (rowLabel i.2 + rowLabel (p (i.1, 0)).2)) := by
  rintro ⟨j,k⟩
  have hs' (l : Fin 4) : (p (j, (p (j,l)).2)).2 = l := by
    have h := congrArg Prod.snd (hs (j,l))
    have he : p (j,l) = (j,(p (j,l)).2) := Prod.ext (hp (j,l)) rfl
    rwa [he] at h
  have hn' (l : Fin 4) : (p (j,l)).2 ≠ l := by
    intro he
    exact hn (j,l) (Prod.ext (hp (j,l)) he)
  refine Prod.ext (hp (j,k)) ?_
  apply rowLabel.injective
  rw [rowLabel.apply_symm_apply]
  exact row_involution_translation (fun l => (p (j,l)).2) hs' hn' k

theorem column_golay_involution_translation (g : Mathieu24CodeModel)
    (hp : ∀ i, (g.val i).1 = i.1) (hs : Function.Involutive g.val)
    (hn : ∀ i, g.val i ≠ i) :
    ∃ t : hexacode, (∀ j, t.val j ≠ 0) ∧
      ∀ i, g.val i = (i.1, rowLabel.symm (rowLabel i.2 + t.val i.1)) := by
  let t : HexWord := fun j => rowLabel (g.val (j,0)).2
  have ht := column_involution_translation g.val hp hs hn
  have he : affinePermutation t 1 = g.val := by
    apply Equiv.ext
    intro i
    exact (ht i).symm
  have hc : CodePreserving (affinePermutation t 1) := he.symm ▸ g.prop
  refine ⟨⟨t,(affine_preservation_necessary t 1 hc).1⟩, ?_, ht⟩
  intro j hz
  change t j = 0 at hz
  have hh := ht (j,0)
  change g.val (j,0) = (j,rowLabel.symm (rowLabel 0 + t j)) at hh
  rw [hz, add_zero, rowLabel.symm_apply_apply] at hh
  exact hn (j,0) hh

theorem standard_pair_translations (a b : GolayMonomialGroup)
    (hstd : quaternionParts a b = distinguishedUnorderedSextet.val)
    (ha : (monomialEmbedding a) ^ 2 = negationIsometry)
    (hb : (monomialEmbedding b) ^ 2 = negationIsometry)
    (hab : (monomialEmbedding a * monomialEmbedding b) ^ 2 = negationIsometry) :
    ∃ h k : hexacode, (∀ j, h.val j ≠ 0) ∧ (∀ j, k.val j ≠ 0) ∧
      (∀ j, h.val j ≠ k.val j) ∧
      monomialPull a = affinePermutation h.val 1 ∧
      monomialPull b = affinePermutation k.val 1 := by
  obtain ⟨hpa,hpb,_,hna,hnb,hnab⟩ := monomial_quaternion_parameters a b ha hb hab
  have hcol := standard_quaternion_coordinate_columns a b hstd
  obtain ⟨h,hh,hap⟩ := column_golay_involution_translation a.right⁻¹
    (fun i => (hcol i).1) hpa hna
  obtain ⟨k,hk,hbp⟩ := column_golay_involution_translation b.right⁻¹
    (fun i => (hcol i).2) hpb hnb
  have hap' : monomialPull a = affinePermutation h.val 1 := Equiv.ext hap
  have hbp' : monomialPull b = affinePermutation k.val 1 := Equiv.ext hbp
  refine ⟨h,k,hh,hk,?_,hap',hbp'⟩
  intro j hj
  apply hnab (j,0)
  rw [hap',hbp']
  change (j,rowLabel.symm (rowLabel (rowLabel.symm (rowLabel 0 + k.val j)) +
    h.val j)) = (j,0)
  rw [rowLabel.apply_symm_apply,hj,add_assoc,letter_self_add,add_zero,
    rowLabel.symm_apply_apply]

theorem affine_linear_conjugate_translation (g : HexAutomorphisms) (h : HexWord)
    (i : Omega) :
    affinePermutation 0 g.val
      (affinePermutation h 1 ((affinePermutation 0 g.val).symm i)) =
      affinePermutation (Monomial.act g.val h) 1 i := by
  simp [affinePermutation, Monomial.act_apply, map_add]

def hexMonomialLift (g : HexAutomorphisms) : GolayMonomialGroup :=
  SemidirectProduct.inr
    ⟨affinePermutation 0 g.val,affine_preserves_code 0 g.val hexacode.zero_mem g.prop⟩

theorem pull_conjugate_hexMonomialLift (g : HexAutomorphisms) (a : GolayMonomialGroup)
    (h : HexWord) (ha : monomialPull a = affinePermutation h 1) (i : Omega) :
    monomialPull (hexMonomialLift g * a * (hexMonomialLift g)⁻¹) i =
      affinePermutation (Monomial.act g.val h) 1 i := by
  change affinePermutation 0 g.val
    (monomialPull a ((affinePermutation 0 g.val).symm i)) = _
  rw [ha]
  exact affine_linear_conjugate_translation g h i

def signLift (c : golay) : GolayMonomialGroup :=
  SemidirectProduct.inl (Multiplicative.ofAdd c)

theorem sign_conjugate_left (c : golay) (a : GolayMonomialGroup) (i : Omega) :
    (signLift c * a * (signLift c)⁻¹).left.toAdd.val i =
      a.left.toAdd.val i + c.val i + c.val (monomialPull a i) := by
  change c.val i + a.left.toAdd.val i + -c.val (monomialPull a i) = _
  have hn (x : Bit) : -x = x := by revert x; decide
  rw [hn, add_comm (c.val i)]

theorem sign_conjugate_pull (c : golay) (a : GolayMonomialGroup) (i : Omega) :
    monomialPull (signLift c * a * (signLift c)⁻¹) i = monomialPull a i := rfl

theorem same_binaryFixed_iff_kernel_eq (a b : GolayMonomialGroup) :
    binaryFixed (monomialEmbedding a) = binaryFixed (monomialEmbedding b) ↔
      LinearMap.ker (Matrix.mulVecLin (StandardCoordinates.monomialMatrix a) - LinearMap.id) =
      LinearMap.ker (Matrix.mulVecLin (StandardCoordinates.monomialMatrix b) - LinearMap.id) := by
  constructor
  · intro h
    ext v
    obtain ⟨w,rfl⟩ := StandardCoordinates.binaryCoordinates.surjective v
    rw [StandardCoordinates.binaryCoordinates_mem_kernel,
      StandardCoordinates.binaryCoordinates_mem_kernel,h]
  · intro h
    ext v
    rw [← StandardCoordinates.binaryCoordinates_mem_kernel,
      ← StandardCoordinates.binaryCoordinates_mem_kernel,h]

/-- The finite ordered-pair orbit in the hexacode. Its conclusion is an actual
hexacode monomial automorphism, which has the Golay lift proved above. -/
def TranslationPairOrbit : Prop :=
  ∀ h k : hexacode, (∀ j, h.val j ≠ 0) → (∀ j, k.val j ≠ 0) →
    (∀ j, h.val j ≠ k.val j) → ∃ g : HexAutomorphisms,
      Monomial.act g.val h.val = referenceHexA ∧
      Monomial.act g.val k.val = referenceHexB

/-- The remaining sign calculation for the reference coordinate permutations.
The kernel equation uses the proven matrices of the literal quotient Λ/2Λ.
The witness is a Golay word, so the two displayed coboundaries give an actual
simultaneous sign conjugator. -/
def ReferenceSignOrbit : Prop :=
  ∀ a b : GolayMonomialGroup,
    (∀ i, monomialPull a i = referencePullA i) →
    (∀ i, monomialPull b i = referencePullB i) →
    (monomialEmbedding a) ^ 2 = negationIsometry →
    (monomialEmbedding b) ^ 2 = negationIsometry →
    (monomialEmbedding a * monomialEmbedding b) ^ 2 = negationIsometry →
    LinearMap.ker (Matrix.mulVecLin (StandardCoordinates.monomialMatrix a) - LinearMap.id) =
      LinearMap.ker (Matrix.mulVecLin (StandardCoordinates.monomialMatrix b) - LinearMap.id) →
    ∃ c : golay,
      (∀ i, a.left.toAdd.val i + c.val i + c.val (referencePullA i) =
        jWord referenceHexB i) ∧
      (∀ i, b.left.toAdd.val i + c.val i + c.val (referencePullB i) =
        jWord (referenceHexA + referenceHexB) i)

/-- Consumer of the sign calculation, including its literal lattice-kernel
premise and the action of its witness in the Golay semidirect product. -/
theorem reference_pair_of_signOrbit (H : ReferenceSignOrbit)
    (a b : GolayMonomialGroup)
    (hpa : ∀ i, monomialPull a i = referencePullA i)
    (hpb : ∀ i, monomialPull b i = referencePullB i)
    (ha : (monomialEmbedding a) ^ 2 = negationIsometry)
    (hb : (monomialEmbedding b) ^ 2 = negationIsometry)
    (hab : (monomialEmbedding a * monomialEmbedding b) ^ 2 = negationIsometry)
    (he : binaryFixed (monomialEmbedding a) = binaryFixed (monomialEmbedding b)) :
    ∃ c : golay, ReferenceQuaternionPair
      (signLift c * a * (signLift c)⁻¹) (signLift c * b * (signLift c)⁻¹) := by
  obtain ⟨c,hca,hcb⟩ := H a b hpa hpb ha hb hab ((same_binaryFixed_iff_kernel_eq a b).mp he)
  refine ⟨c,?_,?_,?_,?_⟩
  · funext i
    rw [sign_conjugate_left,hpa]
    exact hca i
  · funext i
    rw [sign_conjugate_left,hpb]
    exact hcb i
  · intro i
    rw [sign_conjugate_pull,hpa]
  · intro i
    rw [sign_conjugate_pull,hpb]

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.PairNormalization

