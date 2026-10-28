module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.KernelModel
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Counting
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Dynamics.Transvections
public import Theory.Representation.MathieuCodeRestriction.Duality

/-!
# The genuine octad sign action by transvections

The shortened Golay code pairs perfectly with the native cocode modulo its
six-dimensional octad pair space. The complementary-sixteen word corresponds
to the octad parity functional. Transposing the already proved native
transvection formula therefore gives the actual sign action, with all
displacements in the complementary line. Perfectness also proves faithfulness.
Transitivity on the sixteen complementary points identifies the fixed words
as zero and the complementary word.

Source: Aschbacher, *Sporadic Groups* (1994), 25.1(1)–(3), pp.132–133.
The native cocode calculation is the existing H.15.2 development; the actual
native/ATLAS coordinate comparison is retained throughout. The underlying
Golay ports are attributed in `LICENSES/ATLAS.txt` and
`LICENSES/ATLAS-CITATION.cff`.
-/

open Atlas.Conway Atlas.Codes Atlas.Lattices
open MathieuCode.CocodeOctad.Dynamics
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
namespace KernelModel
@[expose] public noncomputable section

private lemma binary_add_self {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 by decide, zero_smul]

def complementWord : signCode :=
  ⟨⟨allOnes, C0_le_golay allOnes_mem_C0⟩ + golayBasis 0, by
    intro i
    change 1 + (golayBasis 0).val i.val = 0
    rcases bit_cases ((golayBasis 0).val i.val) with h | h
    · exact False.elim (i.prop h)
    · rw [h]; exact CharTwo.add_self_eq_zero _⟩

lemma complementWord_apply (i : Omega) :
    complementWord.val.val i = 1 + (golayBasis 0).val i := rfl

lemma complementWord_ne_zero : complementWord ≠ 0 := by
  intro he
  have hi := congrArg (fun c : signCode => c.val.val ((0,0),0)) he
  change 1 + (golayBasis 0).val ((0,0),0) = 0 at hi
  have hzero : (golayBasis 0).val ((0,0),0) = 0 := by
    rw [golayBasis_coe]; decide +kernel
  rw [hzero, add_zero] at hi
  exact one_ne_zero hi

lemma signCodeEquiv_complementWord (g : pointwise) :
    signCodeEquiv g complementWord = complementWord := by
  apply Subtype.ext; apply Subtype.ext; funext i
  change 1 + (golayBasis 0).val (g.val.val.symm i) = 1 + (golayBasis 0).val i
  rw [pointwise_word]

lemma pointwise_sq (g : pointwise) : g ^ 2 = 1 := by
  apply nativeEquiv.symm.injective
  apply (octadTransvectionEquiv nativeOctad).injective
  simp only [map_pow, map_one]
  apply Multiplicative.toAdd.injective
  rw [pow_two]
  change _ + _ = (0 : Axis nativeOctad)
  exact binary_add_self _

lemma pointwise_mul_comm (g h : pointwise) : g * h = h * g := by
  apply nativeEquiv.symm.injective
  apply (octadTransvectionEquiv nativeOctad).injective
  simp only [map_mul]
  exact mul_comm _ _

lemma complement_transitive (i j : Omega)
    (hi : (golayBasis 0).val i = 0) (hj : (golayBasis 0).val j = 0) :
    ∃ g : pointwise, g.val.val i = j := by
  obtain ⟨g, hg⟩ := MathieuCode.octad_kernel_transitive nativeOctad
    (MathieuCode.atlasPointEquiv i) (MathieuCode.atlasPointEquiv j)
    (by simp only [nativeOctad_support, Equiv.symm_apply_apply, hi, ne_eq, not_true_eq_false, not_false_eq_true])
    (by simp only [nativeOctad_support, Equiv.symm_apply_apply, hj, ne_eq, not_true_eq_false, not_false_eq_true])
  refine ⟨nativeEquiv g, ?_⟩
  change MathieuCode.atlasPointEquiv.symm (g.val.val (MathieuCode.atlasPointEquiv i)) = j
  change g.val.val (MathieuCode.atlasPointEquiv i) = MathieuCode.atlasPointEquiv j at hg
  rw [hg, Equiv.symm_apply_apply]

lemma signCode_fixed_iff (c : signCode) :
    (∀ g : pointwise, signCodeEquiv g c = c) ↔ c = 0 ∨ c = complementWord := by
  constructor
  · intro hc
    let j : Omega := ((0,0),0)
    have hj : (golayBasis 0).val j = 0 := by rw [golayBasis_coe]; decide +kernel
    have hconst (i : Omega) (hi : (golayBasis 0).val i = 0) : c.val.val i = c.val.val j := by
      obtain ⟨g, hg⟩ := complement_transitive i j hi hj
      have he := congrArg (fun d : signCode => d.val.val j) (hc g)
      change c.val.val (g.val.val.symm j) = c.val.val j at he
      rw [← hg, Equiv.symm_apply_apply, hg] at he
      exact he
    rcases bit_cases (c.val.val j) with hz | ho
    · left
      apply Subtype.ext; apply Subtype.ext; funext i
      by_cases hi : (golayBasis 0).val i = 0
      · exact (hconst i hi).trans hz
      · exact c.prop ⟨i, hi⟩
    · right
      apply Subtype.ext; apply Subtype.ext; funext i
      by_cases hi : (golayBasis 0).val i = 0
      · rw [complementWord_apply, hi, add_zero]
        exact (hconst i hi).trans ho
      · exact (c.prop ⟨i, hi⟩).trans (complementWord.prop ⟨i, hi⟩).symm
  · rintro (rfl | rfl) g
    · exact map_zero _
    · exact signCodeEquiv_complementWord g

open MathieuCode.CocodeOctad
open scoped BigOperators

lemma signCode_add_self (c : signCode) : c + c = 0 := binary_add_self c

/-- The shortened ATLAS words in the native Golay quotient. -/
def nativeCode : signCode →ₗ[Bit] MathieuCode.Code :=
  MathieuCode.codeLine.mkQ.comp (MathieuCode.atlasGolayEquiv.toLinearMap.comp signCode.subtype)

lemma nativeWord_vanishes (c : signCode) (i : Fin 24) (hi : i ∈ nativeOctad.val) :
    (MathieuCode.atlasGolayEquiv c.val).val i = 0 :=
  c.prop ⟨_, (nativeOctad_support i).mp hi⟩

lemma nativeCode_injective : Function.Injective nativeCode := by
  apply (LinearMap.ker_eq_bot).mp
  apply bot_unique
  intro c hc
  have hm : MathieuCode.atlasGolayEquiv c.val ∈ MathieuCode.codeLine :=
    (Submodule.Quotient.mk_eq_zero _).mp hc
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hm
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < nativeOctad.val.card by
    rw [Sporadic.Mathieu.m24Blocks_card _ nativeOctad.prop]; decide)
  have hbi := congrFun hb i
  change b * 1 = (MathieuCode.atlasGolayEquiv c.val).val i at hbi
  rw [mul_one, nativeWord_vanishes c i hi] at hbi
  rw [hbi, zero_smul] at hb
  apply Subtype.ext
  apply MathieuCode.atlasGolayEquiv.injective
  exact Subtype.ext hb.symm

lemma nativeCode_action (g : pointwise) (c : signCode) :
    nativeCode (signCodeEquiv g c) =
      MathieuCode.codeRepresentation (nativeEquiv.symm g).val (nativeCode c) := by
  obtain ⟨g, rfl⟩ := nativeEquiv.surjective g
  rw [MulEquiv.symm_apply_apply]
  apply congrArg MathieuCode.codeLine.mkQ
  apply Subtype.ext
  exact MathieuCode.atlasWordEquiv_permute g.val.val c.val.val

abbrev CocodeQuotient := MathieuCode.Cocode ⧸ octadPairSpace nativeOctad

def signPairing : signCode →ₗ[Bit] Module.Dual Bit MathieuCode.Cocode :=
  MathieuCode.codeCocodePairing.comp nativeCode

lemma signPairing_annihilates (c : signCode) :
    octadPairSpace nativeOctad ≤ (signPairing c).ker := by
  apply Submodule.span_le.mpr
  rintro v ⟨P, hP, rfl⟩
  change MathieuCode.dotForm (MathieuCode.atlasGolayEquiv c.val).val
    (MathieuCode.wordOfSet P.val) = 0
  change (∑ i : Fin 24, (MathieuCode.atlasGolayEquiv c.val).val i *
    MathieuCode.wordOfSet P.val i) = 0
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i ∈ P.val
  · rw [nativeWord_vanishes c i (hP hi), zero_mul]
  · simp [MathieuCode.wordOfSet, hi]

/-- Perfect pairing with the five-dimensional native cocode quotient. -/
def signDual : signCode →ₗ[Bit] Module.Dual Bit CocodeQuotient where
  toFun c := (octadPairSpace nativeOctad).liftQ (signPairing c) (signPairing_annihilates c)
  map_add' c d := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := (octadPairSpace nativeOctad).mkQ_surjective x
    exact LinearMap.congr_fun (map_add signPairing c d) v
  map_smul' b c := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := (octadPairSpace nativeOctad).mkQ_surjective x
    exact LinearMap.congr_fun (map_smul signPairing b c) v

lemma signDual_mk (c : signCode) (v : MathieuCode.Cocode) :
    signDual c ((octadPairSpace nativeOctad).mkQ v) = signPairing c v := rfl

lemma signDual_injective : Function.Injective signDual := by
  apply (LinearMap.ker_eq_bot).mp
  apply bot_unique
  intro c hc
  apply nativeCode_injective
  rw [map_zero]
  apply MathieuCode.codeCocodePairing_left_nondegenerate
  intro v
  exact LinearMap.congr_fun hc ((octadPairSpace nativeOctad).mkQ v)

lemma signDual_surjective : Function.Surjective signDual := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp signDual_injective
  rw [Subspace.dual_finrank_eq, signCode_finrank]
  have h := (octadPairSpace nativeOctad).finrank_quotient_add_finrank
  rw [finrank_supportedPairSpace, MathieuCode.finrank_cocode] at h
  change Module.finrank Bit CocodeQuotient + 6 = 11 at h
  omega

lemma signDual_action (g : pointwise) (c : signCode) (x : CocodeQuotient) :
    signDual (signCodeEquiv g c) x =
      signDual c (quotientRepresentation nativeOctad
        ⟨(nativeEquiv.symm g).val⁻¹, kernel_le_stabilizer _
          ((MathieuCode.octadPointwiseKernel nativeOctad).inv_mem (nativeEquiv.symm g).prop)⟩ x) := by
  obtain ⟨v, rfl⟩ := (octadPairSpace nativeOctad).mkQ_surjective x
  rw [quotientRepresentation_mk, signDual_mk, signDual_mk]
  change MathieuCode.codeCocodePairing (nativeCode (signCodeEquiv g c)) v = _
  rw [nativeCode_action]
  have h := MathieuCode.codeCocodePairing_invariant (nativeEquiv.symm g).val
    (nativeCode c) (MathieuCode.cocodeRepresentation (nativeEquiv.symm g).val⁻¹ v)
  rw [action_inv'] at h
  exact h

lemma nativeCode_complementWord : nativeCode complementWord = MathieuCode.octadVector nativeOctad := by
  have he : MathieuCode.atlasGolayEquiv complementWord.val =
      (⟨BinaryPermutation.allOne (Fin 24), MathieuCode.allOne_mem⟩ : MathieuCode.golay) +
        ⟨MathieuCode.wordOfSet nativeOctad.val, octad_word_mem nativeOctad⟩ := by
    apply Subtype.ext
    funext i
    change 1 + (golayBasis 0).val (MathieuCode.atlasPointEquiv.symm i) =
      1 + MathieuCode.wordOfSet nativeOctad.val i
    congr 1
    rcases bit_cases ((golayBasis 0).val (MathieuCode.atlasPointEquiv.symm i)) with h | h <;>
      simp [MathieuCode.wordOfSet, nativeOctad_support, h]
  change MathieuCode.codeLine.mkQ (MathieuCode.atlasGolayEquiv complementWord.val) = _
  rw [he, map_add]
  have hz : MathieuCode.codeLine.mkQ
      ⟨BinaryPermutation.allOne (Fin 24), MathieuCode.allOne_mem⟩ = 0 := by
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.subset_span (Set.mem_singleton _)
  rw [hz, zero_add]
  rfl

lemma signDual_complementWord : signDual complementWord = quotientOctadParity nativeOctad := by
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := (octadPairSpace nativeOctad).mkQ_surjective x
  rw [signDual_mk, quotientOctadParity_mkQ]
  change MathieuCode.codeCocodePairing (nativeCode complementWord) v = _
  rw [nativeCode_complementWord]
  obtain ⟨w, rfl⟩ := MathieuCode.codeInCore.mkQ_surjective v
  rfl

/-- The actual pointwise octad fixers act by transvections with the complementary sign as center. -/
lemma signCodeEquiv_transvection (g : pointwise) (c : signCode) :
    signCodeEquiv g c = c +
      signDual c (octadTransvectionEquiv nativeOctad ((nativeEquiv.symm g)⁻¹)).toAdd.val •
        complementWord := by
  apply signDual_injective
  apply LinearMap.ext
  intro x
  rw [signDual_action]
  change signDual c (quotientRepresentation nativeOctad
    ⟨((nativeEquiv.symm g)⁻¹).val, kernel_le_stabilizer _ ((nativeEquiv.symm g)⁻¹).prop⟩ x) = _
  simp only [octadTransvectionEquiv_action_quotient, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, signDual_complementWord, smul_eq_mul]
  rw [mul_comm]

lemma signCodeEquiv_faithful (g : pointwise)
    (hg : ∀ c : signCode, signCodeEquiv g c = c) : g = 1 := by
  let d := (octadTransvectionEquiv nativeOctad ((nativeEquiv.symm g)⁻¹)).toAdd.val
  have hd (c : signCode) : signDual c d = 0 := by
    have h := signCodeEquiv_transvection g c
    rw [hg c] at h
    have hz : signDual c d • complementWord = 0 := (add_eq_left.mp h.symm)
    exact (smul_eq_zero.mp hz).resolve_right complementWord_ne_zero
  have hd0 : d = 0 := by
    apply (Module.eval_apply_injective Bit (V := CocodeQuotient))
    apply LinearMap.ext
    intro f
    change f d = f 0
    rw [map_zero]
    obtain ⟨c, rfl⟩ := signDual_surjective f
    exact hd c
  have he : (octadTransvectionEquiv nativeOctad) ((nativeEquiv.symm g)⁻¹) = 1 := by
    apply Multiplicative.toAdd.injective
    exact Subtype.ext hd0
  have hi : (nativeEquiv.symm g)⁻¹ = 1 :=
    (octadTransvectionEquiv nativeOctad).injective (he.trans (map_one _).symm)
  exact nativeEquiv.symm.injective ((inv_eq_one.mp hi).trans (map_one _).symm)

end
end KernelModel
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
