module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.PairResidual.Displacement
public import Theory.Mathieu.M22.Properties.AutomorphismCoverage

/-!
# The weight-two M24 stabilizer is Aut(M22)

The native M22 image is the pointwise stabilizer of coordinates 0 and 9.
It is normal in the setwise stabilizer of that pair, so conjugation gives
an actual homomorphism to MulAut M22. Double transitivity on the other 22
coordinates forces its kernel to fix those coordinates. Golay minimum
distance and faithfulness of the code action make the kernel trivial.
Orbit--stabilizer gives order 887040; the proved complete M22 automorphism
coverage gives the same order for MulAut M22. Thus conjugation is an
isomorphism. Pair transitivity transports it to every weight-two vector.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, H.15.1(1)
and the preceding discussion, printed p.398. The intrinsic automorphism
coverage is the native result from GLS3, Table 5.3c, Note 1.
-/

public section

open Sporadic.Mathieu
open scoped Pointwise
namespace MathieuCode
noncomputable section

private abbrev basePair : Finset (Fin 24) := {0, 9}
private abbrev pairGroup := MulAction.stabilizer M24 basePair

/-- The native M22 image is exactly the pointwise stabilizer of coordinates 0 and 9. -/
lemma pairResidual_embedding_range (g : M24) :
    g ∈ m22Embedding.range ↔ g • (0 : Fin 24) = 0 ∧ g • (9 : Fin 24) = 9 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨m22Embedding_fixed_zero x, m22Embedding_fixed_nine x⟩
  · rintro ⟨h0, h9⟩
    have hg : g ∈ pointEmbedding.range := by
      rw [pointEmbedding_range]
      exact h0
    obtain ⟨x, rfl⟩ := hg
    have hx : x • (9 : Fin 23) = 9 := by
      apply m23PointEmbedding.injective
      change m23PointEmbedding (x.val 9) = m23PointEmbedding 9
      rw [← pointEmbedding_apply, show m23PointEmbedding 9 = (9 : Fin 24) by decide +kernel]
      exact h9
    let x' : MulAction.stabilizer M23 (9 : Fin 23) := ⟨x, hx⟩
    refine ⟨m23EquivM22PointStabilizer.symm x', ?_⟩
    change pointEmbedding ((m23EquivM22PointStabilizer
      (m23EquivM22PointStabilizer.symm x')).val) = pointEmbedding x
    rw [MulEquiv.apply_symm_apply]

private lemma range_le_pairGroup : m22Embedding.range ≤ pairGroup := by
  intro g hg
  obtain ⟨h0, h9⟩ := (pairResidual_embedding_range g).mp hg
  change g • ({0, 9} : Finset (Fin 24)) = {0, 9}
  simp only [Finset.smul_finset_insert, Finset.smul_finset_singleton, h0, h9]

private abbrev kernelPair := m22Embedding.range.subgroupOf pairGroup

private lemma pair_mem_iff (g : pairGroup) (i : Fin 24) :
    g.val • i ∈ basePair ↔ i ∈ basePair :=
  MulAction.mem_stabilizer_finset.mp g.property i

private instance kernelPair_normal : kernelPair.Normal where
  conj_mem n hn g := by
    change g.val * n.val * g.val⁻¹ ∈ m22Embedding.range
    rw [pairResidual_embedding_range]
    have hn' := (pairResidual_embedding_range n.val).mp hn
    have hf (i : Fin 24) (hi : i ∈ basePair) :
        (g.val * n.val * g.val⁻¹) • i = i := by
      have hpre : g.val⁻¹ • i ∈ basePair := (pair_mem_iff g⁻¹ i).mpr hi
      have hnfix : n.val • (g.val⁻¹ • i) = g.val⁻¹ • i := by
        rcases Finset.mem_insert.mp hpre with h | h
        · rw [h, hn'.1]
        · rw [Finset.mem_singleton.mp h, hn'.2]
      simp only [mul_smul, hnfix, smul_inv_smul]
    exact ⟨hf 0 (by simp), hf 9 (by simp)⟩

private def kernelPairEquiv : kernelPair ≃* M22 :=
  (Subgroup.subgroupOfEquivOfLe range_le_pairGroup).trans
    (MonoidHom.ofInjective m22Embedding_injective).symm

private def pairToAut : pairGroup →* MulAut M22 :=
  (MulAut.congr kernelPairEquiv).toMonoidHom.comp (MulAut.conjNormal (H := kernelPair))


private lemma fixes_moving_eq_one (g : M24)
    (hg : ∀ i : Fin 22, g • m22Coordinates i = m22Coordinates i) : g = 1 := by
  apply code_faithful
  apply LinearMap.ext
  intro q
  obtain ⟨v, rfl⟩ := codeLine.mkQ_surjective q
  rw [map_one, Module.End.one_apply, codeRepresentation_mk]
  apply congrArg codeLine.mkQ
  apply Subtype.ext
  apply sub_eq_zero.mp
  let w : Full := (golayRepresentation g v).val - v.val
  have hw : w ∈ golay := golay.sub_mem (golayRepresentation g v).property v.property
  have hsmall : hammingNorm w ≤ 2 := by
    have hs : (Finset.univ.filter fun i => w i ≠ 0) ⊆ basePair := by
      intro i hi
      obtain h | h | ⟨j, rfl⟩ := pairResidual_coordinates_cover i
      · simp [h]
      · simp [h]
      · have he : g.val.symm (m22Coordinates j) = m22Coordinates j := by
          exact g.val.symm_apply_eq.mpr (hg j).symm
        have hz : w (m22Coordinates j) = 0 := by
          change v.val (g.val.symm (m22Coordinates j)) - v.val (m22Coordinates j) = 0
          rw [he, sub_self]
        exact False.elim ((Finset.mem_filter.mp hi).2 hz)
    exact (Finset.card_le_card hs).trans (by decide)
  by_contra hn
  have hmin := native_golay_minimum hw hn
  omega

private lemma coordinates_not_pair (i : Fin 22) : m22Coordinates i ∉ basePair := by
  revert i
  decide +kernel

private lemma pair_centralizer_eq_one (g : pairGroup)
    (hg : ∀ k : M22, g.val * m22Embedding k = m22Embedding k * g.val) : g = 1 := by
  apply Subtype.ext
  apply fixes_moving_eq_one
  intro i
  have hout : g.val • m22Coordinates i ∉ basePair :=
    fun h => coordinates_not_pair i ((pair_mem_iff g _).mp h)
  obtain h | h | ⟨j, hj⟩ := pairResidual_coordinates_cover (g.val • m22Coordinates i)
  · exact False.elim (hout (by simp [h]))
  · exact False.elim (hout (by simp [h]))
  by_cases hji : j = i
  · exact hj.symm.trans (congrArg m22Coordinates hji)
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by decide)
  obtain ⟨x, hxi, hxj⟩ := (MulAction.is_two_pretransitive_iff.mp m22_isTwoPretransitive)
    (Ne.symm hji) (Ne.symm hki)
  have hc := congrArg (fun p : M24 => p.val (m22Coordinates i)) (hg x)
  change g.val • (m22Embedding x • m22Coordinates i) =
    m22Embedding x • (g.val • m22Coordinates i) at hc
  have hact (a : M22) (b : Fin 22) :
      m22Embedding a • m22Coordinates b = m22Coordinates (a • b) := m22Embedding_apply a b
  rw [hact, hxi, ← hj, hact, hxj] at hc
  exact False.elim (hkj (m22Coordinates.injective hc.symm))

private lemma kernelPairEquiv_embedding (k : kernelPair) :
    m22Embedding (kernelPairEquiv k) = k.val.val :=
  MonoidHom.apply_ofInjective_symm m22Embedding_injective _

private lemma kernelPairEquiv_symm_val (k : M22) :
    (kernelPairEquiv.symm k).val.val = m22Embedding k := by
  have h := kernelPairEquiv_embedding (kernelPairEquiv.symm k)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

private lemma pairToAut_apply (g : pairGroup) (k : M22) :
    m22Embedding (pairToAut g k) = g.val * m22Embedding k * g.val⁻¹ := by
  change m22Embedding (kernelPairEquiv
    ((MulAut.conjNormal (H := kernelPair) g) (kernelPairEquiv.symm k))) = _
  rw [kernelPairEquiv_embedding]
  change g.val * (kernelPairEquiv.symm k).val.val * g.val⁻¹ = _
  rw [kernelPairEquiv_symm_val]

private lemma pairToAut_injective : Function.Injective pairToAut := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply pair_centralizer_eq_one g
  intro k
  have he := pairToAut_apply g k
  rw [hg] at he
  change m22Embedding k = g.val * m22Embedding k * g.val⁻¹ at he
  exact (eq_mul_inv_iff_mul_eq.mp he).symm

private lemma pairGroup_card : Nat.card pairGroup = 887040 := by
  have ho : MulAction.orbit M24 basePair = {B : Finset (Fin 24) | B.card = 2} := by
    ext B
    constructor
    · rintro ⟨g, rfl⟩
      simp
    · intro hB
      obtain ⟨g, hg⟩ := weightTwoOrbit_transitive ⟨basePair, by decide⟩ ⟨B, hB⟩
      rw [pairVector_equivariant, pairVector_injective.eq_iff] at hg
      exact ⟨g, congrArg Subtype.val hg⟩
  have hoc : Nat.card (MulAction.orbit M24 basePair) = 276 := by
    rw [Nat.card_congr (Equiv.setCongr ho), Nat.card_eq_fintype_card]
    change Fintype.card {B : Finset (Fin 24) // B.card = 2} = 276
    rw [Fintype.card_finset_len]
    decide
  have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup M24 basePair)
  rw [Nat.card_prod, hoc, m24_order] at hc
  change 276 * Nat.card pairGroup = 244823040 at hc
  omega

private def designAutEquivAut : m22DesignAut ≃* MulAut M22 :=
  MulEquiv.ofBijective m22DesignAutToAut
    ⟨m22DesignAutToAut_injective, m22DesignAutToAut_surjective⟩

private lemma pairToAut_bijective : Function.Bijective pairToAut := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨pairToAut_injective, ?_⟩
  rw [pairGroup_card, ← Nat.card_congr designAutEquivAut.toEquiv, m22DesignAut_order]

/-- Conjugation identifies the native setwise stabilizer of {0,9} with Aut(M22). -/
def pairResidual_baseStabilizerEquiv :
    MulAction.stabilizer M24 ({0, 9} : Finset (Fin 24)) ≃* MulAut M22 :=
  MulEquiv.ofBijective pairToAut pairToAut_bijective

/-- Every native weight-two M24 vector has its actual stabilizer isomorphic to Aut(M22). -/
lemma pairVector_stabilizer_equiv (B : PointPair) :
    Nonempty (cocodeVectorStabilizer cocodeRepresentation (pairVector B) ≃* MulAut M22) := by
  obtain ⟨g, hg⟩ := weightTwoOrbit_transitive ⟨basePair, by decide⟩ B
  rw [pairVector_equivariant, pairVector_injective.eq_iff] at hg
  have he : g • basePair = B.val := congrArg Subtype.val hg
  exact ⟨(MulEquiv.subgroupCongr (pairVector_stabilizer B)).trans
    ((MulAction.stabilizerEquivStabilizer he.symm).symm.trans pairResidual_baseStabilizerEquiv)⟩

lemma weightTwoOrbit_stabilizer_equiv {v : Cocode} (hv : v ∈ weightTwoOrbit) :
    Nonempty (cocodeVectorStabilizer cocodeRepresentation v ≃* MulAut M22) := by
  obtain ⟨B, rfl⟩ := hv
  exact pairVector_stabilizer_equiv B

end
end MathieuCode
