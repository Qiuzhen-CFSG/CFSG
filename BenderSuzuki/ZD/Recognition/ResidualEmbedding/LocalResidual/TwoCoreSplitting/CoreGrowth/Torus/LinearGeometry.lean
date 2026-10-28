module

public import BenderSuzuki.Converse.PSL2
public import GorensteinWalter.PSL2RootSylow
public import BenderSuzuki.SE.Basic

/-!
# A split torus for a prescribed outside involution in binary PSL₂

A strongly embedded subgroup contains a Sylow two-subgroup and its
normalizer. Conjugacy of Sylow subgroups therefore places a conjugate of
the standard Borel inside the prescribed subgroup. The given outside
involution remains outside this Borel.

For a square-one matrix with nonzero lower-left entry `c`, choose `r² = c`.
An explicit upper-triangular matrix conjugates it to the Weyl reflection.
Transporting the diagonal torus back gives a cyclic subgroup of order
`|K| - 1`, inside the Borel and inverted by the prescribed involution.
The central quotient map is injective in characteristic two, so this
construction transfers to the actual PSL₂ carrier.

Source: GLS, Volume 4, Chapter 4, Lemma 3.2(c–e,i). This proves the
particular linear geometry used in Chapter 2, Proposition 17.6, without
an involution-classification or regular-action premise.
-/

noncomputable section
namespace BenderSuzuki.ZD.CoreGrowthTorus
open BenderSuzuki.Converse BenderSuzuki.PFAppendixIII BenderSuzuki.PFchapter1section1
open scoped Pointwise
variable {K : Type*} [Field K] [CharP K 2] [Finite K]

private theorem exists_Borel_conj_weyl (A : SL2 K)
    (hAA : A * A = 1) (hc : A.val 1 0 ≠ 0) :
    ∃ h : SL2 K, h ∈ Borel K ∧ h * A * h⁻¹ = weyl K := by
  have hd : A.val 1 1 = A.val 0 0 := by
    have he := congrArg (fun g : SL2 K => g.val 1 0) hAA
    have he0 : A.val 1 0 * A.val 0 0 + A.val 1 1 * A.val 1 0 = 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using he
    have he' : (A.val 1 1 + A.val 0 0) * A.val 1 0 = 0 := by
      linear_combination he0
    exact CharTwo.add_eq_zero.mp ((mul_eq_zero.mp he').resolve_right hc)
  have hdet : A.val 0 0 * A.val 0 0 + A.val 0 1 * A.val 1 0 = 1 := by
    simpa only [Matrix.det_fin_two, hd, CharTwo.sub_eq_add] using A.property
  obtain ⟨r, hr2⟩ := (Finite.surjective_of_injective (CharTwo.sq_injective (R := K))) (A.val 1 0)
  change r ^ 2 = A.val 1 0 at hr2
  have hr : r ≠ 0 := by intro hz; apply hc; rw [← hr2, hz]; simp
  let h : SL2 K := ⟨!![r, A.val 0 0 / r; 0, r⁻¹], by
    simp [Matrix.det_fin_two, hr]⟩
  have hcr : r⁻¹ * A.val 1 0 = r := by
    rw [← hr2, pow_two, ← mul_assoc, inv_mul_cancel₀ hr, one_mul]
  have hrel : h * A = weyl K * h := by
    apply Subtype.ext
    change h.val * A.val = (weyl K).val * h.val
    ext i j
    fin_cases i <;> fin_cases j
    · simp [h, Matrix.mul_apply, Fin.sum_univ_two]
      rw [div_eq_mul_inv, mul_assoc, hcr, mul_comm r, CharTwo.add_self_eq_zero]
    · simp [h, Matrix.mul_apply, Fin.sum_univ_two, hd]
      field_simp
      linear_combination hdet + A.val 0 1 * hr2
    · simpa [h, Matrix.mul_apply, Fin.sum_univ_two] using hcr
    · simp [h, Matrix.mul_apply, Fin.sum_univ_two, hd, div_eq_mul_inv, mul_comm]
  refine ⟨h, ?_, ?_⟩
  · rw [mem_Borel_iff]; simp [h]
  · rw [hrel, mul_inv_cancel_right]


omit [Finite K] in
private theorem weyl_inverts_torus (a : SL2 K) (ha : a ∈ Torus K) :
    weyl K * a * (weyl K)⁻¹ = a⁻¹ := by
  rw [Torus_eq_range] at ha
  obtain ⟨r, rfl⟩ := ha
  rw [← map_inv, weyl_inv]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem sl2_torus_of_outside_borel (s : SL2 K)
    (hs : s * s = 1) (hsB : s ∉ Borel K) :
    ∃ U : Subgroup (SL2 K), IsCyclic U ∧ Nat.card U = Nat.card K - 1 ∧
      U ≤ Borel K ∧ ∀ a ∈ U, s * a * s⁻¹ = a⁻¹ := by
  obtain ⟨h, hh, hhs⟩ := exists_Borel_conj_weyl s hs
    (fun hc => hsB ((mem_Borel_iff s).mpr hc))
  let e := MulAut.conj h
  let U := (Torus K).map e.symm.toMonoidHom
  let eU : Torus K ≃* U := (Torus K).equivMapOfInjective _ e.symm.injective
  have hcyc : IsCyclic (Torus K) := by
    rw [Torus_eq_range]
    exact isCyclic_of_surjective _ (torHom K).rangeRestrict_surjective
  have hcard : Nat.card (Torus K) = Nat.card K - 1 := by
    rw [Torus_eq_range, ← Nat.card_congr (MonoidHom.ofInjective
      (torHom_injective (F := K))).toEquiv]
    exact Nat.card_units K
  refine ⟨U, eU.isCyclic.mp hcyc, (Nat.card_congr eU.toEquiv).symm.trans hcard, ?_, ?_⟩
  · rintro a ⟨b, hb, rfl⟩
    change h⁻¹ * b * h ∈ Borel K
    exact (Borel K).mul_mem ((Borel K).mul_mem ((Borel K).inv_mem hh)
      (Torus_le_Borel hb)) hh
  · rintro a ⟨b, hb, rfl⟩
    apply e.injective
    simp only [map_mul, map_inv, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulEquiv.apply_symm_apply]
    change e s * b * (e s)⁻¹ = b⁻¹
    rw [show e s = weyl K from hhs]
    exact weyl_inverts_torus b hb

private theorem psl2_torus_of_outside_borel (s : PSL2 K)
    (hs : IsInvolution s) (hsB : s ∉ PBorel K) :
    ∃ U : Subgroup (PSL2 K), IsCyclic U ∧ Nat.card U = Nat.card K - 1 ∧
      U ≤ PBorel K ∧ ∀ a ∈ U, s * a * s⁻¹ = a⁻¹ := by
  obtain ⟨v, rfl⟩ := pi_surjective s
  have hv : v * v = 1 := by
    apply pi_injective (F := K)
    simpa only [map_mul, map_one, pow_two] using hs.2
  have hvB : v ∉ Borel K := by
    intro h
    exact hsB (PBorel_eq_map (F := K) ▸ Subgroup.mem_map_of_mem (pi K) h)
  obtain ⟨V, hVc, hVo, hVB, hVv⟩ := sl2_torus_of_outside_borel v hv hvB
  let U := V.map (pi K)
  let e : V ≃* U := V.equivMapOfInjective _ pi_injective
  refine ⟨U, e.isCyclic.mp hVc, (Nat.card_congr e.toEquiv).symm.trans hVo, ?_, ?_⟩
  · rw [PBorel_eq_map]
    exact Subgroup.map_mono hVB
  · rintro a ⟨b, hb, rfl⟩
    simpa only [map_mul, map_inv] using congrArg (pi K) (hVv b hb)

/-- A torus inside the prescribed strongly embedded subgroup, inverted by
its prescribed outside involution. Both subgroup and involution retain
their original markings throughout the construction. -/
public theorem psl2_torus_of_stronglyEmbedded
    {n : ℕ} (hKcard : Nat.card K = 2 ^ n)
    (B : Subgroup (PSL2 K)) (hB : IsStronglyEmbedded B)
    (s : PSL2 K) (hs : IsInvolution s) (hsB : s ∉ B) :
    ∃ U : Subgroup (PSL2 K), IsCyclic U ∧ Nat.card U = Nat.card K - 1 ∧
      U ≤ B ∧ ∀ a ∈ U, s * a * s⁻¹ = a⁻¹ := by
  obtain ⟨S, hSB⟩ := hB.containsSylowTwo
  obtain ⟨P, hP⟩ := GorensteinWalter.psl2UpperUnipotent_isSylow K hKcard
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PSL2 K) P S
  let e := MulAut.conj g
  have hroot : PUnip K = GorensteinWalter.psl2UpperUnipotentSubgroup K := by
    rw [PUnip, GorensteinWalter.psl2UpperUnipotentSubgroup,
      GorensteinWalter.psl2UpperUnipotentHom, MonoidHom.range_comp]
    rfl
  have hPS : (PUnip K).map e.toMonoidHom = (S : Subgroup (PSL2 K)) := by
    rw [hroot]
    rw [← hP]
    exact congrArg (fun Q : Sylow 2 (PSL2 K) => (Q : Subgroup (PSL2 K))) hg
  let z := pi K (uni (1 : K))
  have hzP : z ∈ PUnip K := Subgroup.mem_map_of_mem _
    ((mem_Unip_iff _).mpr ⟨1, rfl⟩)
  have hz : IsInvolution z := by
    refine IsInvolution.map_of_injective ?_ (pi K) pi_injective
    refine ⟨?_, ?_⟩
    · intro he
      have he' := uni_injective (he.trans uni_zero.symm)
      exact one_ne_zero he'
    · rw [pow_two, uni_mul_uni, CharTwo.add_self_eq_zero, uni_zero]
  have hxS : e z ∈ (S : Subgroup (PSL2 K)) :=
    hPS ▸ Subgroup.mem_map_of_mem e.toMonoidHom hzP
  have hNB : (PBorel K).map e.toMonoidHom ≤ B := by
    have hnormalizer : Subgroup.normalizer (PUnip K : Set (PSL2 K)) = PBorel K :=
      hroot ▸ GorensteinWalter.psl2UpperUnipotent_normalizer_eq_borel K
    rw [← hnormalizer, Subgroup.map_equiv_normalizer_eq, hPS]
    intro a ha
    apply hB.mem_of_involution_mem_rightConjugate (hSB hxS) ?_
      (IsInvolution.map_of_injective hz e.toMonoidHom e.injective)
    rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨a * e z * a⁻¹,
      hSB ((Subgroup.mem_normalizer_iff.mp ha (e z)).mp hxS), ?_⟩
    simp [mul_assoc]
  have hs0 : e.symm s ∉ PBorel K := by
    intro hm
    apply hsB
    have hh := hNB (Subgroup.mem_map_of_mem e.toMonoidHom hm)
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulEquiv.apply_symm_apply] using hh
  obtain ⟨V, hVc, hVo, hVB, hVs⟩ := psl2_torus_of_outside_borel (e.symm s)
    (IsInvolution.map_of_injective hs e.symm.toMonoidHom e.symm.injective) hs0
  let U := V.map e.toMonoidHom
  let eU : V ≃* U := V.equivMapOfInjective _ e.injective
  refine ⟨U, eU.isCyclic.mp hVc, (Nat.card_congr eU.toEquiv).symm.trans hVo,
    (Subgroup.map_mono hVB).trans hNB, ?_⟩
  rintro a ⟨b, hb, rfl⟩
  have hh := congrArg e (hVs b hb)
  simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply,
    MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe] using hh

end BenderSuzuki.ZD.CoreGrowthTorus
