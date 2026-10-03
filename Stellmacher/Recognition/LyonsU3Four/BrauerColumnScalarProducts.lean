module

public import Stellmacher.Recognition.LyonsU3Four.BrauerColumnInduction
public import Stellmacher.Recognition.LyonsU3Four.LocalFivePrincipalBlock
public import Theory.Character.ModularBlock.InvolutionRootRestriction
public import Theory.Character.ModularBlock.OrdinaryOddQuotient
public import Theory.GroupTheory.OddElementSum
public import Theory.Character.ModularBlock.CartanEquiv

/-!
# Scalar products of the genuine local section columns

The principal ordinary block of the actual involution centralizer is the
inflation of the complete local table through its odd core. Reindexing the
compatible principal projection by that table, then evaluating at `z * π`
for odd-order `π`, expresses the projection in the five complement characters.
Odd lifts of the complement and independence of its characters identify every
coefficient with the integral ambient decomposition column, and give zero
outside the ambient principal block. Frobenius reciprocity conjugates these
coefficients; their integrality removes that conjugation.

The quotient identification preserves the supplied Sylow embedding. The odd
core and the arbitrary enumeration of the five basic characters are retained.
The given genuine table suffices; no additional simplicity, centralizer
structure, or automorphism-order hypotheses are required in this step.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972), p. 381,
Brauer's transfer preceding Lemma 4. Local source:
`refs/original/n-group-global/odd-core-rank-two-source/lyons-u3four-1972-ams-wayback.pdf`.
-/

public section
open scoped BigOperators
open Subgroup ModularBlock PrincipalBlockConstruction CompatibleLocalBlock
noncomputable section
namespace Stellmacher.Recognition.LyonsU3Four
attribute [local instance] Fintype.ofFinite Classical.propDecidable
variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    {α : FiveComplement →* MulAut S}

private theorem inflated_table_index (h : SylowStructure S) (T : LocalFiveCharacterTable S α)
    {H : Type*} [Group H] [Fintype H] (N : Subgroup H) [N.Normal]
    (hN : Odd (Nat.card N)) (e : (H ⧸ N) ≃* LocalFiveGroup S α)
    (d : PrincipalCongruenceBlockData H) :
    ∃ E : LocalFiveRowIndex S ≃ {j // j ∈ d.block}, ∀ r a,
      d.chi (E r).val (ConjClasses.mk a) =
        T.row r (ConjClasses.mk (e (QuotientGroup.mk' N a))) := by
  classical
  let q := compatibleQuotientPrincipalCongruenceBlockData d N
  have hq : q.block = Finset.univ := by
    rw [← q.transport_block e]
    exact T.block_eq_univ h (q.transport e)
  let U : q.I ≃ {j // j ∈ q.block} :=
    (Equiv.subtypeUnivEquiv (fun j => by rw [hq]; exact Finset.mem_univ j)).symm
  let E := (T.blockIndex (q.transport e)).trans
    (U.trans (OrdinaryOddQuotient.blockEquiv d N hN).symm)
  refine ⟨E, ?_⟩
  intro r a
  rw [OrdinaryOddQuotient.blockEquiv_character d N hN]
  change q.chi ((OrdinaryOddQuotient.blockEquiv d N hN)
    ((OrdinaryOddQuotient.blockEquiv d N hN).symm (U (T.blockIndex (q.transport e) r)))).val _ = _
  rw [Equiv.apply_symm_apply]
  have hr := congrFun (T.blockIndex_apply (q.transport e) r)
    (ConjClasses.mk (e (QuotientGroup.mk' N a)))
  change q.chi (T.blockIndex (q.transport e) r)
    (ConjClasses.mk (e.symm (e (QuotientGroup.mk' N a)))) = _ at hr
  simpa only [U, Equiv.subtypeUnivEquiv_symm_apply, e.symm_apply_apply] using hr

private theorem projection_reindex (h : SylowStructure S) (T : LocalFiveCharacterTable S α)
    {H : Type*} [Group H] [Fintype H] (N : Subgroup H) [N.Normal]
    (hN : Odd (Nat.card N)) (e : (H ⧸ N) ≃* LocalFiveGroup S α)
    (d : PrincipalCongruenceBlockData H) (f : ClassFunction H) (a : H) :
    (∑ j ∈ d.block, scalarProduct H f (fun x => d.chi j (ConjClasses.mk x)) *
      d.chi j (ConjClasses.mk a)) =
    ∑ r : LocalFiveRowIndex S,
      scalarProduct H f (fun x => T.row r (ConjClasses.mk (e (QuotientGroup.mk' N x)))) *
        T.row r (ConjClasses.mk (e (QuotientGroup.mk' N a))) := by
  classical
  obtain ⟨E, hE⟩ := inflated_table_index h T N hN e d
  rw [← Finset.sum_coe_sort]
  symm
  apply Fintype.sum_equiv E
  intro r
  simp only [hE]

private theorem scalar_integer_sum {H I : Type*} [Fintype H] [Fintype I]
    (f : H → ℂ) (r : I → H → ℂ) (a : I → ℤ) :
    scalarProduct H f (fun x => ∑ i, (a i : ℂ) * r i x) =
      ∑ i, (a i : ℂ) * scalarProduct H f (r i) := by
  simp only [scalarProduct, star_sum, star_mul, star_intCast, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro x _
  ring

private theorem section_projection (h : SylowStructure S) (T : LocalFiveCharacterTable S α)
    {H : Type*} [Group H] [Fintype H] (N : Subgroup H) [N.Normal]
    (e : (H ⧸ N) ≃* LocalFiveGroup S α) (w : QuarticCentralIndex S)
    (f : ClassFunction H) (u : LocalFiveGroup S α) (hu : Odd (orderOf u)) :
    (∑ r : LocalFiveRowIndex S,
      scalarProduct H f (fun x => T.row r (ConjClasses.mk (e (QuotientGroup.mk' N x)))) *
        T.row r (ConjClasses.mk (SemidirectProduct.inl w.1.1 * u))) =
    ∑ k : FiveLinearIndex, scalarProduct H f (T.inflatedSectionClassFunction w N e k) *
      k u.right := by
  let R : LocalFiveRowIndex S → H → ℂ := fun r x =>
    T.row r (ConjClasses.mk (e (QuotientGroup.mk' N x)))
  have hPhi (k : FiveLinearIndex) : T.inflatedSectionClassFunction w N e k =
      fun x => ∑ r, (localFiveSectionRow S w r k : ℂ) * R r x := by
    funext x
    change T.sectionClassFunction w k (e (QuotientGroup.mk' N x)) = _
    rw [T.sectionClassFunction_apply]
    apply Finset.sum_congr (by ext; simp)
    intro r _
    rfl
  calc
    _ = ∑ r : LocalFiveRowIndex S, scalarProduct H f (R r) *
        (∑ k : FiveLinearIndex, (localFiveSectionRow S w r k : ℂ) * k u.right) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [T.section_expansion h w r u hu]
    _ = _ := by
      simp_rw [hPhi, scalar_integer_sum]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro r _
      ring

private theorem five_coefficients_unique (ε : Fin 5 ≃ FiveLinearIndex)
    (A B : Fin 5 → ℂ)
    (he : ∀ v : FiveComplement, ∑ i, A i * ε i v = ∑ i, B i * ε i v) : A = B := by
  have hlin := (linearIndependent_monoidHom FiveComplement ℂ).comp ε ε.injective
  apply hlin.fintypeLinearCombination_injective
  change (∑ i, A i • (ε i : FiveComplement → ℂ)) = ∑ i, B i • (ε i : FiveComplement → ℂ)
  funext v
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using he v

private theorem root_projection_expansion (h : SylowStructure S)
    (T : LocalFiveCharacterTable S α) {z : G} (hz : z ∈ centerImage S)
    (hz2 : orderOf z = 2)
    (e : (centralizer ({z} : Set G) ⧸ pPrimeCore 2 (centralizer ({z} : Set G))) ≃*
      LocalFiveGroup S α)
    (he : ∀ s : S, e (involutionCentralizerQuotientMap S hz s) = SemidirectProduct.inl s)
    (w : QuarticCentralIndex S) (hw : (w.1.1 : G) = z)
    (b : PrincipalCongruenceBlockData G) (j : b.I)
    (π : centralizer ({z} : Set G)) (hπ : Odd (orderOf π)) :
    (∑ k : FiveLinearIndex,
      scalarProduct (centralizer ({z} : Set G))
        (fun a => b.chi j (ConjClasses.mk (a : G)))
        (T.inflatedSectionClassFunction w (pPrimeCore 2 _) e k) *
          k (e (QuotientGroup.mk' (pPrimeCore 2 _) π)).right) =
    if j ∈ b.block then b.chi j (ConjClasses.mk (z * (π : G))) else 0 := by
  let C := centralizer ({z} : Set G)
  let N := pPrimeCore 2 C
  let zC : C := inclusion (sylow_le_involutionCentralizer S hz) w.1.1
  have hzC : (zC : G) = z := hw
  have hzC2 : zC ^ 2 = 1 := by
    apply Subtype.ext
    change (zC : G) ^ 2 = 1
    rw [hzC, ← hz2, pow_orderOf_eq_one]
  have hcomm : Commute zC π := by
    apply Subtype.ext
    change (zC : G) * (π : G) = (π : G) * (zC : G)
    rw [hzC]
    exact (mem_centralizer_singleton_iff.mp π.property).symm
  have hpow : (zC * π) ^ orderOf π = zC := by
    rw [hcomm.mul_pow, pow_orderOf_eq_one, mul_one]
    obtain ⟨n, hn⟩ := hπ
    rw [hn, pow_add, pow_mul, hzC2]
    simp
  have hroot : z ∈ zpowers ((zC * π : C) : G) := by
    refine mem_zpowers_iff.mpr ⟨(orderOf π : ℤ), ?_⟩
    rw [zpow_natCast]
    exact (congrArg Subtype.val hpow).trans hzC
  have hproj := InvolutionRootRestriction.restriction_projection_on_involution_roots
    b z hz2 j (zC * π) hroot
  have hN : Odd (Nat.card N) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := C))
  dsimp only at hproj
  have hre := projection_reindex h T N hN e
    (CompatibleBrauerBlock.localData b C) (fun a => b.chi j (ConjClasses.mk (a : G))) (zC * π)
  have hproj' : (∑ r : LocalFiveRowIndex S,
      scalarProduct C (fun a => b.chi j (ConjClasses.mk (a : G)))
        (fun x => T.row r (ConjClasses.mk (e (QuotientGroup.mk' N x)))) *
          T.row r (ConjClasses.mk (e (QuotientGroup.mk' N (zC * π))))) =
      if j ∈ b.block then b.chi j (ConjClasses.mk ((zC * π : C) : G)) else 0 := by
    rw [← hre]
    convert hproj using 1
    apply Finset.sum_congr rfl
    intro r _
    congr 1
    unfold scalarProduct
    congr 1
    apply Finset.sum_congr (by ext; simp)
    intro x _
    rfl
  clear hproj
  have hproj := hproj'
  have hem : e (QuotientGroup.mk' N (zC * π)) =
      SemidirectProduct.inl w.1.1 * e (QuotientGroup.mk' N π) := by
    rw [map_mul, map_mul]
    congr 1
    exact he w.1.1
  simp_rw [hem] at hproj
  have hu : Odd (orderOf (e (QuotientGroup.mk' N π))) :=
    hπ.of_dvd_nat (orderOf_map_dvd (e.toMonoidHom.comp (QuotientGroup.mk' N)) π)
  have hs := section_projection h T N e w
    (fun a => b.chi j (ConjClasses.mk (a : G))) (e (QuotientGroup.mk' N π)) hu
  rw [hs] at hproj
  simpa only [Subgroup.coe_mul, hzC] using hproj

omit [Finite G] in
private theorem exists_odd_complement_lift
    {H : Type*} [Group H] [Fintype H] (N : Subgroup H) [N.Normal]
    (hN : Odd (Nat.card N)) (e : (H ⧸ N) ≃* LocalFiveGroup S α)
    (v : FiveComplement) :
    ∃ π : H, Odd (orderOf π) ∧ e (QuotientGroup.mk' N π) = SemidirectProduct.inr v := by
  obtain ⟨π, hπ⟩ := QuotientGroup.mk'_surjective N (e.symm (SemidirectProduct.inr v))
  have heπ : e (QuotientGroup.mk' N π) = SemidirectProduct.inr v := by simp [hπ]
  refine ⟨π, (OddElementSum.odd_quotient_iff N hN π).mp ?_, heπ⟩
  rw [← e.orderOf_eq, heπ]
  apply (by decide : Odd 5).of_dvd_nat
  apply orderOf_dvd_of_pow_eq_one
  rw [← map_pow]
  have hv : v ^ 5 = 1 := by
    have hcard : Nat.card FiveComplement = 5 := by
      change Nat.card (Multiplicative (ZMod 5)) = 5
      rw [Nat.card_eq_fintype_card]
      decide
    simpa only [hcard] using pow_card_eq_one' (x := v)
  rw [hv, map_one]

/-- The genuine local section column has precisely the integral ambient
coefficient supplied by the section expansion, and is zero off the principal block. -/
theorem LocalFiveCharacterTable.inducedSection_scalarProduct
    (T : LocalFiveCharacterTable S α) (h : SylowStructure S)
    {z : G} (hz : z ∈ centerImage S) (hz2 : orderOf z = 2)
    (e : (centralizer ({z} : Set G) ⧸ pPrimeCore 2 (centralizer ({z} : Set G))) ≃*
      LocalFiveGroup S α)
    (he : ∀ s : S, e (involutionCentralizerQuotientMap S hz s) = SemidirectProduct.inl s)
    (w : QuarticCentralIndex S) (hw : (w.1.1 : G) = z)
    (b : PrincipalCongruenceBlockData G)
    (c : GeneralizedDecompositionData {j // j ∈ b.block})
    (t : G) (μ : centralizer ({z} : Set G) →* ℂ)
    (hc : c.Equation3_1 (fun j g => b.chi j.val (ConjClasses.mk g)) t z μ)
    (ε : Fin 5 ≃ FiveLinearIndex)
    (hε : ∀ i (π : centralizer ({z} : Set G)), Odd (orderOf π) →
      μ π ^ GeneralizedDecompositionData.basicExponent i =
        ε i (e (QuotientGroup.mk' (pPrimeCore 2 _) π)).right)
    (i : Fin 5) (j : b.I) :
    scalarProduct G
      (inducedClassFunction (centralizer ({z} : Set G))
        (T.inflatedSectionClassFunction w (pPrimeCore 2 _) e (ε i)))
      (ofConjClassFunction (b.chi j)) =
    if hj : j ∈ b.block then (c.iDz i ⟨j, hj⟩ : ℂ) else 0 := by
  classical
  let C := centralizer ({z} : Set G)
  let N := pPrimeCore 2 C
  let f : ClassFunction C := fun a => b.chi j (ConjClasses.mk (a : G))
  let A : Fin 5 → ℂ := fun k => scalarProduct C f (T.inflatedSectionClassFunction w N e (ε k))
  let B : Fin 5 → ℂ := fun k => if hj : j ∈ b.block then (c.iDz k ⟨j, hj⟩ : ℂ) else 0
  have hAB : A = B := by
    apply five_coefficients_unique ε
    intro v
    have hN : Odd (Nat.card N) :=
      Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := C))
    obtain ⟨π, hπ, heπ⟩ := exists_odd_complement_lift N hN e v
    have hp := root_projection_expansion h T hz hz2 e he w hw b j π hπ
    rw [heπ] at hp
    change (∑ k, scalarProduct C f (T.inflatedSectionClassFunction w N e k) * k v) = _ at hp
    calc
      (∑ k, A k * ε k v) = ∑ k : FiveLinearIndex,
          scalarProduct C f (T.inflatedSectionClassFunction w N e k) * k v :=
        ε.sum_comp (fun k => scalarProduct C f
          (T.inflatedSectionClassFunction w N e k) * k v)
      _ = _ := hp
      _ = ∑ k, B k * ε k v := by
        by_cases hj : j ∈ b.block
        · simp only [hj, if_pos, B, dif_pos]
          have hv := hc.2 ⟨j, hj⟩ π hπ
          dsimp only at hv
          rw [hv]
          apply Finset.sum_congr rfl
          intro k _
          rw [hε k π hπ, heπ]
          rfl
        · simp [hj, B]
  rw [scalarProduct_inducedClassFunction _ _ (ofConjClassFunction_isClassFunction _)]
  change scalarProduct C (T.inflatedSectionClassFunction w N e (ε i)) f = B i
  rw [← scalarProduct_conj]
  change star (A i) = B i
  rw [hAB]
  dsimp [B]
  split <;> simp

/-- Brauer transfer for each of the five genuine local section columns, with
an arbitrary compatible enumeration of the basic characters. -/
theorem LocalFiveCharacterTable.inducedSection_eq_iDz_column
    (T : LocalFiveCharacterTable S α) (h : SylowStructure S)
    {z : G} (hz : z ∈ centerImage S) (hz1 : z ≠ 1)
    (e : (centralizer ({z} : Set G) ⧸ pPrimeCore 2 (centralizer ({z} : Set G))) ≃*
      LocalFiveGroup S α)
    (he : ∀ s : S, e (involutionCentralizerQuotientMap S hz s) = SemidirectProduct.inl s)
    (w : QuarticCentralIndex S) (hw : (w.1.1 : G) = z)
    (b : PrincipalCongruenceBlockData G)
    (c : GeneralizedDecompositionData {j // j ∈ b.block})
    (t : G) (μ : centralizer ({z} : Set G) →* ℂ)
    (hc : c.Equation3_1 (fun j g => b.chi j.val (ConjClasses.mk g)) t z μ)
    (ε : Fin 5 ≃ FiveLinearIndex)
    (hε : ∀ i (π : centralizer ({z} : Set G)), Odd (orderOf π) →
      μ π ^ GeneralizedDecompositionData.basicExponent i =
        ε i (e (QuotientGroup.mk' (pPrimeCore 2 _) π)).right)
    (i : Fin 5) :
    inducedClassFunction (centralizer ({z} : Set G))
      (T.inflatedSectionClassFunction w (pPrimeCore 2 _) e (ε i)) =
      ∑ j : {j // j ∈ b.block}, (c.iDz i j : ℂ) • ofConjClassFunction (b.chi j.val) := by
  classical
  have hzpow : z ^ 2 = 1 := by
    let _ := h.center_elementary
    rw [← hw]
    exact congrArg Subtype.val (elemPow_eq_one_of_isElementaryAbelian (p := 2)
      w.1.1 w.1.property)
  have hz2 : orderOf z = 2 := orderOf_eq_prime hzpow hz1
  have hscalar := T.inducedSection_scalarProduct h hz hz2 e he w hw b c t μ hc ε hε i
  rw [inducedClassFunction_eq_iDz_full_column _ b c i _
    (fun j => by simpa only [dif_pos j.property] using hscalar j.val)
    (fun j hj => by simpa only [dif_neg hj] using hscalar j)]
  have hs := Finset.sum_attach_eq_sum_dite b.block
    (fun j : {j // j ∈ b.block} => (c.iDz i j : ℂ) • ofConjClassFunction (b.chi j.val))
  rw [← Finset.univ_eq_attach] at hs
  rw [hs]
  apply Finset.sum_congr rfl
  intro j _
  split <;> simp_all

end Stellmacher.Recognition.LyonsU3Four
