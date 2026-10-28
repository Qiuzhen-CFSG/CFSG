module
public import Stellmacher.Recognition.LyonsU3Four.BrauerColumnInduction
public import Theory.Character.ModularBlock.OrdinaryOddQuotient
public import Theory.Character.ModularBlock.CartanEquiv
public import Theory.Character.ModularBlock.InvolutionRootRestriction

/-!
# Coefficients of the induced genuine local columns

The ordinary principal rows of the involution centralizer are exactly the
inflated rows of the supplied local table, by descent through its odd core.
The principal-block restriction theorem, evaluated on the involution times
odd-order elements, identifies the signed sums of restriction multiplicities.
Independence of the five complement characters identifies every coefficient,
including zero for each nonprincipal ambient row. Frobenius reciprocity then
gives the desired induction identity for the genuine local section columns.

The enumeration of the five linear characters is arbitrary, subject only to
compatibility with the power basis in equation (3.1). Neither induction nor
its scalar products are assumed, and the odd core need not be trivial.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), p. 381,
Brauer's transfer preceding Lemma 4.
-/

public section
noncomputable section
namespace Stellmacher.Recognition.LyonsU3Four
open scoped BigOperators
open Subgroup ModularBlock PrincipalBlockConstruction CompatibleLocalBlock
-- Use the same finite enumerations as the principal-block restriction API.
attribute [local instance 2000] Fintype.ofFinite
attribute [local instance] Classical.propDecidable
variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    {α : FiveComplement →* MulAut S}

/-- The ordinary principal rows of an odd extension of the local group are
exactly the inflated rows of its genuine ordinary table. -/
theorem LocalFiveCharacterTable.exists_inflatedBlockIndex
    (T : LocalFiveCharacterTable S α) (h : SylowStructure S)
    {H : Type*} [Group H] [Finite H] (d : PrincipalCongruenceBlockData H)
    (N : Subgroup H) [N.Normal] (hN : Odd (Nat.card N))
    (e : (H ⧸ N) ≃* LocalFiveGroup S α) :
    ∃ E : LocalFiveRowIndex S ≃ {j // j ∈ d.block},
      ∀ r a, d.chi (E r).val (ConjClasses.mk a) =
        T.row r (ConjClasses.mk (e (QuotientGroup.mk' N a))) := by
  let q := compatibleQuotientPrincipalCongruenceBlockData d N
  let K := q.transport e
  have hall : q.block = Finset.univ := by
    simpa only [K, PrincipalCongruenceBlockData.transport_block] using T.block_eq_univ h K
  let E₀ : LocalFiveRowIndex S ≃ {j // j ∈ q.block} :=
    (T.blockIndex K).trans (Equiv.subtypeUnivEquiv
      (by intro j; rw [hall]; exact Finset.mem_univ j)).symm
  let E := E₀.trans (OrdinaryOddQuotient.blockEquiv d N hN).symm
  refine ⟨E, ?_⟩
  intro r a
  rw [OrdinaryOddQuotient.blockEquiv_character d N hN]
  change q.chi ((OrdinaryOddQuotient.blockEquiv d N hN)
    ((OrdinaryOddQuotient.blockEquiv d N hN).symm (E₀ r))).val _ = _
  rw [Equiv.apply_symm_apply]
  change q.chi (T.blockIndex K r) _ = _
  have hv := congrFun (T.blockIndex_apply K r)
    (ConjClasses.mk (e (QuotientGroup.mk' N a)))
  change q.chi (T.blockIndex K r)
    (ConjClasses.mk (e.symm (e (QuotientGroup.mk' N a)))) = _ at hv
  simpa only [MulEquiv.symm_apply_apply] using hv

omit [Finite G] in
private theorem five_coefficients_unique
    {H : Type*} [Group H] [Finite H]
    (q : H →* LocalFiveGroup S α) (hq : Function.Surjective q)
    (a b : FiveLinearIndex → ℂ)
    (hab : ∀ v : H, Odd (orderOf v) →
      (∑ j, a j * j (q v).right) = ∑ j, b j * j (q v).right) : a = b := by
  apply funext
  apply Fintype.linearIndependent_iffₛ.mp (linearIndependent_monoidHom FiveComplement ℂ)
  funext v
  have hv5 : (SemidirectProduct.inr v : LocalFiveGroup S α) ^ 5 = 1 := by
    rw [← map_pow]
    have hv : v ^ 5 = 1 := by
      simpa only [show Nat.card FiveComplement = 5 from by
        rw [Nat.card_congr (Multiplicative.toAdd : FiveComplement ≃ ZMod 5), Nat.card_zmod]] using pow_card_eq_one' (x := v)
    rw [hv, map_one]
  have hvodd : Odd (orderOf (SemidirectProduct.inr v : LocalFiveGroup S α)) :=
    (by decide : Odd 5).of_dvd_nat (orderOf_dvd_of_pow_eq_one hv5)
  obtain ⟨u, hu, hqu⟩ := q.exists_pRegular_lift hq 2 Nat.prime_two
    (SemidirectProduct.inr v) hvodd.not_two_dvd_nat
  have huodd : Odd (orderOf u) := Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using hu)
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hqu,
    SemidirectProduct.right_inr] using hab u huodd

omit [Finite G] in
private theorem root_mul_odd {z : G} (hz2 : orderOf z = 2)
    (v : centralizer ({z} : Set G)) (hv : Odd (orderOf v)) :
    z ∈ zpowers (z * (v : G)) := by
  have hz : z ^ 2 = 1 := hz2 ▸ pow_orderOf_eq_one z
  have hc : Commute z (v : G) := (mem_centralizer_singleton_iff.mp v.property).symm
  have hp : (z * (v : G)) ^ orderOf v = z := by
    rw [hc.mul_pow, ← Subgroup.coe_pow, pow_orderOf_eq_one, Subgroup.coe_one, mul_one]
    obtain ⟨k, hk⟩ := hv
    rw [hk, pow_add, pow_mul, hz]
    simp
  exact (congrArg (fun x => x ∈ zpowers (z * (v : G))) hp).mp
    (pow_mem (mem_zpowers (z * (v : G))) (orderOf v))

/-- The actual restriction multiplicities against inflated local rows recover
all five coefficients, with zero coefficients for nonprincipal ambient rows. -/
theorem LocalFiveCharacterTable.restriction_section_coefficients
    (T : LocalFiveCharacterTable S α) (h : SylowStructure S)
    {z : G} (hz : z ∈ centerImage S) (hz2 : orderOf z = 2)
    (e : (centralizer ({z} : Set G) ⧸ pPrimeCore 2 (centralizer ({z} : Set G))) ≃*
      LocalFiveGroup S α)
    (he : ∀ s : S, e (involutionCentralizerQuotientMap S hz s) = SemidirectProduct.inl s)
    (w : QuarticCentralIndex S) (hw : (w.1.1 : G) = z)
    (b : PrincipalCongruenceBlockData G)
    (c : GeneralizedDecompositionData {j // j ∈ b.block}) (t : G)
    (μ : centralizer ({z} : Set G) →* ℂ)
    (hc : c.Equation3_1 (fun j g => b.chi j.val (ConjClasses.mk g)) t z μ)
    (ε : Fin 5 ≃ FiveLinearIndex)
    (hε : ∀ i (v : centralizer ({z} : Set G)), Odd (orderOf v) →
      μ v ^ GeneralizedDecompositionData.basicExponent i =
        ε i (e (QuotientGroup.mk' (pPrimeCore 2 _) v)).right)
    (j : b.I) (i : Fin 5) :
    (∑ r : LocalFiveRowIndex S,
      scalarProduct (centralizer ({z} : Set G))
        (fun a => b.chi j (ConjClasses.mk (a : G)))
        (fun a => T.row r (ConjClasses.mk (e (QuotientGroup.mk' (pPrimeCore 2 _) a)))) *
        (localFiveSectionRow S w r (ε i) : ℂ)) =
      if hj : j ∈ b.block then (c.iDz i ⟨j, hj⟩ : ℂ) else 0 := by
  let C := centralizer ({z} : Set G)
  let N := pPrimeCore 2 C
  let q : C →* LocalFiveGroup S α := e.toMonoidHom.comp (QuotientGroup.mk' N)
  let d := CompatibleBrauerBlock.localData b (centralizer ({z} : Set G))
  have hN : Odd (Nat.card N) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := C))
  obtain ⟨E, hE⟩ := T.exists_inflatedBlockIndex h d N hN e
  let θ : ClassFunction C := fun a => b.chi j (ConjClasses.mk (a : G))
  let m : LocalFiveRowIndex S → ℂ := fun r =>
    scalarProduct C θ (fun a => T.row r (ConjClasses.mk (q a)))
  let A : FiveLinearIndex → ℂ := fun k =>
    if hj : j ∈ b.block then (c.iDz (ε.symm k) ⟨j, hj⟩ : ℂ) else 0
  have hexp (v : C) (hv : Odd (orderOf v)) :
      (∑ k : FiveLinearIndex, (∑ r, m r * (localFiveSectionRow S w r k : ℂ)) *
        k (q v).right) = ∑ k, A k * k (q v).right := by
    let zC : C := inclusion (sylow_le_involutionCentralizer S hz) w.1.1
    have hzC : (zC : G) = z := hw
    have hqz : q zC = SemidirectProduct.inl w.1.1 := he w.1.1
    have hp := InvolutionRootRestriction.restriction_projection_on_involution_roots
      b z hz2 j (zC * v) (by simpa only [Subgroup.coe_mul, hzC] using root_mul_odd hz2 v hv)
    dsimp only at hp
    change (∑ l ∈ d.block, scalarProduct C θ
      (fun a => d.chi l (ConjClasses.mk a)) * d.chi l (ConjClasses.mk (zC * v))) = _ at hp
    rw [Finset.sum_subtype d.block (fun _ => Iff.rfl)] at hp
    rw [← E.sum_comp] at hp
    simp only [hE] at hp
    change (∑ r, m r * T.row r (ConjClasses.mk (q (zC * v)))) = _ at hp
    rw [map_mul, hqz] at hp
    have hqv : Odd (orderOf (q v)) := hv.of_dvd_nat (orderOf_map_dvd q v)
    simp_rw [T.section_expansion h w _ (q v) hqv, Finset.mul_sum] at hp
    rw [Finset.sum_comm] at hp
    have hleft : (∑ k : FiveLinearIndex, (∑ r, m r * (localFiveSectionRow S w r k : ℂ)) *
        k (q v).right) =
      ∑ k : FiveLinearIndex, ∑ r, m r * ((localFiveSectionRow S w r k : ℂ) * k (q v).right) := by
      simp only [Finset.sum_mul, mul_assoc]
    rw [hleft, hp]
    by_cases hj : j ∈ b.block
    · rw [if_pos hj]
      change b.chi j (ConjClasses.mk ((zC : G) * (v : G))) = _
      rw [hzC]
      have hcj := hc.2 ⟨j, hj⟩ v hv
      dsimp only at hcj
      rw [hcj]
      simp_rw [hε _ v hv]
      simpa only [A, dif_pos hj, Equiv.symm_apply_apply, q, N, C, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using
        ε.sum_comp (fun k => (c.iDz (ε.symm k) ⟨j, hj⟩ : ℂ) * k (q v).right)
    · simp only [if_neg hj, A, dif_neg hj, zero_mul, Finset.sum_const_zero]
  have huniq := five_coefficients_unique q
    (e.surjective.comp (QuotientGroup.mk'_surjective N)) _ A hexp
  have hi := congrFun huniq (ε i)
  simpa only [m, θ, q, A, C, N, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Equiv.symm_apply_apply] using hi

private theorem scalarProduct_int_sum {H R : Type*} [Fintype H] [Fintype R]
    (f : R → ClassFunction H) (a : R → ℤ) (θ : ClassFunction H) :
    scalarProduct H (fun x => ∑ r, (a r : ℂ) * f r x) θ =
      star (∑ r, scalarProduct H θ (f r) * (a r : ℂ)) := by
  simp only [star_sum, star_mul, star_intCast, scalarProduct_conj]
  simp only [scalarProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Brauer transfer for the genuine local columns, in any enumeration compatible
with the given equation (3.1). No assertion about induced coefficients is an input. -/
theorem LocalFiveCharacterTable.induced_inflatedSectionClassFunction_eq_iDz
    (T : LocalFiveCharacterTable S α) (h : SylowStructure S)
    {z : G} (hz : z ∈ centerImage S) (hz2 : orderOf z = 2)
    (e : (centralizer ({z} : Set G) ⧸ pPrimeCore 2 (centralizer ({z} : Set G))) ≃*
      LocalFiveGroup S α)
    (he : ∀ s : S, e (involutionCentralizerQuotientMap S hz s) = SemidirectProduct.inl s)
    (w : QuarticCentralIndex S) (hw : (w.1.1 : G) = z)
    (b : PrincipalCongruenceBlockData G)
    (c : GeneralizedDecompositionData {j // j ∈ b.block}) (t : G)
    (μ : centralizer ({z} : Set G) →* ℂ)
    (hc : c.Equation3_1 (fun j g => b.chi j.val (ConjClasses.mk g)) t z μ)
    (ε : Fin 5 ≃ FiveLinearIndex)
    (hε : ∀ i (v : centralizer ({z} : Set G)), Odd (orderOf v) →
      μ v ^ GeneralizedDecompositionData.basicExponent i =
        ε i (e (QuotientGroup.mk' (pPrimeCore 2 _) v)).right)
    (i : Fin 5) :
    inducedClassFunction (centralizer ({z} : Set G))
      (T.inflatedSectionClassFunction w (pPrimeCore 2 _) e (ε i)) =
      ∑ j : {j // j ∈ b.block}, (c.iDz i j : ℂ) • ofConjClassFunction (b.chi j.val) := by
  let C := centralizer ({z} : Set G)
  let Φ := T.inflatedSectionClassFunction w (pPrimeCore 2 C) e (ε i)
  have hscalar (j : b.I) : scalarProduct G (inducedClassFunction C Φ)
      (ofConjClassFunction (b.chi j)) =
        if hj : j ∈ b.block then (c.iDz i ⟨j, hj⟩ : ℂ) else 0 := by
    rw [scalarProduct_inducedClassFunction C Φ (ofConjClassFunction_isClassFunction _)]
    rw [Subsingleton.elim C.instFintypeSubtypeMemOfDecidablePred (Fintype.ofFinite C)]
    change scalarProduct C
      (fun a => T.sectionClassFunction w (ε i) (e (QuotientGroup.mk' (pPrimeCore 2 C) a)))
      (fun a => b.chi j (ConjClasses.mk (a : G))) = _
    have hexp : (fun a : C => T.sectionClassFunction w (ε i)
        (e (QuotientGroup.mk' (pPrimeCore 2 C) a))) =
        (fun a => ∑ r : LocalFiveRowIndex S, (localFiveSectionRow S w r (ε i) : ℂ) *
          T.row r (ConjClasses.mk (e (QuotientGroup.mk' (pPrimeCore 2 C) a)))) := by
      funext a
      rw [T.sectionClassFunction_apply]
      apply Finset.sum_congr
      · exact congrArg (@Fintype.elems (LocalFiveRowIndex S)) (Subsingleton.elim _ _)
      · intro r _; rfl
    rw [hexp]
    rw [scalarProduct_int_sum
      (fun r a => T.row r (ConjClasses.mk (e (QuotientGroup.mk' (pPrimeCore 2 C) a))))
      (fun r => localFiveSectionRow S w r (ε i))]
    rw [T.restriction_section_coefficients h hz hz2 e he w hw b c t μ hc ε hε j i]
    split_ifs <;> simp
  have hfull := inducedClassFunction_eq_iDz_full_column C b c i Φ
    (fun j => by simpa only [dif_pos j.property] using hscalar j.val)
    (fun j hj => by simpa only [dif_neg hj] using hscalar j)
  rw [hfull]
  ext g
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  let A : b.I → ℂ := fun j => if hj : j ∈ b.block then (c.iDz i ⟨j, hj⟩ : ℂ) else 0
  have hsum := Finset.sum_subtype (F := Fintype.ofFinite {j // j ∈ b.block}) b.block (fun _ => Iff.rfl)
    (fun j => A j * ofConjClassFunction (b.chi j) g)
  have hzero : (∑ j : b.I, A j * ofConjClassFunction (b.chi j) g) =
      ∑ j ∈ b.block, A j * ofConjClassFunction (b.chi j) g := by
    apply (Finset.sum_subset (Finset.subset_univ _ ) ?_).symm
    intro j _ hj
    simp only [A, dif_neg hj, zero_mul]
  exact hzero.trans (hsum.trans (by
    apply Finset.sum_congr rfl
    intro j _
    simp only [A, dif_pos j.property]))

end Stellmacher.Recognition.LyonsU3Four
