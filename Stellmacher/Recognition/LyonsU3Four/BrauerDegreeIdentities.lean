module

public import Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
public import Stellmacher.Recognition.LyonsU3Four.InvolutionFusion
public import Stellmacher.Recognition.LyonsU3Four.ElementOrders
public import Theory.Character.ModularBlock.InvolutionPairVanishing
public import Theory.Character.InvolutionSum
public import Stellmacher.Recognition.LyonsU3Four.BrauerColumnScalarProducts
public import Stellmacher.Recognition.LyonsU3Four.BrauerLocalInvolutionEvaluation

/-!
# Brauer degree identities for the Lyons columns

The degrees here are values at one of the actual ambient principal-block
characters. Section orthogonality proves their pairing with every local
column is zero. Centrality of Sylow involutions excludes an involution
inverting an order-four element (the dihedral-eight obstruction), so the
involution-weighted degree expression for the order-four column also vanishes.

The root-pairing formula identifies the remaining degree expressions with
pairings in the actual involution centralizer. Genuine local-column induction
and the three local involution classes evaluate those pairings through the
actual odd core. The resulting order identity holds for all five columns, so
every difference has zero degree-denominator expression. Only the quotient
identification and its basis compatibility remain explicit local witnesses.

Source: R. Lyons, *A Characterization of the Group U₃(4)*, Trans. AMS 164
(1972), pp. 381–382, Lemma 4 and Lemma 5(c).
-/

public section
noncomputable section
namespace Stellmacher.Recognition.LyonsU3Four
open scoped BigOperators
open Subgroup ModularBlock PrincipalBlockConstruction Theory.Character
attribute [local instance] Fintype.ofFinite
variable {G : Type*} [Group G] [Finite G]

/-- Lyons's degree-denominator expression, using actual ambient degrees. -/
@[expose] def brauerDegreeSum (b : PrincipalCongruenceBlockData G) (z : G)
    (A : {j // j ∈ b.block} → ℤ) : ℂ :=
  (Nat.card G : ℂ) * ∑ j, b.chi j.val (ConjClasses.mk z) ^ 2 *
    (A j : ℂ) / b.chi j.val (ConjClasses.mk 1)

/-- The regular two-section is orthogonal to a nontrivial involution section. -/
theorem principalBlock_degree_sum_on_involution_section (b : PrincipalCongruenceBlockData G) (z : G) (hz : orderOf z = 2)
    (π : centralizer ({z} : Set G)) (hπ : Odd (orderOf π)) :
    ∑ j : {j // j ∈ b.block}, b.chi j.val (ConjClasses.mk 1) *
      b.chi j.val (ConjClasses.mk (z * (π : G))) = 0 := by
  have hπ' : Odd (orderOf (π : G)) := by
    exact (orderOf_injective (centralizer ({z} : Set G)).subtype Subtype.val_injective π).symm ▸ hπ
  have hcomm : Commute z (π : G) :=
    (Subgroup.mem_centralizer_singleton_iff.mp π.property).symm
  have ho : orderOf (z * (π : G)) = 2 * orderOf (π : G) := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hz]; exact hπ'.coprime_two_left), hz]
  have hs := SectionOrthogonality.principalBlock_column_eq_zero_of_not_mem_twoSection
    b 1 ⟨0, by simp⟩ (z * (π : G)) (by
      rintro ⟨v, hv, _, hc⟩
      simp only [one_mul] at hc
      obtain ⟨g, hg⟩ := isConj_iff.mp hc
      have he : orderOf (z * (π : G)) = orderOf v := by
        rw [← hg]
        exact (MulAut.conj g).orderOf_eq v
      rw [← he, ho] at hv
      exact (Nat.not_even_iff_odd.mpr hv) (even_two_mul _))
  have hs' := congrArg star hs
  simp only [star_sum, star_mul, star_conjChar_apply_inv (b.complete.1 _).1,
    inv_one, inv_inv, star_zero] at hs'
  rw [Finset.sum_subtype b.block (fun _ => Iff.rfl)] at hs'
  simpa only [mul_comm] using hs'



/-- Independence needs only the order of the actual homomorphism, even when
its source has a nontrivial odd core. -/
theorem fivePowers_independent_on_odd {H : Type*} [Group H] [Finite H] (μ : H →* ℂ) (hμ : orderOf μ = 5) :
    LinearIndependent ℂ (fun i : Fin 5 =>
      fun v : {v : H // Odd (orderOf v)} => μ v.val ^ GeneralizedDecompositionData.basicExponent i) := by
  classical
  have hinj : Function.Injective (fun i : Fin 5 => μ ^ GeneralizedDecompositionData.basicExponent i) := by
    intro i j hij
    have hi : GeneralizedDecompositionData.basicExponent i < orderOf μ := by
      rw [hμ]; fin_cases i <;> decide
    have hj : GeneralizedDecompositionData.basicExponent j < orderOf μ := by
      rw [hμ]; fin_cases j <;> decide
    have he := pow_injOn_Iio_orderOf hi hj hij
    exact (show Function.Injective GeneralizedDecompositionData.basicExponent by decide) he
  have hli := (linearIndependent_monoidHom H ℂ).comp _ hinj
  apply Fintype.linearIndependent_iffₛ.mpr
  intro a b hab
  apply Fintype.linearIndependent_iffₛ.mp hli a b
  funext x
  obtain ⟨u, v, ⟨n, hn⟩, hv, _, rfl⟩ := exists_commuting_prime_parts 2 Nat.prime_two x
  have hμu : μ u = 1 := by
    have hp5 : μ u ^ 5 = 1 := by
      have hh := DFunLike.congr_fun (show μ ^ 5 = 1 by rw [← hμ]; exact pow_orderOf_eq_one μ) u
      simpa using hh
    have hp2 : μ u ^ (2 ^ n) = 1 := by rw [← map_pow, hn, map_one]
    apply orderOf_eq_one_iff.mp
    apply Nat.dvd_one.mp
    have hh := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hp5) (orderOf_dvd_of_pow_eq_one hp2)
    simpa only [((show Nat.Coprime 5 2 by decide).pow_right n).gcd_eq_one] using hh
  have hvodd : Odd (orderOf v) := Nat.coprime_two_left.mp (Nat.prime_two.coprime_iff_not_dvd.mpr hv)
  have he := congrFun hab ⟨v, hvodd⟩
  simpa [map_mul, hμu] using he

/-- Lemma 5(c) for all five involution columns, with the actual degrees. -/
theorem degree_iDz_eq_zero (b : PrincipalCongruenceBlockData G)
    (c : GeneralizedDecompositionData {j // j ∈ b.block}) (t z : G)
    (hz : orderOf z = 2) (μ : centralizer ({z} : Set G) →* ℂ)
    (hμ : orderOf μ = 5)
    (heq : c.Equation3_1 (fun j g => b.chi j.val (ConjClasses.mk g)) t z μ)
    (i : Fin 5) :
    ∑ j, b.chi j.val (ConjClasses.mk 1) * (c.iDz i j : ℂ) = 0 := by
  classical
  apply Fintype.linearIndependent_iffₛ.mp (fivePowers_independent_on_odd μ hμ)
    (fun i => ∑ j, b.chi j.val (ConjClasses.mk 1) * (c.iDz i j : ℂ)) (fun _ => 0) _ i
  funext v
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, zero_mul, Finset.sum_const_zero]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, ← heq.2 _ v.val v.property]
  exact principalBlock_degree_sum_on_involution_section b z hz v.val v.property

/-- Lemma 5(c) for the order-four column. -/
theorem degree_dT_eq_zero (b : PrincipalCongruenceBlockData G)
    (c : GeneralizedDecompositionData {j // j ∈ b.block}) (t z : G)
    (ht : orderOf t = 4) (μ : centralizer ({z} : Set G) →* ℂ)
    (heq : c.Equation3_1 (fun j g => b.chi j.val (ConjClasses.mk g)) t z μ) :
    ∑ j, b.chi j.val (ConjClasses.mk 1) * (c.dT j : ℂ) = 0 := by
  have hs := SectionOrthogonality.principalBlock_column_eq_zero_of_not_isConj
    b t 1 ⟨2, by simpa [ht] using pow_orderOf_eq_one t⟩ ⟨0, by simp⟩ (by
      intro hc
      obtain ⟨g, hg⟩ := isConj_iff.mp hc
      have he : t = 1 := (MulAut.conj g).injective (by simpa using hg)
      simp [he] at ht)
  simp only [star_conjChar_apply_inv (b.complete.1 _).1, inv_one] at hs
  rw [Finset.sum_subtype b.block (fun _ => Iff.rfl)] at hs
  simpa only [heq.at_t, mul_comm] using hs

/-- Lemma 4(a). The supplied Sylow has no dihedral subgroup of order eight. -/
theorem brauerDegreeSum_dT_eq_zero (S : Sylow 2 G) (h : SylowStructure S)
    (b : PrincipalCongruenceBlockData G)
    (c : GeneralizedDecompositionData {j // j ∈ b.block}) (t z : G)
    (ht : orderOf t = 4) (hz : orderOf z = 2)
    (μ : centralizer ({z} : Set G) →* ℂ)
    (heq : c.Equation3_1 (fun j g => b.chi j.val (ConjClasses.mk g)) t z μ) :
    brauerDegreeSum b z c.dT = 0 := by
  have hz2 : z * z = 1 := by simpa only [hz, pow_two] using pow_orderOf_eq_one z
  have ht4 : ∃ n : ℕ, t ^ (2 ^ n) = 1 :=
    ⟨2, by simpa [ht] using pow_orderOf_eq_one t⟩
  have hs := InvolutionPairVanishing.principalBlock_pairSum_eq_zero_of_twoSection_support
    b z t hz2 ht4 (by
      intro y hy hc
      apply classSumPairCount_eq_zero_on_twoSection t z ht4 hz2 _ y hy hc
      intro u hu
      apply order_four_not_inverted_by_square_one S h ht
      obtain ⟨g, rfl⟩ := isConj_iff.mp hu
      simpa only [map_pow, map_one, MulAut.conj_apply] using
        congrArg (MulAut.conj g) (show z ^ 2 = 1 by simpa only [pow_two] using hz2))
  rw [Finset.sum_subtype b.block (fun _ => Iff.rfl)] at hs
  unfold brauerDegreeSum
  rw [show (∑ j : {j // j ∈ b.block}, b.chi j.val (ConjClasses.mk z) ^ 2 *
      (c.dT j : ℂ) / b.chi j.val (ConjClasses.mk 1)) = 0 by
        simpa only [heq.at_t] using hs, mul_zero]

/-- Linearity for the differences of columns used in Lemma 4(b). -/
theorem brauerDegreeSum_sub (b : PrincipalCongruenceBlockData G) (z : G)
    (A B : {j // j ∈ b.block} → ℤ) :
    brauerDegreeSum b z (A - B) = brauerDegreeSum b z A - brauerDegreeSum b z B := by
  simp only [brauerDegreeSum, Pi.sub_apply, Int.cast_sub, mul_sub, sub_div,
    Finset.sum_sub_distrib]

/-- Brauer's degree expression is the genuine local involution-pair pairing
multiplied by the square of the actual centralizer order. The local function
must have root support and induce to the specified ambient column. -/
theorem brauerDegreeSum_eq_centralizer_sq_mul_pairing [IsSimpleGroup G] (S : Sylow 2 G) (h : SylowStructure S)
    (b : PrincipalCongruenceBlockData G) (z : G) (hz : orderOf z = 2)
    (A : {j // j ∈ b.block} → ℤ)
    (Φ : ClassFunction (centralizer ({z} : Set G)))
    (hsupport : ∀ a : centralizer ({z} : Set G), z ∉ zpowers (a : G) → Φ a = 0)
    (hind : inducedClassFunction (centralizer ({z} : Set G)) Φ =
      ∑ j : {j // j ∈ b.block}, (A j : ℂ) • ofConjClassFunction (b.chi j.val)) :
    brauerDegreeSum b z A = (Nat.card (centralizer ({z} : Set G)) : ℂ)^2 *
      scalarProduct (centralizer ({z} : Set G)) Φ (fun a => (involutionPairCount a : ℂ)) := by
  have hirr (j : {j // j ∈ b.block}) :
      IsIrreducibleCharacter (ofConjClassFunction (b.chi j.val)) := by
    obtain ⟨n, ρ, hρ⟩ := (b.complete.1 j.val).1
    refine ⟨n, ρ, (irreducible_iff_character_norm_one ρ).mpr ?_, ?_⟩
    · simpa [hρ] using (b.complete.1 j.val).2
    · rw [hρ]; rfl
  have hi := scalarProduct_induced_involutionPairCount z hz Φ hsupport
  rw [hind, scalarProduct_expansion_involutionPairCount _ hirr] at hi
  have hs (j : {j // j ∈ b.block}) := involutionSum_of_fusion z hz
    (fun u hu => involutions_isConj S h hu hz)
    (ofConjClassFunction (b.chi j.val)) (ofConjClassFunction_isClassFunction _)
  simp_rw [hs] at hi
  have hi' : (Nat.card G : ℂ)⁻¹ * ∑ j : {j // j ∈ b.block},
      ((Nat.card G : ℂ) / Nat.card (centralizer ({z} : Set G)) *
        b.chi j.val (ConjClasses.mk z)) ^ 2 * (A j : ℂ) /
          b.chi j.val (ConjClasses.mk 1) =
      scalarProduct (centralizer ({z} : Set G)) Φ (fun a => (involutionPairCount a : ℂ)) := by
    convert hi using 1
    all_goals congr <;> exact Subsingleton.elim _ _
  rw [← hi']
  unfold brauerDegreeSum
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hg : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := G)).ne'
  have hc : (Nat.card (centralizer ({z} : Set G)) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := centralizer ({z} : Set G))).ne'
  field_simp

/-- Assemble the actual centralizer-order identity for every local column.
Root support is proved through the odd core; the two remaining inputs are the
induction identity and the evaluated local pairing. -/
theorem brauerDegreeSum_iDz_of_local_pairing [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S)
    (b : PrincipalCongruenceBlockData G)
    (c : GeneralizedDecompositionData {j // j ∈ b.block})
    (β : MulAut S) (hβ : orderOf β = 15)
    (α : FiveComplement →* MulAut S)
    (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ))
    {z : G} (hz : z ∈ centerImage S) (hz2 : orderOf z = 2)
    (e : (centralizer ({z} : Set G) ⧸ pPrimeCore 2 (centralizer ({z} : Set G))) ≃*
      LocalFiveGroup S α)
    (he : ∀ s : S, e (involutionCentralizerQuotientMap S hz s) = SemidirectProduct.inl s)
    (w : QuarticCentralIndex S) (hw : (w.1.1 : G) = z)
    (T : LocalFiveCharacterTable S α) (ε : Fin 5 ≃ FiveLinearIndex)
    (hind : ∀ i : Fin 5,
      inducedClassFunction (centralizer ({z} : Set G))
        (T.inflatedSectionClassFunction w (pPrimeCore 2 _) e (ε i)) =
          ∑ j : {j // j ∈ b.block}, (c.iDz i j : ℂ) • ofConjClassFunction (b.chi j.val))
    (hpair : ∀ j : FiveLinearIndex,
      (Nat.card (centralizer (centerImage S : Set G)) : ℂ)^2 *
        scalarProduct (centralizer ({z} : Set G))
          (T.inflatedSectionClassFunction w (pPrimeCore 2 _) e j)
          (fun a => (involutionPairCount a : ℂ)) =
        128 * (Nat.card (centralizer ({z} : Set G)) : ℂ))
    (i : Fin 5) :
    (Nat.card (centralizer (centerImage S : Set G)) : ℂ)^2 *
      brauerDegreeSum b z (c.iDz i) =
        128 * (Nat.card (centralizer ({z} : Set G)) : ℂ)^3 := by
  rw [brauerDegreeSum_eq_centralizer_sq_mul_pairing S h b z hz2 (c.iDz i)
    (T.inflatedSectionClassFunction w (pPrimeCore 2 _) e (ε i))
    (fun a ha => T.inflatedSectionClassFunction_eq_zero_of_not_root
      h β hβ hα hz e he w hw (ε i) a ha) (hind i)]
  calc
    _ = (Nat.card (centralizer ({z} : Set G)) : ℂ)^2 *
        ((Nat.card (centralizer (centerImage S : Set G)) : ℂ)^2 *
          scalarProduct (centralizer ({z} : Set G))
            (T.inflatedSectionClassFunction w (pPrimeCore 2 _) e (ε i))
            (fun a => (involutionPairCount a : ℂ))) := by ring
    _ = _ := by rw [hpair]; ring

/-- Equal centralizer-order identities force every column difference to have
zero degree-denominator expression, including Lyons's columns zero and one. -/
theorem brauerDegreeSum_iDz_sub_eq_zero_of_order_identities
    (S : Sylow 2 G) (b : PrincipalCongruenceBlockData G) (z : G)
    (c : GeneralizedDecompositionData {j // j ∈ b.block})
    (horder : ∀ i : Fin 5,
      (Nat.card (centralizer (centerImage S : Set G)) : ℂ)^2 *
        brauerDegreeSum b z (c.iDz i) =
          128 * (Nat.card (centralizer ({z} : Set G)) : ℂ)^3)
    (i k : Fin 5) :
    brauerDegreeSum b z (c.iDz i - c.iDz k) = 0 := by
  rw [brauerDegreeSum_sub, sub_eq_zero]
  have hD : (Nat.card (centralizer (centerImage S : Set G)) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := centralizer (centerImage S : Set G))).ne'
  exact mul_left_cancel₀ (pow_ne_zero 2 hD) ((horder i).trans (horder k).symm)


/-- Lyons's Lemma 4(c), for every genuine local column and the actual ambient
character degrees. The local quotient and basic-character compatibility are
the only transport witnesses: induction and local involution counts are proved. -/
theorem brauerDegreeSum_iDz_order_identity [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S)
    (b : PrincipalCongruenceBlockData G)
    (c : GeneralizedDecompositionData {j // j ∈ b.block})
    (β : MulAut S) (hβ : orderOf β = 15)
    (α : FiveComplement →* MulAut S)
    (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ))
    {z : G} (hz : z ∈ centerImage S) (hz2 : orderOf z = 2)
    (e : (centralizer ({z} : Set G) ⧸ pPrimeCore 2 (centralizer ({z} : Set G))) ≃*
      LocalFiveGroup S α)
    (he : ∀ s : S, e (involutionCentralizerQuotientMap S hz s) = SemidirectProduct.inl s)
    (w : QuarticCentralIndex S) (hw : (w.1.1 : G) = z)
    (T : LocalFiveCharacterTable S α)
    (t : G) (μ : centralizer ({z} : Set G) →* ℂ)
    (hc : c.Equation3_1 (fun j g => b.chi j.val (ConjClasses.mk g)) t z μ)
    (ε : Fin 5 ≃ FiveLinearIndex)
    (hε : ∀ i (π : centralizer ({z} : Set G)), Odd (orderOf π) →
      μ π ^ GeneralizedDecompositionData.basicExponent i =
        ε i (e (QuotientGroup.mk' (pPrimeCore 2 _) π)).right)
    (i : Fin 5) :
    (Nat.card (centralizer (centerImage S : Set G)) : ℂ)^2 *
      brauerDegreeSum b z (c.iDz i) =
        128 * (Nat.card (centralizer ({z} : Set G)) : ℂ)^3 := by
  have hz1 : z ≠ 1 := by intro hh; simp [hh] at hz2
  refine brauerDegreeSum_iDz_of_local_pairing S h b c β hβ α hα hz hz2 e he w hw T ε
    (T.inducedSection_eq_iDz_column h hz hz1 e he w hw b c t μ hc ε hε) ?_ i
  intro j
  convert brauerLocalInvolutionPairing h β hβ hα hz e he w hw T j using 1
  congr
  exact Subsingleton.elim _ _

/-- Lyons's Lemma 4(b), including the difference of columns zero and one.
In fact every pair of the five local columns has the same degree sum. -/
theorem brauerDegreeSum_iDz_sub_eq_zero [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S)
    (b : PrincipalCongruenceBlockData G)
    (c : GeneralizedDecompositionData {j // j ∈ b.block})
    (β : MulAut S) (hβ : orderOf β = 15)
    (α : FiveComplement →* MulAut S)
    (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ))
    {z : G} (hz : z ∈ centerImage S) (hz2 : orderOf z = 2)
    (e : (centralizer ({z} : Set G) ⧸ pPrimeCore 2 (centralizer ({z} : Set G))) ≃*
      LocalFiveGroup S α)
    (he : ∀ s : S, e (involutionCentralizerQuotientMap S hz s) = SemidirectProduct.inl s)
    (w : QuarticCentralIndex S) (hw : (w.1.1 : G) = z)
    (T : LocalFiveCharacterTable S α)
    (t : G) (μ : centralizer ({z} : Set G) →* ℂ)
    (hc : c.Equation3_1 (fun j g => b.chi j.val (ConjClasses.mk g)) t z μ)
    (ε : Fin 5 ≃ FiveLinearIndex)
    (hε : ∀ i (π : centralizer ({z} : Set G)), Odd (orderOf π) →
      μ π ^ GeneralizedDecompositionData.basicExponent i =
        ε i (e (QuotientGroup.mk' (pPrimeCore 2 _) π)).right)
    (i k : Fin 5) :
    brauerDegreeSum b z (c.iDz i - c.iDz k) = 0 := by
  exact brauerDegreeSum_iDz_sub_eq_zero_of_order_identities S b z c
    (brauerDegreeSum_iDz_order_identity S h b c β hβ α hα hz hz2 e he w hw T t μ hc ε hε) i k

end Stellmacher.Recognition.LyonsU3Four
