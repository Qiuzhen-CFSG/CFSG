module

public import Stellmacher.Recognition.LyonsU3Four.LocalCentralizerBlocks
public import Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
public import Theory.Character.ModularBlock.InvolutionBrauerExpansion
public import Theory.Character.TwoSectionMassBudget

/-!
# Local models and proved inputs for the ambient Lyons sections

The actual odd-core quotient and its order-five linear generator determine the
ordered local basis. `FiveSectionModel.BrauerData` records a genuine modular
family in these coordinates, not arbitrary functions of degree one. These data
are shared inputs to the independent expansion, Gram and mass calculations.

The complex expansions come from compatible local principal blocks. From an
integral expansion we prove the order-four column norm, both principal-row
normalizations, and the order-four section mass. The two distinct nonidentity
sections have total mass strictly less than one because the omitted identity
section has positive mass. Thus their combined mass formula will imply (3.3).

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), pp. 373--374,
equations (3.1)--(3.3).
-/

public section
noncomputable section

namespace Stellmacher.Recognition.LyonsU3Four

open Subgroup ModularBlock PrincipalBlockConstruction
open ModularBlock.TwoSectionContribution
attribute [local instance] Fintype.ofFinite Classical.propDecidable

variable {G : Type*} [Group G]

/-- The square of an order-four Sylow element is a nonidentity ambient central
involution.  This is the precise input needed by the local involution block. -/
public theorem orderFour_square_mem_centerImage
    (S : Sylow 2 G) (h : SylowStructure S) (t : S) (ht : orderOf t = 4) :
    (t : G) ^ 2 ∈ centerImage S ∧ (t : G) ^ 2 ≠ 1 := by
  have hsq : t ^ 2 ∈ Subgroup.center S := square_mem_center S h t
  have hz : (t : G) ^ 2 ∈ centerImage S := by
    refine ⟨t ^ 2, hsq, rfl⟩
  refine ⟨hz, ?_⟩
  intro he
  have heS : t ^ 2 = 1 := Subtype.ext he
  have hdvd : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one heS
  rw [ht] at hdvd
  omega

variable {G : Type*} [Group G] [Finite G]

/-- Actual complex coefficients for the order-four and involution sections.
For every principal-block row, the displayed equations are the genuine local
Brauer expansions obtained from the transported local principal blocks. -/
public theorem exists_complex_ambient_section_columns
    (S : Sylow 2 G) (h : SylowStructure S) (d : LocalCentralizerData S)
    (b : PrincipalCongruenceBlockData G) (t : S) (ht : orderOf t = 4) :
    ∃ aT : Cartan.PrincipalDecompositionData
        (CompatibleBrauerBlock.localData b
          (Subgroup.centralizer ({(t : G)} : Set G))) 1,
      ∃ aZ : Cartan.PrincipalDecompositionData
        (CompatibleBrauerBlock.localData b
          (Subgroup.centralizer ({(t : G)^2} : Set G))) 5,
      ∃ cT : {j // j ∈ b.block} → ℂ,
      ∃ cZ : Fin 5 → {j // j ∈ b.block} → ℂ,
      (∀ j (v : Subgroup.centralizer ({(t : G)} : Set G)), Odd (orderOf v) →
        b.chi j.1 (ConjClasses.mk ((t : G) * (v : G))) =
          cT j * BrauerCharacter.value
            (CompatibleBrauerBlock.localData b
              (Subgroup.centralizer ({(t : G)} : Set G)))
            (aT.family.rep 0) v) ∧
      (∀ j (v : Subgroup.centralizer ({(t : G)^2} : Set G)), Odd (orderOf v) →
        b.chi j.1 (ConjClasses.mk (((t : G)^2) * (v : G))) =
          ∑ i, cZ i j * BrauerCharacter.value
            (CompatibleBrauerBlock.localData b
              (Subgroup.centralizer ({(t : G)^2} : Set G)))
            (aZ.family.rep i) v) := by
  let z : G := (t : G) ^ 2
  have hz := orderFour_square_mem_centerImage S h t ht
  let lt := CompatibleBrauerBlock.localData b
    (Subgroup.centralizer ({(t : G)} : Set G))
  let lz := CompatibleBrauerBlock.localData b
    (Subgroup.centralizer ({z} : Set G))
  obtain ⟨aT0, hTdeg, hTcartan⟩ := orderFourCentralizer_principal_cartan S d t ht lt
  obtain ⟨aZ0, hZdeg, hZcartan⟩ := involutionCentralizer_principal_cartan S h d hz.1 hz.2 lz
  let χ : {j // j ∈ b.block} → ClassFunction G :=
    fun j => fun g => b.chi j.1 (ConjClasses.mk g)
  have hm (j : {j // j ∈ b.block}) :
      ∃ i ∈ b.block, ∀ g, χ j g = b.chi i (ConjClasses.mk g) :=
    ⟨j.1, j.2, fun g => rfl⟩
  have htpow : ∃ n : ℕ, (t : G) ^ (2 ^ n) = 1 := by
    refine ⟨2, ?_⟩
    change ((t : G) ^ 4) = 1
    have htG : orderOf (t : G) = 4 := (Subgroup.orderOf_coe t).trans ht
    rw [← htG]
    exact pow_orderOf_eq_one (t : G)
  have hzpow : ∃ n : ℕ, z ^ (2 ^ n) = 1 := by
    refine ⟨1, ?_⟩
    dsimp [z]
    rw [← pow_mul, show 2 * 2 = 4 by norm_num]
    have htG : orderOf (t : G) = 4 := (Subgroup.orderOf_coe t).trans ht
    rw [← htG]
    exact pow_orderOf_eq_one (t : G)
  choose cT hcT _ using fun j =>
    exists_complex b (χ j) (hm j) (t : G) htpow aT0
  choose cZ hcZ _ using fun j =>
    exists_complex b (χ j) (hm j) z hzpow aZ0
  refine ⟨aT0, aZ0, (fun j => cT j 0), (fun i j => cZ j i), ?_, ?_⟩
  · intro j v hv
    simpa [χ, lt] using hcT j v hv
  · intro j v hv
    simpa [χ, z, lz, Fin.sum_univ_succ] using hcZ j v hv

/-- Actual odd-core quotient coordinates and a chosen generator of its five
linear characters. -/
structure FiveSectionModel (S : Sylow 2 G) (z : G) where
  central : z ∈ centerImage S
  β : MulAut S
  order_β : orderOf β = 15
  α : FiveComplement →* MulAut S
  action : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ)
  quotientEquiv :
    (centralizer ({z} : Set G) ⧸ pPrimeCore 2 (centralizer ({z} : Set G))) ≃*
      LocalFiveGroup S α
  preservesSylow : ∀ s : S,
    quotientEquiv (involutionCentralizerQuotientMap S central s) = SemidirectProduct.inl s
  generator : FiveLinearIndex
  order_generator : orderOf generator = 5
  enumeration : Fin 5 ≃ FiveLinearIndex
  enumeration_apply : ∀ i,
    enumeration i = generator ^ GeneralizedDecompositionData.basicExponent i

namespace FiveSectionModel
variable {S : Sylow 2 G} {z : G} (M : FiveSectionModel S z)

/-- The actual order-five character, inflated through the centralizer's odd core. -/
def mu : centralizer ({z} : Set G) →* ℂ :=
  M.generator.comp (SemidirectProduct.rightHom.comp
    (M.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 _))))

omit [Finite G] in
@[simp] theorem mu_apply (v : centralizer ({z} : Set G)) :
    M.mu v = M.generator (M.quotientEquiv (QuotientGroup.mk' (pPrimeCore 2 _) v)).right := by rfl

omit [Finite G] in
/-- Inflation through the surjective actual quotient preserves the order. -/
theorem order_mu : orderOf M.mu = 5 := by
  let q := SemidirectProduct.rightHom.comp
    (M.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 _)))
  have hq : Function.Surjective q :=
    SemidirectProduct.rightHom_surjective.comp
      (M.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _))
  have hi : Function.Injective (MonoidHom.compHom' (P := ℂ) q) := by
    intro χ ψ he
    ext x
    obtain ⟨v, rfl⟩ := hq x
    exact DFunLike.congr_fun he v
  exact (orderOf_injective (MonoidHom.compHom' q) hi M.generator).trans M.order_generator

/-- Genuine local Brauer data expressed in Lyons's ordered powers. -/
structure BrauerData (b : PrincipalCongruenceBlockData G) where
  decomposition : Cartan.PrincipalDecompositionData
    (CompatibleBrauerBlock.localData b (centralizer ({z} : Set G))) 5
  degree : ∀ i, decomposition.family.degree i = 1
  cartan : ∀ i k, decomposition.cartan i k = 4 * (3 + if i = k then 1 else 0)
  value : ∀ i (v : centralizer ({z} : Set G)), Odd (orderOf v) →
    BrauerCharacter.value (CompatibleBrauerBlock.localData b _) (decomposition.family.rep i) v =
      M.mu v ^ GeneralizedDecompositionData.basicExponent i

end FiveSectionModel

attribute [local instance] Fintype.ofFinite Classical.propDecidable

/-- Uniqueness in the genuine Brauer family fixes the principal involution row. -/
theorem ambient_section_principal_iDz
    {S : Sylow 2 G} (b : PrincipalCongruenceBlockData G) (t z : G)
    (M : FiveSectionModel S z) (a : M.BrauerData b)
    (c : GeneralizedDecompositionData {j // j ∈ b.block})
    (he : c.Equation3_1 (fun j g => b.chi j.1 (ConjClasses.mk g)) t z M.mu)
    (i : Fin 5) : c.iDz i ⟨b.principal, b.principal_mem⟩ = if i = 0 then 1 else 0 := by
  let p : {j // j ∈ b.block} := ⟨b.principal, b.principal_mem⟩
  have heq : (fun k => (c.iDz k p : ℂ)) = (fun k => if k = 0 then (1 : ℂ) else 0) := by
    apply TwistedBrauerExpansion.coefficients_unique _ a.decomposition
    intro v hv
    simp_rw [a.value _ v hv]
    rw [← he.2 p v hv]
    simp [p, b.principal_eq, GeneralizedDecompositionData.basicExponent]
  have hi := congrFun heq i
  exact_mod_cast hi

/-- Every principal-block row is an actual irreducible ambient character. -/
theorem ambient_section_character_irreducible
    (b : PrincipalCongruenceBlockData G) (j : {i // i ∈ b.block}) :
    IsIrreducibleCharacter (fun g => b.chi j.1 (ConjClasses.mk g)) := by
  obtain ⟨n, ρ, hρ⟩ := (b.complete.1 j.val).1
  refine ⟨n, ρ, (irreducible_iff_character_norm_one ρ).mpr ?_, ?_⟩
  · simpa [hρ] using (b.complete.1 j.val).2
  · funext g
    rw [hρ]
    rfl

/-- The singleton coefficient column has squared norm sixteen. -/
theorem ambient_section_tt
    (S : Sylow 2 G) (d : LocalCentralizerData S)
    (b : PrincipalCongruenceBlockData G) (t : S) (ht : orderOf t = 4)
    (μ : centralizer ({(t : G)^2} : Set G) →* ℂ)
    (c : GeneralizedDecompositionData {j // j ∈ b.block})
    (he : c.Equation3_1 (fun j g => b.chi j.1 (ConjClasses.mk g)) (t : G) ((t : G)^2) μ) :
    GeneralizedDecompositionData.columnInner c.dT c.dT = 16 := by
  have hn := ambient_orderFour_column_norm S d t ht b
  rw [Finset.sum_subtype b.block (fun _ => Iff.rfl)] at hn
  simp_rw [GeneralizedDecompositionData.Equation3_1.at_t c he] at hn
  rw [GeneralizedDecompositionData.columnInner_complex] at hn
  exact_mod_cast hn

/-- The principal character normalizes the order-four column to one. -/
theorem ambient_section_principal_dT
    (b : PrincipalCongruenceBlockData G) (t z : G)
    (μ : centralizer ({z} : Set G) →* ℂ)
    (c : GeneralizedDecompositionData {j // j ∈ b.block})
    (he : c.Equation3_1 (fun j g => b.chi j.1 (ConjClasses.mk g)) t z μ) :
    c.dT ⟨b.principal, b.principal_mem⟩ = 1 := by
  have hp := GeneralizedDecompositionData.Equation3_1.at_t c he ⟨b.principal, b.principal_mem⟩
  simp only [b.principal_eq, ordinaryPrincipalCharacter_apply] at hp
  exact_mod_cast hp.symm

/-- The actual order-four section mass is the coefficient square divided by sixteen. -/
theorem ambient_orderFour_mass
    (S : Sylow 2 G) (d : LocalCentralizerData S)
    (b : PrincipalCongruenceBlockData G) (t : S) (ht : orderOf t = 4)
    (μ : centralizer ({(t : G)^2} : Set G) →* ℂ)
    (c : GeneralizedDecompositionData {j // j ∈ b.block})
    (he : c.Equation3_1 (fun j g => b.chi j.1 (ConjClasses.mk g)) (t : G) ((t : G)^2) μ)
    (j : {i // i ∈ b.block}) :
    Theory.Character.twoSectionMass (fun g => b.chi j.1 (ConjClasses.mk g)) (t : G) =
      (c.dT j : ℝ)^2 / 16 := by
  let C := centralizer ({(t : G)} : Set G)
  let l := CompatibleBrauerBlock.localData b C
  obtain ⟨a, hd, _⟩ := orderFourCentralizer_principal_cartan S d t ht l
  have hN : Odd (Nat.card (pPrimeCore 2 C)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := C))
  have hQ : IsPGroup 2 (C ⧸ pPrimeCore 2 C) :=
    IsPGroup.of_card (n := 4) (by simpa using d.orderFour_quotient_card t ht)
  obtain ⟨n, hn⟩ := S.isPGroup' t
  have hm := TwoSectionContribution.mass_of_oddNormal_twoGroup b
    (fun g => b.chi j.1 (ConjClasses.mk g)) ⟨j.1, j.2, fun _ => rfl⟩
    (t : G) ⟨n, congrArg Subtype.val hn⟩ a (pPrimeCore 2 C) hN hQ hd (c.dT j)
    (GeneralizedDecompositionData.Equation3_1.at_t c he j)
  have hcard : Nat.card (C ⧸ pPrimeCore 2 C) = 16 := d.orderFour_quotient_card t ht
  change Theory.Character.twoSectionMass _ _ = _ / (Nat.card (C ⧸ pPrimeCore 2 C) : ℝ) at hm
  simpa only [hcard, Nat.cast_ofNat] using hm

/-- The two sections at an order-four element and its square have total mass below one. -/
theorem ambient_two_section_mass_lt_one
    (b : PrincipalCongruenceBlockData G) (t : G) (ht : orderOf t = 4)
    (j : {i // i ∈ b.block}) :
    Theory.Character.twoSectionMass (fun g => b.chi j.1 (ConjClasses.mk g)) t +
      Theory.Character.twoSectionMass (fun g => b.chi j.1 (ConjClasses.mk g)) (t^2) < 1 := by
  have ht4 : t ^ 4 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hz : orderOf (t ^ 2) = 2 := by rw [orderOf_pow, ht]; decide
  let r : Fin 2 → G := ![t, t^2]
  have hr : ∀ i, ∃ k : ℕ, r i ^ (2^k) = 1 := by
    intro i
    fin_cases i
    · exact ⟨2, ht4⟩
    · exact ⟨1, by change (t^2)^2 = 1; simpa only [← pow_mul] using ht4⟩
  have hne : ∀ i, r i ≠ 1 := by
    intro i
    fin_cases i
    · intro he
      have : t = 1 := he
      simp [this] at ht
    · intro he
      have : t ^ 2 = 1 := he
      simp [this] at hz
  have hsep : ∀ i j, IsConj (r i) (r j) → i = j := by
    intro i j hij
    have hord : orderOf (r i) = orderOf (r j) := by
      obtain ⟨g, hg⟩ := isConj_iff.mp hij
      exact (MulAut.conj g).orderOf_eq (r i) |>.symm.trans (congrArg orderOf hg)
    fin_cases i <;> fin_cases j <;> simp_all [r]
  simpa only [Fin.sum_univ_two, r, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] using
    Theory.Character.sum_twoSectionMass_lt_one r hr hne hsep
      (ambient_section_character_irreducible b j)

/-- The combined mass identity gives the strict integer contribution inequality. -/
theorem ambient_contributionBound_of_mass_identity
    (b : PrincipalCongruenceBlockData G) (t : G) (ht : orderOf t = 4)
    (c : GeneralizedDecompositionData {j // j ∈ b.block})
    (hm : ∀ j : {i // i ∈ b.block},
      Theory.Character.twoSectionMass (fun g => b.chi j.1 (ConjClasses.mk g)) t +
        Theory.Character.twoSectionMass (fun g => b.chi j.1 (ConjClasses.mk g)) (t^2) =
          (c.contribution j : ℝ) / 64) : c.ContributionBound := by
  intro j
  have hb := ambient_two_section_mass_lt_one b t ht j
  rw [hm j] at hb
  have hh : (c.contribution j : ℝ) < 64 := by linarith
  exact_mod_cast hh

end Stellmacher.Recognition.LyonsU3Four
