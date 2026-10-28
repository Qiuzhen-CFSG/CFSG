module

public import Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
public import Stellmacher.Recognition.LyonsU3Four.LocalCentralizerBlocks
public import Stellmacher.Recognition.LyonsU3Four.SylowCharacterRestrictionBounds
public import Stellmacher.Recognition.LyonsU3Four.AmbientGaloisRealization
public import Theory.Character.IrreducibleDegrees
public import Stellmacher.Recognition.LyonsU3Four.AmbientIntegralSections
public import Theory.GroupTheory.CharacteristicCentralizerSylow

/-!
# Realization of the ambient Lyons decomposition constraints

The rows are the genuine irreducible characters of the ambient principal block,
with their actual positive degrees and section values. From the original Sylow
structure and local centralizer data, `exists_ambient_decomposition` constructs
all six integral columns and discharges the pattern, degree, order and prime
constraints used by the independent Table I elimination.

The integral section construction supplies expansions, Gram identities and the
strict contribution bound. Actual Sylow restriction multiplicities give the
congruence and degree bounds. Whole-character Galois transport gives the column
symmetry and separated-row prime bounds. Brauer's degree identities, transported
through the actual odd-core quotient and its ordered five-character basis, give
the rational weighted-column identities. No triviality of local odd cores is
assumed. Final adapters turn degree uniqueness and the surviving column value
from Table I into character rationality and the centralizer formula at every
nonidentity element of the Sylow center.

Source: R. Lyons, *A Characterization of the Group U₃(4)*, Trans. AMS 164
(1972), §§3–4, pp. 373–374 and 381–382.
-/

public section
noncomputable section

namespace Stellmacher.Recognition.LyonsU3Four
open ModularBlock.PrincipalBlockConstruction Subgroup
open scoped BigOperators
attribute [local instance] Fintype.ofFinite
variable {G : Type*} [Group G] [Finite G]

namespace AmbientGeneralizedDecompositionData
variable {b : PrincipalCongruenceBlockData G} {t z : G}
  {μ : Subgroup.centralizer ({z} : Set G) →* ℂ}
  (a : AmbientGeneralizedDecompositionData b t z μ)

/-- The actual ambient character attached to a principal-block row. -/
@[expose] def character (_ : AmbientGeneralizedDecompositionData b t z μ)
    (j : {i // i ∈ b.block}) : ClassFunction G :=
  ofConjClassFunction (b.chi j.val)

theorem character_irreducible (j : {i // i ∈ b.block}) :
    IsIrreducibleCharacter (a.character j) := by
  obtain ⟨n, ρ, hρ⟩ := (b.complete.1 j.val).1
  refine ⟨n, ρ, (irreducible_iff_character_norm_one ρ).mpr ?_, ?_⟩
  · simpa [hρ] using (b.complete.1 j.val).2
  · change ofConjClassFunction (b.chi j.val) = ρ.character
    rw [hρ]
    rfl

/-- The degree is the dimension of an irreducible representation affording
this row, rather than a free integer assigned to the numerical pattern. -/
@[expose] def degree (j : {i // i ∈ b.block}) : ℕ :=
  (a.character_irreducible j).degree

theorem character_one (j : {i // i ∈ b.block}) :
    a.character j 1 = (a.degree j : ℂ) :=
  (a.character_irreducible j).degree_eq

theorem degree_pos (j : {i // i ∈ b.block}) : 0 < a.degree j :=
  (a.character_irreducible j).degree_pos

theorem degree_dvd_card (j : {i // i ∈ b.block}) : a.degree j ∣ Nat.card G :=
  (a.character_irreducible j).degree_dvd_card

theorem character_at_t (j : {i // i ∈ b.block}) :
    a.character j t = (a.columns.dT j : ℂ) :=
  GeneralizedDecompositionData.Equation3_1.at_t a.columns a.equation_3_1 j

theorem character_at_z (j : {i // i ∈ b.block}) :
    a.character j z = (a.columns.zValue j : ℂ) :=
  GeneralizedDecompositionData.Equation3_1.at_z a.columns a.equation_3_1 j

/-- Actual Sylow restriction multiplicities constrain the existing integral
columns whenever the section bases are an order-four element and its square. -/
theorem restriction_constraints [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) (d : LocalCentralizerData S)
    (s : S) (hs : orderOf s = 4) (ht : (s : G) = t) (hz : t ^ 2 = z)
    (j : {i // i ∈ b.block}) :
    ∃ m k : ℕ,
      (a.degree j : ℤ) - a.columns.zValue j = 16 * (m : ℤ) ∧
      (a.degree j : ℤ) + 3 * a.columns.zValue j + 60 * a.columns.dT j =
        64 * (k : ℤ) ∧
      Int.ModEq 4 (a.columns.dT j) (a.columns.zValue j) := by
  have hc : IsCharacter (a.character j) := by
    obtain ⟨n, ρ, _, hρ⟩ := a.character_irreducible j
    exact ⟨n, ρ, hρ⟩
  obtain ⟨n, x, y, m, k, hn, hx, hy, hm, hk, hmod⟩ :=
    genuine_sylow_character_constraints S h d hc s hs
  rw [ht] at hx hy
  rw [hz] at hy
  have hdn : n = a.degree j := by
    exact_mod_cast hn.symm.trans (a.character_one j)
  have hdx : x = a.columns.dT j := by
    exact_mod_cast hx.symm.trans (a.character_at_t j)
  have hdy : y = a.columns.zValue j := by
    exact_mod_cast hy.symm.trans (a.character_at_z j)
  exact ⟨m, k, by simpa only [hdn, hdx, hdy] using And.intro hm (And.intro hk hmod)⟩

/-- Every nonprincipal ambient row has degree at least twelve. -/
theorem degree_ge_twelve_of_ne_one [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) (d : LocalCentralizerData S)
    (s : S) (hs : orderOf s = 4) (j : {i // i ∈ b.block})
    (hj : a.character j ≠ 1) : 12 ≤ a.degree j :=
  genuine_nonprincipal_degree_ge_twelve S h d (a.character_irreducible j)
    hj s hs (a.character_one j)

/-- The degree agrees with the datum-independent actual row degree. -/
theorem degree_eq_ambientRowDegree (j : {i // i ∈ b.block}) :
    a.degree j = ambientRowDegree b j := by
  apply Nat.cast_injective (R := ℂ)
  exact (a.character_one j).symm.trans (ofConj_irreducible (b.complete.1 j.val)).degree_eq

/-- Completeness distinguishes every other row from the trivial character. -/
theorem character_ne_one_of_ne_principal (j : {i // i ∈ b.block})
    (hj : j ≠ ⟨b.principal, b.principal_mem⟩) : a.character j ≠ 1 := by
  intro he
  apply hj
  apply Subtype.ext
  apply b.complete.2.2
  rw [b.principal_eq]
  funext C
  obtain ⟨g, rfl⟩ := Quotient.exists_rep C
  exact congrFun he g

/-- The distinguished row has its actual degree one. -/
theorem principal_degree : a.degree ⟨b.principal, b.principal_mem⟩ = 1 := by
  have hh := a.character_one ⟨b.principal, b.principal_mem⟩
  change b.chi b.principal (ConjClasses.mk 1) = _ at hh
  rw [b.principal_eq] at hh
  change (1 : ℂ) = (a.degree ⟨b.principal, b.principal_mem⟩ : ℂ) at hh
  exact_mod_cast hh.symm

/-- Lyons’s Lemma 5 and degree-preserving Galois symmetry for actual rows. -/
theorem degree_constraints [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) (d : LocalCentralizerData S)
    (s : S) (hs : orderOf s = 4) (ht : (s : G) = t) :
    a.columns.DegreeConstraints ⟨b.principal, b.principal_mem⟩
      (fun j => (a.degree j : ℤ)) := by
  have hz : orderOf z = 2 := by rw [← a.square_t, orderOf_pow, a.order_t]; decide
  have hdeg (j : {i // i ∈ b.block}) :
      b.chi j.val (ConjClasses.mk 1) = (a.degree j : ℂ) := a.character_one j
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast a.principal_degree
  · intro j
    exact_mod_cast (a.degree_pos j).ne'
  · intro j hj
    simpa only [Int.natAbs_natCast] using
      a.degree_ge_twelve_of_ne_one S h d s hs j (a.character_ne_one_of_ne_principal j hj)
  · intro j
    obtain ⟨m, k, hm, hk, hmod⟩ := a.restriction_constraints S h d s hs ht a.square_t j
    rw [hk]
    exact Int.modEq_zero_iff_dvd.mpr (dvd_mul_right 64 _)
  · intro j
    obtain ⟨m, k, hm, hk, hmod⟩ := a.restriction_constraints S h d s hs ht a.square_t j
    rw [hk]
    positivity
  · have hh := degree_dT_eq_zero b a.columns t z a.order_t μ a.equation_3_1
    simp_rw [hdeg] at hh
    exact_mod_cast hh
  · intro i
    have hh := degree_iDz_eq_zero b a.columns t z hz μ a.order_mu a.equation_3_1 i
    simp_rw [hdeg] at hh
    exact_mod_cast hh
  · simpa only [a.degree_eq_ambientRowDegree] using
      ambient_signedGaloisSymmetry a.columns a.equation_3_1 a.order_mu

/-- Degree divisibility and the separated-row prime bound for actual rows. -/
theorem prime_constraints [IsSimpleGroup G] :
    a.columns.PrimeConstraints (fun j => (a.degree j : ℤ)) (Nat.card G) := by
  simpa only [a.degree_eq_ambientRowDegree] using
    ambient_primeConstraints a.columns a.equation_3_1 a.order_mu


/-- The numerical weighted column is Brauer’s expression divided by the group order. -/
theorem brauerDegreeSum_eq_weightedColumn (A : {i // i ∈ b.block} → ℤ) :
    brauerDegreeSum b z A = (Nat.card G : ℂ) *
      (a.columns.weightedColumn (fun j => (a.degree j : ℤ)) A : ℂ) := by
  have h1 (j : {i // i ∈ b.block}) :
      b.chi j.val (ConjClasses.mk 1) = (a.degree j : ℂ) := a.character_one j
  have hz (j : {i // i ∈ b.block}) :
      b.chi j.val (ConjClasses.mk z) = (a.columns.zValue j : ℂ) := a.character_at_z j
  simp [brauerDegreeSum, GeneralizedDecompositionData.weightedColumn, h1, hz]

end AmbientGeneralizedDecompositionData

/-- Lemma 4 in the rational numerical interface, with every quotient and local
basis witness supplied by the actual five-section model. -/
theorem ambient_orderConstraints_of_model [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S)
    (b : PrincipalCongruenceBlockData G) (t z : G)
    (M : FiveSectionModel S z)
    (a : AmbientGeneralizedDecompositionData b t z M.mu) :
    a.columns.OrderConstraints (fun j => (a.degree j : ℤ)) (Nat.card G)
      (Nat.card (centralizer ({z} : Set G)))
      (Nat.card (centralizer (centerImage S : Set G))) := by
  have hz2 : orderOf z = 2 := by rw [← a.square_t, orderOf_pow, a.order_t]; decide
  have hz1 : z ≠ 1 := by intro he; simp [he] at hz2
  obtain ⟨w, hw, hwz⟩ := M.central
  let v : QuarticCentralIndex S := ⟨⟨w, hw⟩, fun he => hz1 (by
    rw [← hwz]
    exact congrArg (fun x : center S => (x.val : G)) he)⟩
  obtain ⟨T⟩ := exists_localFiveCharacterTable S M.α h M.β M.order_β M.action
  have hid := brauerDegreeSum_iDz_order_identity S h b a.columns
    M.β M.order_β M.α M.action M.central hz2 M.quotientEquiv M.preservesSylow
    v hwz T t M.mu a.equation_3_1 M.enumeration (by
      intro i π hπ
      rw [M.enumeration_apply]
      simp only [MonoidHom.pow_apply, FiveSectionModel.mu_apply])
  have hidQ (i : Fin 5) :
      (Nat.card G : ℚ) * (Nat.card (centralizer (centerImage S : Set G)) : ℚ)^2 *
        a.columns.weightedColumn (fun j => (a.degree j : ℤ)) (a.columns.iDz i) =
          128 * (Nat.card (centralizer ({z} : Set G)) : ℚ)^3 := by
    have hh := hid i
    rw [a.brauerDegreeSum_eq_weightedColumn] at hh
    have hh' : (Nat.card G : ℂ) * (Nat.card (centralizer (centerImage S : Set G)) : ℂ)^2 *
        (a.columns.weightedColumn (fun j => (a.degree j : ℤ)) (a.columns.iDz i) : ℂ) =
          128 * (Nat.card (centralizer ({z} : Set G)) : ℂ)^3 := by
      calc
        _ = (Nat.card (centralizer (centerImage S : Set G)) : ℂ)^2 *
            ((Nat.card G : ℂ) *
            (a.columns.weightedColumn (fun j => (a.degree j : ℤ)) (a.columns.iDz i) : ℂ)) := by ring
        _ = _ := hh
    exact_mod_cast hh'
  refine ⟨Nat.card_pos, Nat.card_pos, Nat.card_pos, ?_, ?_, hidQ 0⟩
  · have hh := brauerDegreeSum_dT_eq_zero S h b a.columns t z a.order_t hz2 M.mu a.equation_3_1
    rw [a.brauerDegreeSum_eq_weightedColumn] at hh
    have hg : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := G)).ne'
    exact_mod_cast (mul_eq_zero.mp hh).resolve_left hg
  · intro i
    apply mul_left_cancel₀ (show (Nat.card G : ℚ) *
        (Nat.card (centralizer (centerImage S : Set G)) : ℚ)^2 ≠ 0 by
      exact mul_ne_zero (by exact_mod_cast (Nat.card_pos (α := G)).ne')
        (pow_ne_zero 2 (by exact_mod_cast
          (Nat.card_pos (α := centralizer (centerImage S : Set G))).ne')))
    exact (hidQ i).trans (hidQ 0).symm

/-- Actual ambient data and all three numerical constraint packages for a
chosen order-four element. No array, degree, or order identity is assumed. -/
theorem exists_ambient_decomposition_at [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) (d : LocalCentralizerData S)
    (b : PrincipalCongruenceBlockData G) (t : S) (ht : orderOf t = 4) :
    ∃ μ : centralizer ({(t : G)^2} : Set G) →* ℂ,
      ∃ a : AmbientGeneralizedDecompositionData b (t : G) ((t : G)^2) μ,
        a.columns.DegreeConstraints ⟨b.principal, b.principal_mem⟩
          (fun j => (a.degree j : ℤ)) ∧
        a.columns.OrderConstraints (fun j => (a.degree j : ℤ)) (Nat.card G)
          (Nat.card (centralizer ({(t : G)^2} : Set G)))
          (Nat.card (centralizer (centerImage S : Set G))) ∧
        a.columns.PrimeConstraints (fun j => (a.degree j : ℤ)) (Nat.card G) := by
  obtain ⟨M, l, c, hμ, h31, h32, h33, hpT, hpZ⟩ :=
    exists_ambient_integral_sections S h d b t ht
  have h34 : c.Equation3_4 := by
    intro j
    have hc : IsCharacter (ofConjClassFunction (b.chi j.val)) := by
      obtain ⟨n, ρ, _, hρ⟩ := ofConj_irreducible (b.complete.1 j.val)
      exact ⟨n, ρ, hρ⟩
    obtain ⟨n, x, y, m, k, hn, hx, hy, hm, hk, hmod⟩ :=
      genuine_sylow_character_constraints S h d hc t ht
    have hx' : x = c.dT j := by exact_mod_cast hx.symm.trans (GeneralizedDecompositionData.Equation3_1.at_t c h31 j)
    have hy' : y = c.zValue j := by exact_mod_cast hy.symm.trans (GeneralizedDecompositionData.Equation3_1.at_z c h31 j)
    simpa only [hx', hy'] using hmod
  have hzn : ∀ j, c.zValue j ≠ 0 := by
    intro j hj
    have hn := ambient_principal_character_center_ne_zero S M.central b j.val j.property
    rw [h31.at_z, hj, Int.cast_zero] at hn
    exact hn rfl
  let a : AmbientGeneralizedDecompositionData b (t : G) ((t : G)^2) M.mu := {
    order_t := (Subgroup.orderOf_coe t).trans ht
    square_t := rfl
    order_mu := hμ
    columns := c
    equation_3_1 := h31
    pattern := ⟨h32, h33, h34, ambient_galoisSymmetry c h31 hμ, hpT, hpZ, hzn⟩ }
  exact ⟨M.mu, a, a.degree_constraints S h d t ht rfl,
    ambient_orderConstraints_of_model S h b (t : G) ((t : G)^2) M a,
    a.prime_constraints⟩


omit [Finite G] in
/-- The center has four elements and the Sylow subgroup has sixty-four, so
there is a noncentral element; its order is four. -/
theorem exists_sylow_order_four (S : Sylow 2 G) (h : SylowStructure S) :
    ∃ t : S, orderOf t = 4 := by
  classical
  have hne : center S ≠ ⊤ := by
    intro he
    have hh := h.center_card
    rw [he, Subgroup.card_top, h.card] at hh
    omega
  obtain ⟨t, ht⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hne)
  exact ⟨t, (order_four_iff_not_mem_center S h t).mpr ht.2⟩

/-- Complete ambient realization from the original local group data. The
rows are genuine principal-block irreducible characters, and all numerical
constraints used by the independent Table I elimination are discharged. -/
theorem exists_ambient_decomposition [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) (d : LocalCentralizerData S) :
    ∃ b : PrincipalCongruenceBlockData G, ∃ t : S, ∃ _ht : orderOf t = 4,
      ∃ μ : centralizer ({(t : G)^2} : Set G) →* ℂ,
      ∃ a : AmbientGeneralizedDecompositionData b (t : G) ((t : G)^2) μ,
        a.columns.DegreeConstraints ⟨b.principal, b.principal_mem⟩
          (fun j => (a.degree j : ℤ)) ∧
        a.columns.OrderConstraints (fun j => (a.degree j : ℤ)) (Nat.card G)
          (Nat.card (centralizer ({(t : G)^2} : Set G)))
          (Nat.card (centralizer (centerImage S : Set G))) ∧
        a.columns.PrimeConstraints (fun j => (a.degree j : ℤ)) (Nat.card G) := by
  obtain ⟨b⟩ := exists_principalCongruenceBlockData G
  obtain ⟨t, ht⟩ := exists_sylow_order_four S h
  exact ⟨b, t, ht, exists_ambient_decomposition_at S h d b t ht⟩


namespace AmbientGeneralizedDecompositionData
variable {b : PrincipalCongruenceBlockData G} {t z : G}
  {μ : centralizer ({z} : Set G) →* ℂ}
  (a : AmbientGeneralizedDecompositionData b t z μ)

/-- Uniqueness of an actual degree gives rationality of the whole character,
using closure of the principal block under every complex automorphism. -/
theorem character_rational_of_unique_degree (j : {i // i ∈ b.block})
    (hunique : ∀ k, a.degree k = a.degree j → k = j) :
    ∀ g : G, ∃ q : ℚ, a.character j g = (q : ℂ) := by
  apply principalBlock_rational_of_unique_degree b j
  intro k hk
  apply hunique k
  simpa only [a.degree_eq_ambientRowDegree] using hk

/-- The order formula obtained from the surviving weighted column holds at
all nonidentity central Sylow elements, since they are conjugate in the ambient
group. The numerical value is the independent Table I calculation's output. -/
theorem centralizer_formula_of_weight [IsSimpleGroup G]
    (S : Sylow 2 G) (h : SylowStructure S) (hz : z ∈ centerImage S)
    (ho : a.columns.OrderConstraints (fun j => (a.degree j : ℤ)) (Nat.card G)
      (Nat.card (centralizer ({z} : Set G)))
      (Nat.card (centralizer (centerImage S : Set G))))
    (hw : a.columns.weightedColumn (fun j => (a.degree j : ℤ))
      (a.columns.iDz 0) = 128 / 195) :
    ∀ u ∈ centerImage S, u ≠ 1 →
      Nat.card G * Nat.card (centralizer (centerImage S : Set G)) ^ 2 =
        195 * Nat.card (centralizer ({u} : Set G)) ^ 3 := by
  have hz2 : orderOf z = 2 := by rw [← a.square_t, orderOf_pow, a.order_t]; decide
  have hz1 : z ≠ 1 := by intro he; simp [he] at hz2
  intro u hu hu1
  have hc := Subgroup.card_centralizer_eq_of_isConj z u
    (centerImage_nonidentity_isConj S h hz hu hz1 hu1)
  rw [← hc]
  exact ho.centralizer_formula hw

end AmbientGeneralizedDecompositionData
end Stellmacher.Recognition.LyonsU3Four
