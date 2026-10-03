module

public import Glauberman.SuzukiCharacterization.NormalizerFrobenius
public import Glauberman.SuzukiCharacterization.CharacterSelectionCore
public import Theory.Character.Induction
public import Theory.Character.ModularBlock.InvolutionPairVanishing
public import Theory.Character.ModularBlock.InvolutionColumnVanishing
public import Theory.Character.ModularBlock.LocalColumnNorm
public import Theory.Character.ModularBlock.NormalComplementDegree

/-!
# Principal-block columns for Suzuki character selection

The commutator-support condition excludes products of two conjugates of the
chosen involution from every two-section based outside P₀. Principal-block
kernel support therefore makes the involution-pair column vanish there.
Averaging against θ - 1 gives Lemma 4.1; Frobenius reciprocity identifies
its coefficients with the induced character difference.

The involution is central in P. Its centralizer has a normal odd complement,
whose quotient has order |P|. Local column orthogonality and the principal-block
degree sum then give squared norm |P|. Removing the principal row gives
(4.2)–(4.3). The final adapter supplies both column inputs to the existing
character-selection theorem, leaving its separate degree lower bound explicit.
No normalizer orbit or degree-lower-bound hypothesis is needed for these columns.

Source: Glauberman, *A Characterization of the Suzuki Groups* (1968),
Lemma 4.1 and equations (4.1)–(4.3), pp. 89–90, saved at
`refs/original/n-group-global/odd-core-rank-two-source/glauberman-suzuki-1968-euclid-wayback.pdf`.
-/

open scoped BigOperators
open Theory.Character ModularBlock.PrincipalBlockConstruction
noncomputable section
attribute [local instance] Fintype.ofFinite

namespace Glauberman.SuzukiCharacterization.CharacterSelection

private theorem pair_count_zero {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    (s : CommutatorSupportData P) (x : P) (hx : x ∉ s.P₀)
    (y : G) (hy : Odd (orderOf y)) (hxy : Commute (x : G) y) :
    classSumPairCountMul (ConjClasses.mk (s.v : G)) (ConjClasses.mk (s.v : G))
      ((x : G) * y) = 0 := by
  classical
  rw [classSumPairCountMul_eq_card]
  apply Nat.card_eq_zero.mpr
  left
  constructor
  rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hab⟩
  have ha' : IsConj (s.v : G) a := by
    exact (ConjClasses.mk_eq_mk_iff_isConj.mp (ConjClasses.mem_carrier_iff_mk_eq.mp ha)).symm
  have hb' : IsConj (s.v : G) b := by
    exact (ConjClasses.mk_eq_mk_iff_isConj.mp (ConjClasses.mem_carrier_iff_mk_eq.mp hb)).symm
  obtain ⟨g, rfl⟩ := isConj_iff.mp ha'
  obtain ⟨k, rfl⟩ := isConj_iff.mp hb'
  apply hx (s.support g k x y hxy (Nat.coprime_two_left.mpr hy) ?_)
  have hv : (s.v : G)⁻¹ = s.v := by
    apply inv_eq_of_mul_eq_one_left
    have hh := pow_orderOf_eq_one s.v
    rw [s.involution, pow_two] at hh
    exact congrArg Subtype.val hh
  simpa only [mul_inv_rev, inv_inv, hv, mul_assoc] using hab

variable {G : Type*} [Group G] [Finite G]

private theorem principalBlock_column_vanishes_on_difference_support (P : Sylow 2 G) (d : PrincipalCongruenceBlockData G)
    (s : CommutatorSupportData P) (x : P) (hx : (s.theta - 1) x ≠ 0) :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk (x : G)) *
      d.chi i (ConjClasses.mk (s.v : G)) ^ 2 / d.chi i (ConjClasses.mk 1) = 0 := by
  have hv : (s.v : G) * s.v = 1 := by
    have hh := pow_orderOf_eq_one s.v
    rw [s.involution, pow_two] at hh
    exact congrArg Subtype.val hh
  have hp : ∃ n : ℕ, (x : G) ^ (2 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_pow_pow_eq_one x
    exact ⟨n, congrArg Subtype.val hn⟩
  have hn : x ∉ s.P₀ := by
    intro hmem
    apply hx
    change s.theta x - 1 = 0
    rw [(s.kernel x).mpr hmem, sub_self]
  simpa only [mul_comm] using
    ModularBlock.InvolutionPairVanishing.principalBlock_pairSum_eq_zero_of_twoSection_support
      d s.v x hv hp (fun y hy hxy => pair_count_zero P s x hn y hy hxy)

private theorem principalBlock_weighted_identity_complex (P : Sylow 2 G) (d : PrincipalCongruenceBlockData G)
    (s : CommutatorSupportData P) (c₀ c₁ : d.I → ℕ)
    (hc₀ : ∀ i, scalarProduct P (fun x : P => d.chi i (ConjClasses.mk (x : G))) 1 = c₀ i)
    (hc₁ : ∀ i, scalarProduct P (fun x : P => d.chi i (ConjClasses.mk (x : G))) s.theta = c₁ i) :
    ∑ i ∈ d.block, ((c₁ i : ℂ) - c₀ i) *
      d.chi i (ConjClasses.mk (s.v : G)) ^ 2 / d.chi i (ConjClasses.mk 1) = 0 := by
  have h := ModularBlock.InvolutionColumnVanishing.principalBlock_involution_weighted_sum_eq_zero_of_pointwise
    d (P : Subgroup G) (s.theta - 1) s.v (principalBlock_column_vanishes_on_difference_support P d s)
  have hcoeff (i : d.I) :
      scalarProduct P (fun x : P => d.chi i (ConjClasses.mk (x : G))) (s.theta - 1) =
        (c₁ i : ℂ) - c₀ i := by
    rw [← scalarProduct_conj, scalarProduct_sub_left, star_sub,
      scalarProduct_conj, scalarProduct_conj, hc₁, hc₀]
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [← hcoeff i]
  congr 3

/-- Lemma 4.1 in restriction-multiplicity form. The support condition alone
forces the weighted principal-block sum to vanish. -/
public theorem principalBlock_weighted_identity (P : Sylow 2 G) (d : PrincipalCongruenceBlockData G)
    (s : CommutatorSupportData P) (c₀ c₁ : d.I → ℕ)
    (hc₀ : ∀ i, scalarProduct P (fun x : P => d.chi i (ConjClasses.mk (x : G))) 1 = c₀ i)
    (hc₁ : ∀ i, scalarProduct P (fun x : P => d.chi i (ConjClasses.mk (x : G))) s.theta = c₁ i) :
    ∑ i ∈ d.block, ((c₁ i : ℝ) - c₀ i) *
      Complex.normSq (d.chi i (ConjClasses.mk (s.v : G))) /
        (d.chi i (ConjClasses.mk 1)).re = 0 := by
  have hv : (s.v : G)⁻¹ = s.v := by
    apply inv_eq_of_mul_eq_one_left
    have hh := pow_orderOf_eq_one s.v
    rw [s.involution, pow_two] at hh
    exact congrArg Subtype.val hh
  have hsq (i : d.I) : d.chi i (ConjClasses.mk (s.v : G)) ^ 2 =
      (Complex.normSq (d.chi i (ConjClasses.mk (s.v : G))) : ℂ) := by
    calc
      _ = d.chi i (ConjClasses.mk (s.v : G)) * star (d.chi i (ConjClasses.mk (s.v : G))) := by
        rw [star_conjChar_apply_inv (d.complete.1 i).1, hv, pow_two]
      _ = _ := Complex.mul_conj _
  have hdeg (i : d.I) : ((d.chi i (ConjClasses.mk 1)).re : ℂ) = d.chi i (ConjClasses.mk 1) := by
    apply Complex.conj_eq_iff_re.mp
    simpa only [Complex.star_def, inv_one] using star_conjChar_apply_inv (d.complete.1 i).1 (1 : G)
  apply Complex.ofReal_injective
  push_cast
  simp only [hdeg, ← hsq]
  exact principalBlock_weighted_identity_complex P d s c₀ c₁ hc₀ hc₁

/-- Equation (4.1) at the chosen central involution: the complete principal-block
column has squared norm exactly the Sylow order, hence satisfies the required bound. -/
public theorem principalBlock_column_norm (P : Sylow 2 G) (h : Hypotheses P)
    (d : PrincipalCongruenceBlockData G) (s : CommutatorSupportData P) :
    ∑ i ∈ d.block, Complex.normSq (d.chi i (ConjClasses.mk (s.v : G))) = Nat.card P := by
  let C := Subgroup.centralizer ({(s.v : G)} : Set G)
  have hPC : (P : Subgroup G) ≤ C := by
    intro p hp
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_center_iff.mp s.central ⟨p, hp⟩))
  have hv : (s.v : G) ≠ 1 := by
    intro he
    have hh : s.v = 1 := Subtype.ext he
    have ho := s.involution
    rw [hh, orderOf_one] at ho
    norm_num at ho
  obtain ⟨N, hN, hcop, hquot⟩ := h.centralizer_hasNormalPComplement P s.v s.v.property hv
  let := hN
  let S : Sylow 2 C := P.subtype hPC
  have hcard : Nat.card S = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv
  have hdegree := ModularBlock.NormalComplementDegree.sum_degree_sq_eq_sylow_card
    (ModularBlock.CompatibleBrauerBlock.localData d C) S N hcop hquot
  have hp : ∃ n : ℕ, (s.v : G) ^ (2 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_pow_pow_eq_one s.v
    exact ⟨n, congrArg Subtype.val hn⟩
  have hn := ModularBlock.LocalColumnNorm.principalBlock_local_column_norm d s.v hp
  rw [hdegree, hcard] at hn
  have hr := congrArg Complex.re hn
  simpa only [Complex.re_sum, Complex.star_def, Complex.mul_conj,
    Complex.ofReal_re, Complex.natCast_re] using hr


/-- Frobenius reciprocity identifies the induced difference coefficient with
the difference of the two natural restriction multiplicities. -/
public theorem induced_difference_multiplicity (P : Sylow 2 G) (d : PrincipalCongruenceBlockData G)
    (s : CommutatorSupportData P) (c₀ c₁ : d.I → ℕ)
    (hc₀ : ∀ i, scalarProduct P (fun x : P => d.chi i (ConjClasses.mk (x : G))) 1 = c₀ i)
    (hc₁ : ∀ i, scalarProduct P (fun x : P => d.chi i (ConjClasses.mk (x : G))) s.theta = c₁ i)
    (i : d.I) :
    scalarProduct G (inducedClassFunction (P : Subgroup G) (s.theta - 1))
      (ofConjClassFunction (d.chi i)) = (c₁ i : ℂ) - c₀ i := by
  let : Fintype P := Fintype.ofFinite P
  have h₁ := congrArg star (hc₁ i)
  have h₀ := congrArg star (hc₀ i)
  simp only [scalarProduct_conj, star_natCast] at h₁ h₀
  calc
    _ = scalarProduct P (s.theta - 1) (fun x : P => d.chi i (ConjClasses.mk (x : G))) := by
      convert scalarProduct_inducedClassFunction (P : Subgroup G) (s.theta - 1)
        (ofConjClassFunction_isClassFunction (d.chi i)) using 1
      congr 2
      exact Subsingleton.elim _ _
    _ = scalarProduct P s.theta (fun x : P => d.chi i (ConjClasses.mk (x : G))) -
        scalarProduct P 1 (fun x : P => d.chi i (ConjClasses.mk (x : G))) :=
      scalarProduct_sub_left _ _ _
    _ = _ := by rw [h₁, h₀]

/-- Equations (4.2) and (4.3): removing the principal row leaves weighted mass
one and squared column norm exactly |P| - 1. -/
public theorem principalBlock_nonprincipal_column_identities (P : Sylow 2 G) (h : Hypotheses P)
    (d : PrincipalCongruenceBlockData G) (s : CommutatorSupportData P) (c₀ c₁ : d.I → ℕ)
    (hc₀ : ∀ i, scalarProduct P (fun x : P => d.chi i (ConjClasses.mk (x : G))) 1 = c₀ i)
    (hc₁ : ∀ i, scalarProduct P (fun x : P => d.chi i (ConjClasses.mk (x : G))) s.theta = c₁ i) :
    (∑ i ∈ d.block.erase d.principal, ((c₁ i : ℝ) - c₀ i) *
      Complex.normSq (d.chi i (ConjClasses.mk (s.v : G))) /
        (d.chi i (ConjClasses.mk 1)).re = 1) ∧
    (∑ i ∈ d.block.erase d.principal, Complex.normSq (d.chi i (ConjClasses.mk (s.v : G))) =
      (Nat.card P : ℝ) - 1) := by
  classical
  let : Fintype P := Fintype.ofFinite P
  have hpval (g : G) : d.chi d.principal (ConjClasses.mk g) = 1 := by
    rw [d.principal_eq]
    rfl
  have hc₀p : c₀ d.principal = 1 := by
    have hp := hc₀ d.principal
    simp only [hpval] at hp
    have he : scalarProduct P (fun _ => (1 : ℂ)) 1 = 1 := by simp [scalarProduct]
    have hp' : scalarProduct P (fun _ => (1 : ℂ)) 1 = (c₀ d.principal : ℂ) := hp
    rw [he] at hp'
    exact_mod_cast hp'.symm
  have hc₁p : c₁ d.principal = 0 := by
    have hz := s.linear.1.scalarProduct_principal_eq_zero s.theta_ne_one
    have hz' : scalarProduct P 1 s.theta = 0 := by
      rw [← scalarProduct_conj, hz, star_zero]
    have hp := hc₁ d.principal
    simp only [hpval] at hp
    change scalarProduct P 1 s.theta = _ at hp
    rw [hz'] at hp
    exact_mod_cast hp.symm
  have hw := principalBlock_weighted_identity P d s c₀ c₁ hc₀ hc₁
  have hn := principalBlock_column_norm P h d s
  rw [← Finset.sum_erase_add _ _ d.principal_mem] at hw hn
  simp only [hc₀p, hc₁p, Nat.cast_zero, Nat.cast_one, zero_sub, hpval,
    Complex.normSq_one, Complex.one_re, mul_one, div_one] at hw hn
  constructor <;> linarith

/-- The column inputs to character selection leave only the degree lower bound. -/
public theorem exists_zero_sum_of_degree_lower
    (P : Sylow 2 G) (h : Hypotheses P)
    (d : PrincipalCongruenceBlockData G) (s : CommutatorSupportData P)
    (c₀ c₁ : d.I → ℕ)
    (hc₀ : ∀ i, scalarProduct P (fun x : P => d.chi i (ConjClasses.mk (x : G))) 1 = c₀ i)
    (hc₁ : ∀ i, scalarProduct P (fun x : P => d.chi i (ConjClasses.mk (x : G))) s.theta = c₁ i)
    (q : ℝ) (hq : 0 < q)
    (hlower : ∀ i ∈ d.block, 1 ≤ (c₁ i : ℤ) - c₀ i →
      (c₀ i : ℝ) + q + ((c₁ i : ℝ) - 1) * ((Nat.card P : ℝ) - 1) ≤
        (d.chi i (ConjClasses.mk 1)).re) :
    ∃ i ∈ d.block, ∑ x : P, d.chi i (ConjClasses.mk (x : G)) = 0 := by
  exact exists_zero_sum_of_column_identities P d s c₀ c₁ hc₀ hc₁ q hq
    (principalBlock_weighted_identity P d s c₀ c₁ hc₀ hc₁) (principalBlock_column_norm P h d s).le hlower

end Glauberman.SuzukiCharacterization.CharacterSelection
