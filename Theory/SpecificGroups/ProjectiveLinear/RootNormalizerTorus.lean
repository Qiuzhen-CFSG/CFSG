module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Theory.GroupTheory.QuasithinBasic
public import Theory.GroupTheory.PrimeRankWitness
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

/-!
# Rank-three tori in projective root normalizers

In PSL of dimension at least four, the diagonal matrices
`diag(a,b,c,(abc)⁻¹,1,…)` normalize every transvection root group. Their
projective kernel consists of scalar matrices with fourth power one, so
restriction to odd-prime torsion is injective. A prime divisor of `|F|-1`
therefore gives an elementary abelian rank-three subgroup of the literal
root normalizer.

In characteristic two the projective root group is a nontrivial two-group.
For `|F| > 2`, an odd prime divides `|F|-1`, contradicting quasithinness.
This supplies the linear-family instance of the split-torus argument in
Aschbacher–Smith, *The Classification of Quasithin Groups*, Lemma A.2.18
(printed p.40), used in Theorem D/14.8.2(1) (pp.1078–1079).
No Borel decomposition, subgroup classification or induction premise is used.
-/

@[expose] public section

open Matrix
namespace Theory.SpecificGroups.ProjectiveLinearRoot
variable {F : Type*} [Field F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The additive field parametrizes a transvection root group in SL. -/
noncomputable def rootHom {i j : ι} (hij : i ≠ j) :
    Multiplicative F →* SpecialLinearGroup ι F where
  toFun x := SpecialLinearGroup.transvection hij x.toAdd
  map_one' := SpecialLinearGroup.transvection_coeff_zero hij
  map_mul' x y := SpecialLinearGroup.transvection_add hij x.toAdd y.toAdd

/-- The literal central quotient from SL to PSL. -/
noncomputable def project : SpecialLinearGroup ι F →* ProjectiveSpecialLinearGroup ι F :=
  QuotientGroup.mk' _

/-- The transvection root map after passage to the central quotient. -/
noncomputable def projectiveRootHom {i j : ι} (hij : i ≠ j) :
    Multiplicative F →* ProjectiveSpecialLinearGroup ι F :=
  project.comp (rootHom hij)

/-- No nonidentity transvection is a scalar matrix. -/
theorem projectiveRootHom_injective {i j : ι} (hij : i ≠ j) :
    Function.Injective (projectiveRootHom (F := F) hij) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  change QuotientGroup.mk (SpecialLinearGroup.transvection hij x.toAdd) = 1 at hx
  rw [QuotientGroup.eq_one_iff, SpecialLinearGroup.transvection_mem_center_iff] at hx
  exact congrArg Multiplicative.ofAdd hx

/-- The image of the additive root map in PSL. -/
noncomputable def rootSubgroup {i j : ι} (hij : i ≠ j) :
    Subgroup (ProjectiveSpecialLinearGroup ι F) := (projectiveRootHom hij).range

/-- The image of the root element with parameter one is nonidentity. -/
theorem rootSubgroup_ne_bot {i j : ι} (hij : i ≠ j) :
    rootSubgroup (F := F) hij ≠ ⊥ := by
  intro h
  have hx : projectiveRootHom hij (Multiplicative.ofAdd (1 : F)) = 1 := by
    have hm : projectiveRootHom hij (Multiplicative.ofAdd (1 : F)) ∈ rootSubgroup hij :=
      ⟨_, rfl⟩
    simpa [h] using hm
  have := (projectiveRootHom_injective hij) (hx.trans (map_one _).symm)
  exact one_ne_zero (congrArg Multiplicative.toAdd this)

/-- In characteristic two the root image is a two-group. -/
theorem rootSubgroup_isTwoGroup [CharP F 2] {i j : ι} (hij : i ≠ j) :
    IsPGroup 2 (rootSubgroup (F := F) hij) := by
  have h : IsPGroup 2 (Multiplicative F) := by
    intro x
    refine ⟨1, ?_⟩
    change (2 ^ 1 : ℕ) • x.toAdd = 0
    rw [pow_one, nsmul_eq_mul, CharP.cast_eq_zero F 2, zero_mul]
  exact h.of_surjective (projectiveRootHom (F := F) hij).rangeRestrict
    (projectiveRootHom (F := F) hij).rangeRestrict_surjective


/-- The actual root normalizer is a two-local subgroup. -/
theorem rootNormalizer_isTwoLocal [CharP F 2] {i j : ι} (hij : i ≠ j) :
    IsTwoLocal (Subgroup.normalizer (rootSubgroup (F := F) hij : Set (ProjectiveSpecialLinearGroup ι F))) :=
  ⟨rootSubgroup hij, rootSubgroup_ne_bot hij, rootSubgroup_isTwoGroup hij, rfl⟩

variable (k : ℕ) (C : Subgroup Fˣ)

/-- Three free diagonal entries and a fourth enforcing determinant one. -/
def torusEntries (a : Fin 3 → C) : Fin (4 + k) → C :=
  Fin.append ![a 0, a 1, a 2, (a 0 * a 1 * a 2)⁻¹] (fun _ => 1)

/-- The chosen diagonal matrix has determinant one in every dimension. -/
theorem torusEntries_det (a : Fin 3 → C) :
    (diagonal (fun i => ((torusEntries k C a i).val : F))).det = 1 := by
  rw [det_diagonal, Fin.prod_univ_add]
  simp [torusEntries, Fin.prod_univ_succ, ← mul_assoc]

/-- The three-parameter diagonal homomorphism into SL. -/
noncomputable def torusSpecial : (Fin 3 → C) →* SpecialLinearGroup (Fin (4 + k)) F where
  toFun a := ⟨diagonal (fun i => ((torusEntries k C a i).val : F)), torusEntries_det k C a⟩
  map_one' := by
    apply Subtype.ext
    apply congrArg diagonal
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      fin_cases j <;> simp [torusEntries]
    · intro j
      simp [torusEntries]
  map_mul' a b := by
    apply Subtype.ext
    change diagonal _ = diagonal _ * diagonal _
    rw [diagonal_mul_diagonal]
    apply congrArg diagonal
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      fin_cases j <;> simp [torusEntries, mul_assoc, mul_comm, mul_left_comm]
    · intro j
      simp [torusEntries]

@[simp] theorem torusSpecial_coe (a : Fin 3 → C) :
    (torusSpecial k C a : Matrix (Fin (4 + k)) (Fin (4 + k)) F) =
      diagonal (fun i => ((torusEntries k C a i).val : F)) := rfl

/-- The same diagonal homomorphism in the actual central quotient. -/
noncomputable def torusProjective : (Fin 3 → C) →*
    ProjectiveSpecialLinearGroup (Fin (4 + k)) F := project.comp (torusSpecial k C)

/-- Fourth-torsion-free parameter groups survive projectivization faithfully. -/
theorem torusProjective_injective (hfour : ∀ u : C, u ^ 4 = 1 → u = 1) :
    Function.Injective (torusProjective k C) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  change QuotientGroup.mk (torusSpecial k C a) = 1 at ha
  rw [QuotientGroup.eq_one_iff, SpecialLinearGroup.mem_center_iff] at ha
  obtain ⟨r, _, hr⟩ := ha
  have hd (i : Fin 4) : ((![a 0, a 1, a 2, (a 0 * a 1 * a 2)⁻¹] i).val : F) = r := by
    have hi := congrArg (fun M : Matrix (Fin (4+k)) (Fin (4+k)) F =>
      M (Fin.castAdd k i) (Fin.castAdd k i)) hr
    simpa [torusSpecial_coe, Matrix.scalar, torusEntries] using hi.symm
  have h1 : a 1 = a 0 := Subtype.ext (Units.ext ((hd 1).trans (hd 0).symm))
  have h2 : a 2 = a 0 := Subtype.ext (Units.ext ((hd 2).trans (hd 0).symm))
  have h3 : (a 0 * a 1 * a 2)⁻¹ = a 0 :=
    Subtype.ext (Units.ext ((hd 3).trans (hd 0).symm))
  have hpow : a 0 ^ 4 = 1 := by
    rw [h1, h2] at h3
    have ht := inv_eq_iff_mul_eq_one.mp h3
    simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using ht
  have h0 := hfour (a 0) hpow
  funext i
  fin_cases i
  · exact h0
  · exact h1.trans h0
  · exact h2.trans h0


private theorem torus_conj_root (a : Fin 3 → C) {i j : Fin (4+k)} (hij : i ≠ j) (x : F) :
    torusSpecial k C a * SpecialLinearGroup.transvection hij x * (torusSpecial k C a)⁻¹ =
      SpecialLinearGroup.transvection hij
        (((torusEntries k C a i).val : F) * x * ((torusEntries k C a j).val : F)⁻¹) := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Subtype.ext
  change diagonal _ * (1 + single i j x) =
    (1 + single i j _) * diagonal _
  ext u v
  rw [diagonal_mul, mul_diagonal]
  by_cases huv : u = v
  · subst v
    by_cases hui : u = i <;> by_cases huj : u = j <;>
      simp_all [Matrix.single_apply, eq_comm]
  · by_cases hui : u = i <;> by_cases hvj : v = j <;>
      simp_all [eq_comm, mul_assoc]

private theorem torusProjective_conj_root (a : Fin 3 → C)
    {i j : Fin (4+k)} (hij : i ≠ j) (x : Multiplicative F) :
    torusProjective k C a * projectiveRootHom hij x * (torusProjective k C a)⁻¹ =
      projectiveRootHom hij (Multiplicative.ofAdd
        (((torusEntries k C a i).val : F) * x.toAdd * ((torusEntries k C a j).val : F)⁻¹)) := by
  have ht := congrArg (project (F := F)) (torus_conj_root k C a hij x.toAdd)
  simpa only [torusProjective, projectiveRootHom, rootHom, MonoidHom.comp_apply,
    MonoidHom.coe_mk, OneHom.coe_mk, map_mul, map_inv, toAdd_ofAdd] using ht

/-- Every chosen diagonal matrix normalizes the literal projective root image. -/
theorem torusProjective_mem_normalizer (a : Fin 3 → C)
    {i j : Fin (4+k)} (hij : i ≠ j) :
    torusProjective k C a ∈ Subgroup.normalizer
      (rootSubgroup (F := F) hij : Set (ProjectiveSpecialLinearGroup (Fin (4+k)) F)) := by
  have hf (a : Fin 3 → C) (g : ProjectiveSpecialLinearGroup (Fin (4+k)) F)
      (hg : g ∈ rootSubgroup hij) :
      torusProjective k C a * g * (torusProjective k C a)⁻¹ ∈ rootSubgroup hij := by
    obtain ⟨x, rfl⟩ := hg
    rw [torusProjective_conj_root]
    exact ⟨_, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨hf a g, fun hg => ?_⟩
  simpa only [map_inv, inv_inv, inv_mul_cancel_left, mul_assoc, inv_mul_cancel,
    mul_one] using hf a⁻¹ _ hg

/-- The torus homomorphism with codomain the actual root normalizer. -/
noncomputable def torusNormalizer {i j : Fin (4+k)} (hij : i ≠ j) :
    (Fin 3 → C) →* Subgroup.normalizer
      (rootSubgroup (F := F) hij : Set (ProjectiveSpecialLinearGroup (Fin (4+k)) F)) :=
  (torusProjective k C).codRestrict _ (fun a => torusProjective_mem_normalizer k C a hij)

/-- Restricting the codomain to the root normalizer preserves injectivity. -/
theorem torusNormalizer_injective {i j : Fin (4+k)} (hij : i ≠ j)
    (hfour : ∀ u : C, u ^ 4 = 1 → u = 1) :
    Function.Injective (torusNormalizer k C hij) := by
  intro a b hab
  exact torusProjective_injective k C hfour (congrArg Subtype.val hab)


/-- Every odd prime dividing the multiplicative field order contributes rank three. -/
theorem primeRank_rootNormalizer_ge_three [Finite F] {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hd : p ∣ Nat.card F - 1)
    {i j : Fin (4+k)} (hij : i ≠ j) :
    3 ≤ primeRank p (Subgroup.normalizer
      (rootSubgroup (F := F) hij : Set (ProjectiveSpecialLinearGroup (Fin (4+k)) F))) := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  have hdu : p ∣ Nat.card Fˣ := by simpa only [Nat.card_units] using hd
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p hdu
  have hroot : IsPrimitiveRoot u p := hu ▸ IsPrimitiveRoot.orderOf u
  have hc : Nat.card (rootsOfUnity p F) = p := hroot.card_rootsOfUnity'
  have hpow (u : rootsOfUnity p F) : u ^ p = 1 :=
    Subtype.ext ((mem_rootsOfUnity p u.val).mp u.property)
  have hcop : p.Coprime 4 := by
    have h2 : p.Coprime 2 := hp.coprime_iff_not_dvd.mpr (by
      intro h
      have he := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h
      rw [he] at ho
      norm_num at ho)
    exact h2.pow_right 2
  have hfour (u : rootsOfUnity p F) (hu : u ^ 4 = 1) : u = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.dvd_one.mp
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (hpow u)) (orderOf_dvd_of_pow_eq_one hu)
  apply primeRank_ge_of_elementary_embedding
    (A := Fin 3 → rootsOfUnity p F)
    (fun a => funext (fun i => hpow (a i)))
    (by rw [Nat.card_fun, hc, Nat.card_fin])
    (torusNormalizer k (rootsOfUnity p F) hij)
  exact torusNormalizer_injective k (rootsOfUnity p F) hij hfour

/-- No PSL of dimension at least four over an even field larger than two is quasithin. -/
theorem not_quasithin [Finite F] [CharP F 2]
    (hq : 2 < Nat.card F) :
    ¬ IsQuasithin (ProjectiveSpecialLinearGroup (Fin (4+k)) F) := by
  intro hG
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (show Nat.card F - 1 ≠ 1 by omega)
  have heven : Even (Nat.card F) := by
    rw [Nat.card_eq_fintype_card, even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
    exact FiniteField.even_card_iff_char_two.mp (ringChar.eq F 2)
  have ho : Odd p := hp.odd_of_ne_two (by
    intro he
    subst p
    obtain ⟨a, ha⟩ := heven
    obtain ⟨b, hb⟩ := hd
    omega)
  let i : Fin (4+k) := ⟨0, by omega⟩
  let j : Fin (4+k) := ⟨1, by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i, j] at this
  have hr := primeRank_rootNormalizer_ge_three (F := F) k hp ho hd hij
  have hb := Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hG _
    (rootNormalizer_isTwoLocal hij) p hp ho
  omega

end Theory.SpecificGroups.ProjectiveLinearRoot
