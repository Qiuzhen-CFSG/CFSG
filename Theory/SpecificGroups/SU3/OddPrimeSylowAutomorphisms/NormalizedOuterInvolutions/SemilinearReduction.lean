module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.GraphComparison
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Diagonal
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Semilinear
public import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.Algebra.ZMod

/-!
# Reduction of odd-prime outer involutions to unitary twists

Over a field of order `p²`, the field automorphism group has at most two
elements: its automorphisms are linear over the prime field, and the extension
has degree two. The prescribed fixed-field cardinality makes the Hermitian
conjugation nontrivial. Thus any concrete semilinear formula for an outer
involution has exactly this field part, since involutory unitary conjugation
is inner.

This removes the need for a separate faithfulness theorem for the field
component. Existence of semilinear formulas for arbitrary automorphisms remains
an explicit mathematical input. Entrywise graph action is constructed on the
actual projective image in every characteristic, adapting the construction in
`Theory.SpecificGroups.SU3.ProjectiveGraphFixed`.

Source: GLS3, Theorem 2.5.12(a,c,d,f), with Section 2.7's matrix identification;
Aschbacher–Smith F.6.18(10)–(11), printed pp.309–310.
-/

open Matrix
open scoped Matrix
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter
variable {E : Type*} [Field E] (J : HermitianForm 3 E)
variable (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
include hJ in
private theorem form_map : J.form.map J.conj = J.form := by
  rw [hJ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
include hJ in
private theorem map_mem (x : J.specialSubgroup) :
    GeneralLinearGroup.map J.conj.toRingHom x.val ∈ J.specialSubgroup := by
  obtain ⟨hx, hd⟩ := (J.mem_specialSubgroup_iff x.val).mp x.property
  apply (J.mem_specialSubgroup_iff _).mpr
  constructor
  · have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M.map J.conj) hx
    have ht : (J.conjTranspose x.val.val).map J.conj =
        J.conjTranspose (x.val.val.map J.conj) := by
      ext i j
      rfl
    change J.conjTranspose (x.val.val.map J.conj) * J.form *
      x.val.val.map J.conj = J.form
    simpa only [Matrix.map_mul, ht, form_map J hJ] using h
  · apply Units.ext
    change (J.conj.mapMatrix x.val.val).det = 1
    rw [← RingEquiv.map_det]
    have hd' : x.val.val.det = 1 := congrArg Units.val hd
    rw [hd', map_one]

/-- Entrywise conjugation on the actual special unitary subgroup. -/
public def entrywiseSpecialAut : MulAut J.specialSubgroup where
  toFun x := ⟨GeneralLinearGroup.map J.conj.toRingHom x.val, map_mem J hJ x⟩
  invFun x := ⟨GeneralLinearGroup.map J.conj.toRingHom x.val, map_mem J hJ x⟩
  left_inv x := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact J.conj_involutive _
  right_inv x := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact J.conj_involutive _
  map_mul' x y := Subtype.ext (map_mul _ _ _)

@[simp] public theorem entrywiseSpecialAut_apply_val (x : J.specialSubgroup) :
    (entrywiseSpecialAut J hJ x).val.val = x.val.val.map J.conj := by rfl

private def entrywiseProjectiveHom : ProjectiveSpecialUnitaryMatrixGroup J →* ProjectiveSpecialUnitaryMatrixGroup J :=
  ((ProjGenLinGroup.map J.conj.toRingHom).comp
    (ProjectiveSpecialUnitaryMatrixGroup J).subtype).codRestrict _ (by
      intro b
      obtain ⟨x, rfl⟩ := J.specialToProjective_surjective b
      change ProjGenLinGroup.map J.conj.toRingHom (J.specialToProjective x).val ∈ _
      rw [J.specialToProjective_apply_val]
      exact Subgroup.mem_map_of_mem _ (map_mem J hJ x))

private theorem entrywiseProjectiveHom_apply (x : J.specialSubgroup) :
    entrywiseProjectiveHom J hJ (J.specialToProjective x) = J.specialToProjective (entrywiseSpecialAut J hJ x) := by
  apply Subtype.ext
  change ProjGenLinGroup.map J.conj.toRingHom (J.specialToProjective x).val = _
  rw [specialToProjective_apply_val, ProjGenLinGroup.map_mk,
    specialToProjective_apply_val]
  rfl

/-- Entrywise conjugation descended to the actual projective image of SU₃. -/
public def entrywiseProjectiveAut : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) where
  toFun := entrywiseProjectiveHom J hJ
  invFun := entrywiseProjectiveHom J hJ
  left_inv b := by
    obtain ⟨x, rfl⟩ := J.specialToProjective_surjective b
    rw [entrywiseProjectiveHom_apply, entrywiseProjectiveHom_apply]
    congr 1
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact J.conj_involutive _
  right_inv b := by
    obtain ⟨x, rfl⟩ := J.specialToProjective_surjective b
    rw [entrywiseProjectiveHom_apply, entrywiseProjectiveHom_apply]
    congr 1
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact J.conj_involutive _
  map_mul' := map_mul (entrywiseProjectiveHom J hJ)

@[simp] public theorem entrywiseProjectiveAut_specialToProjective (x : J.specialSubgroup) :
    entrywiseProjectiveAut J hJ (J.specialToProjective x) =
      J.specialToProjective (entrywiseSpecialAut J hJ x) := by
  exact entrywiseProjectiveHom_apply J hJ x

public theorem entrywiseProjectiveAut_isEntrywiseConjugation : J.IsEntrywiseConjugation (entrywiseProjectiveAut J hJ) := by
  intro x
  exact ⟨entrywiseSpecialAut J hJ x, entrywiseSpecialAut_apply_val J hJ x,
    entrywiseProjectiveAut_specialToProjective J hJ x⟩


/-- There are at most two field automorphisms of a field of prime-square order. -/
public theorem fieldAut_card_le_two [Finite E] {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card E = p ^ 2) : Nat.card (E ≃+* E) ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  let := Fintype.ofFinite E
  let := charP_of_card_eq_prime_pow (by simpa using hcard : Fintype.card E = p ^ 2)
  let := ZMod.algebra E p
  have hdim : Module.finrank (ZMod p) E = 2 := by
    apply Nat.pow_right_injective hp.two_le
    simpa only [Nat.card_zmod, hcard] using
      (Module.natCard_eq_pow_finrank (K := ZMod p) (V := E)).symm
  let f : (E ≃+* E) → (E ≃ₐ[ZMod p] E) := fun σ =>
    AlgEquiv.ofRingEquiv (f := σ) (fun z =>
      congrArg (fun f : ZMod p →+* E => f z)
        (Subsingleton.elim (σ.toRingHom.comp (algebraMap (ZMod p) E))
          (algebraMap (ZMod p) E)))
  have hf : Function.Injective f := by
    intro σ τ h
    exact RingEquiv.ext fun x => congrArg (fun g : E ≃ₐ[ZMod p] E => g x) h
  exact (Nat.card_le_card_of_injective f hf).trans (by
    rw [Nat.card_eq_fintype_card]
    exact (AlgEquiv.card_le (F := ZMod p) (K := E)).trans_eq hdim)

/-- Every field automorphism is trivial or the stored Hermitian conjugation.
No hypothesis on its order or on semilinear faithfulness is required. -/
public theorem fieldAut_eq_one_or_conj [Finite E] {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card E = p ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = p)
    (σ : E ≃+* E) : σ = 1 ∨ σ = J.conj := by
  classical
  have hJne : J.conj ≠ 1 := by
    intro h
    let e : {x : E // J.conj x = x} ≃ E :=
      { toFun := Subtype.val
        invFun := fun x => ⟨x, by rw [h]; rfl⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hc := Nat.card_congr e
    rw [hcard, hfixed] at hc
    have := hp.two_le
    nlinarith
  by_cases hσ : σ = 1
  · exact Or.inl hσ
  by_cases hσJ : σ = J.conj
  · exact Or.inr hσJ
  let : Finite (E ≃+* E) := Finite.of_injective (fun σ : E ≃+* E => (σ : E → E))
    DFunLike.coe_injective
  let := Fintype.ofFinite (E ≃+* E)
  have hle : ({1, σ, J.conj} : Finset (E ≃+* E)).card ≤ 2 :=
    (Finset.card_le_univ _).trans (by
      simpa only [← Nat.card_eq_fintype_card] using fieldAut_card_le_two hp hcard)
  simp [hσJ, Ne.symm hσ, Ne.symm hJne] at hle

/-- A supplied semilinear formula for an outer involution is a unitary twist
of entrywise conjugation. Arbitrary-automorphism coverage is not asserted. -/
public theorem outer_twist_of_semilinear [Finite E] {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card E = p ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = p)
    {γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hγ : J.IsEntrywiseConjugation γ)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ^ 2 = 1)
    (houter : ¬ ∃ k, a = MulAut.conj k)
    (hsem : ∃ σ : E ≃+* E, J.HasUnitarySemilinearForm a σ) :
    ∃ u : J.unitarySubgroup, a = J.unitaryConj u * γ := by
  obtain ⟨σ, hσ⟩ := hsem
  rcases fieldAut_eq_one_or_conj J hp hcard hfixed σ with rfl | rfl
  · obtain ⟨u, rfl⟩ := (HasUnitarySemilinearForm.one_iff J).mp hσ
    exact False.elim (houter (J.unitaryConj_is_inner_of_sq_eq_one u ha))
  · exact (HasUnitarySemilinearForm.conj_iff J hγ).mp hσ

end BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter
