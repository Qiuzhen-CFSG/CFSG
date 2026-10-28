module
public import Theory.SpecificGroups.SU3.StronglyClosedPairs.Overgroup.Graph
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Coverage
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.FieldFaithfulness
public import Theory.SpecificGroups.SU3.EvenTwoRank.Automorphisms

/-!
# Excluding outer factors in a root-normalizing two-group

Take a power whose nontrivial field part is the Hermitian involution. Its
upper triangular matrix splits as a root matrix times a diagonal matrix.
Remove the root actor inside the same two-group. The remaining diagonal
graph actor squares to one by the odd diagonal exponent calculation.

If the factor's inner part is elementary, the original graph twist has
fourth power one and hence square one. If its inner part contains the root,
removing that root yields a square-one graph actor in the factor. Both cases
contradict innerness of all involutions, by field-component faithfulness.
Arbitrary higher two-powers of the original field parameter are allowed.

Source: GLS3, Theorem 2.5.12 and §2.7; Huppert II.10.12; the unitary model
calculation for Aschbacher (1975), Lemma 3.4, pp.94–96.
-/

open Matrix Subgroup BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.StronglyClosedPairs
open ExtensionBorel BorelTorus BorelTorus.SemilinearActors
variable {E : Type*} [Field E] [Finite E] [CharP E 2]
variable (J : HermitianForm 3 E)
variable (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
variable {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2^n)^2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)

omit [CharP E 2] in
include hJ hn hcard hfixed in
private theorem inner_semilinear_field_eq_one
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (σ : E ≃+* E)
    (hform : J.HasUnitarySemilinearForm a σ)
    (ha : a ∈ (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).range) : σ = 1 := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨u, rfl⟩ := J.specialToProjective_surjective x
  have hone : J.HasUnitarySemilinearForm (MulAut.conj (J.specialToProjective u)) 1 :=
    (HasUnitarySemilinearForm.one_iff J).mpr
      ⟨⟨u.val, u.property.1⟩, (J.unitaryConj_special_is_inner u).symm⟩
  apply J.semilinear_identity_field_eq_one n hn hJ hcard hfixed σ
  simpa only [inv_mul_cancel, inv_one, one_mul] using (hone.inv J hJ).mul J hJ hform

private theorem exists_involution_power {G : Type*} [Group G] (a : G)
    {r : ℕ} (hr : a ^ (2 ^ r) = 1) (ha : a ≠ 1) :
    ∃ k : ℕ, (a ^ k) ^ 2 = 1 ∧ a ^ k ≠ 1 := by
  induction r with
  | zero => simp only [pow_zero, pow_one] at hr; exact (ha hr).elim
  | succ r ih =>
    by_cases h : a ^ (2 ^ r) = 1
    · exact ih h
    · refine ⟨2 ^ r, ?_, h⟩
      rw [← pow_mul, ← pow_succ]
      exact hr

omit [CharP E 2] in
include hn hcard hfixed in
private theorem graph_factorization
    (A : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hA : IsPGroup 2 A)
    (hUA : (projectiveRoot J hJ).map MulAut.conj ≤ A)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ∈ A)
    (hform : J.HasUnitarySemilinearForm a J.conj)
    (hroot : (projectiveRoot J hJ).map a.toMonoidHom = projectiveRoot J hJ) :
    ∃ z : hermitianUnipotentCoord J, ∃ d : J.unitarySubgroup,
      (∀ i j, i ≠ j → d.val.val i j = 0) ∧
      a = MulAut.conj (hermitianUnipotentPSU J hJ z) *
        (J.unitaryConj d * fieldActor J hJ J.conj) ∧
      (J.unitaryConj d * fieldActor J hJ J.conj)^2 = 1 := by
  obtain ⟨u, hu⟩ := hform
  obtain ⟨h10, h20, h21⟩ := projective_semilinear_upper J hJ hcard hfixed a J.conj u hu hroot
  obtain ⟨z, d, hf, hd, _⟩ := upper_unitary_factorization J hJ u h10 h20 h21
  have he : a = MulAut.conj (hermitianUnipotentPSU J hJ z) *
      (J.unitaryConj d * fieldActor J hJ J.conj) := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [hu]
    simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv, unitaryConj_apply_val, fieldActor_apply_val,
      hermitianUnipotentPSU_val, hf, map_mul]
    group
  have hβ : J.unitaryConj d * fieldActor J hJ J.conj ∈ A := by
    have hz : MulAut.conj (hermitianUnipotentPSU J hJ z) ∈ A := hUA ⟨_, ⟨z, rfl⟩, rfl⟩
    have hh := A.mul_mem (A.inv_mem hz) ha
    rwa [he, inv_mul_cancel_left] at hh
  obtain ⟨r, hr⟩ := hA ⟨_, hβ⟩
  exact ⟨z, d, hd, he, diagonal_graph_square_one J hJ (by omega) hcard d hd
    (congrArg Subtype.val hr)⟩

include hn hcard hfixed in
/-- In a root-normalizing two-group containing every root inner actor, a factor
with only inner involutions is inner if its inner part is elementary or contains
the whole root group. The field parameter may have arbitrary two-power order. -/
public theorem root_normalizing_factor_inner
    (A B : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hA : IsPGroup 2 A) (hBA : B ≤ A)
    (hUA : (projectiveRoot J hJ).map MulAut.conj ≤ A)
    (hstable : ∀ a ∈ A, (projectiveRoot J hJ).map a.toMonoidHom = projectiveRoot J hJ)
    (hinv : ∀ b ∈ B, b^2 = 1 → b ∈ (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).range)
    (hpart : (∀ x : ProjectiveSpecialUnitaryMatrixGroup J, MulAut.conj x ∈ B → x^2 = 1) ∨
      (projectiveRoot J hJ).map MulAut.conj ≤ B) :
    B ≤ (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).range := by
  have hnfix : ∃ t : E, J.conj t ≠ t := by
    by_contra! h
    exact J.conj_ne_one_of_card n hn hcard hfixed (RingEquiv.ext h)
  have hi := MulAut.conj_injective_of_center_eq_bot (EvenTwoRank.standard_center_eq_bot J hJ hnfix)
  have hid (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ∈ A)
      (hf : J.HasUnitarySemilinearForm a 1) : a ∈ (projectiveRoot J hJ).map MulAut.conj := by
    obtain ⟨u, hu⟩ := hf
    obtain ⟨h10, h20, h21⟩ := projective_semilinear_upper J hJ hcard hfixed a 1 u hu (hstable a ha)
    apply projective_identity_field_mem_root_inner J hJ hcard (by omega) A hA hUA a ha u h10 h20 h21
    intro x
    have hx := hu x
    change (a x).val = ProjGenLinGroup.mk u.val * ProjGenLinGroup.map (RingHom.id E) x.val * (ProjGenLinGroup.mk u.val)⁻¹ at hx
    simpa only [ProjGenLinGroup.map_id, MonoidHom.id_apply] using hx
  intro a haB
  obtain ⟨r, hr⟩ := hA ⟨a, hBA haB⟩
  obtain ⟨σ, hs⟩ := J.semilinear_coverage n hn hJ hcard hfixed a
  obtain ⟨σ, hs, s, hσpow⟩ := hs.exists_twoPower_field J hJ (congrArg Subtype.val hr)
  by_cases hσ : σ = 1
  · obtain ⟨x, _, hx⟩ := hid a (hBA haB) (hσ ▸ hs)
    exact ⟨x, hx⟩
  exfalso
  obtain ⟨k, hk, hkne⟩ := exists_involution_power σ hσpow hσ
  have hkJ := J.field_involution_eq_conj n hn hcard hfixed (σ^k) hk hkne
  have hform : J.HasUnitarySemilinearForm (a^k) J.conj := hkJ ▸ hs.pow J hJ k
  have haB' := B.pow_mem haB k
  have haA' := hBA haB'
  obtain ⟨z, d, hd, he, hβsq⟩ := graph_factorization J hJ hn hcard hfixed
    A hA hUA (a^k) haA' hform (hstable _ haA')
  have hnotinner {b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
      (hf : J.HasUnitarySemilinearForm b J.conj) :
      b ∉ (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).range := by
    intro hb
    exact J.conj_ne_one_of_card n hn hcard hfixed
      (inner_semilinear_field_eq_one J hJ hn hcard hfixed b J.conj hf hb)
  rcases hpart with hsmall | hfull
  · have hfield : J.HasUnitarySemilinearForm ((a^k)^2) 1 := by
      have hJJ : J.conj^2 = 1 := by ext x; exact J.conj_involutive x
      simpa only [hJJ] using hform.pow J hJ 2
    obtain ⟨x, _, hx⟩ := hid ((a^k)^2) (A.pow_mem haA' 2) hfield
    have hxB : MulAut.conj x ∈ B := hx.symm ▸ B.pow_mem haB' 2
    have h4 : (a^k)^4 = 1 := by
      rw [show (4 : ℕ) = 2*2 from rfl, pow_mul, ← hx, ← map_pow, hsmall x hxB, map_one]
    have h2 : (a^k)^2 = 1 := by
      rw [he] at h4 ⊢
      exact root_diagonal_graph_fourth J hJ hnfix hi d hd hβsq z h4
    exact hnotinner hform (hinv _ haB' h2)
  · have hz : MulAut.conj (hermitianUnipotentPSU J hJ z) ∈ B := hfull ⟨_, ⟨z, rfl⟩, rfl⟩
    have hβB := B.mul_mem (B.inv_mem hz) haB'
    rw [he, inv_mul_cancel_left] at hβB
    apply hnotinner (b := J.unitaryConj d * fieldActor J hJ J.conj) _ (hinv _ hβB hβsq)
    refine ⟨d, fun x => ?_⟩
    rw [MulAut.mul_apply, J.unitaryConj_apply_val, fieldActor_apply_val]

end BenderSuzuki.MatrixGroups.HermitianForm.StronglyClosedPairs
