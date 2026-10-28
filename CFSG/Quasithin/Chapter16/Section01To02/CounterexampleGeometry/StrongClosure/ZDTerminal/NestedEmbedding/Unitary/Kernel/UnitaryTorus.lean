module

public import BenderSuzuki.Converse.PSU3
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.InternalRigidity.Unitary.Sylow

/-!
# A fixed-field torus element with trivial Sylow centralizer

For the standard three-dimensional Hermitian form over a field of order
`q²`, with fixed field of order `q = 2ⁿ ≥ 4`, choose a fixed-field unit
`k ≠ 1`. Its genuine projective diagonal matrix normalizes the Hermitian
root image and scales the two root coordinates by `k⁻¹` and `k⁻²`.
Neither scalar is one in characteristic two. Injectivity of the projective
root homomorphism therefore gives trivial centralizer in the root image.
The existing root Sylow identification and Sylow conjugacy transport this
element to every Sylow two-subgroup of the actual projective matrix group.

Source: Huppert, Volume I, II.10.12(b), the root and torus matrices and their
conjugation formula; the intrinsic unitary input for the terminal argument
of Aschbacher (1975), Lemma 3.4, printed p.96.
-/

open Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm.EvenInner
open scoped Pointwise
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
variable {E : Type*} [Field E] [Finite E]

omit [Finite E] in
private theorem torus_fixed_root [CharP E 2]
    (J : HermitianForm 3 E) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (k : Eˣ) (hk : J.conj (k : E) = k) (hk1 : (k : E) ≠ 1)
    (z : hermitianUnipotentCoord J)
    (hc : Commute (hermitianTorusPSU J hJ k) (hermitianUnipotentPSU J hJ z)) :
    hermitianUnipotentPSU J hJ z = 1 := by
  -- Projective commutation implies equality of the actual root coordinates.
  have he : hermitianTorusAction J k z = z :=
    BenderSuzuki.Converse.hUPSU_injective J hJ
      (mul_right_cancel ((hermitianTorusPSU_mul_unipotent J hJ k z).symm.trans hc.eq))
  have ha := congrArg (fun w : hermitianUnipotentCoord J => w.val.1) he
  have hb := congrArg (fun w : hermitianUnipotentCoord J => w.val.2) he
  rw [hermitianTorusAction_fst, hk] at ha
  rw [hermitianTorusAction_snd, hk] at hb
  have hscale : (k : E) * (k : E)⁻¹ ^ 2 = (k : E)⁻¹ := by
    field_simp
  rw [mul_assoc, hscale] at ha
  have hki : (k : E)⁻¹ ≠ 1 := by simpa using hk1
  have hki2 : (k : E)⁻¹ ^ 2 ≠ 1 := by
    intro h
    apply hki
    exact CharTwo.sq_injective (h.trans (one_pow 2).symm)
  have ha0 : z.val.1 = 0 := by
    by_contra ha0
    exact hki ((mul_eq_left₀ ha0).mp ha)
  have hb0 : z.val.2 = 0 := by
    rw [mul_assoc, ← pow_two] at hb
    by_contra hb0
    exact hki2 ((mul_eq_left₀ hb0).mp hb)
  have hz : z = 1 := Subtype.ext (Prod.ext ha0 hb0)
  rw [hz, map_one]

private theorem torus_normalizes_root
    (J : HermitianForm 3 E) (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) (k : Eˣ) :
    hermitianTorusPSU J hJ k ∈ normalizer (rootImage J hJ : Set _) := by
  apply mem_normalizer_fintype
  rintro x ⟨z, rfl⟩
  refine ⟨hermitianTorusAction J k z, ?_⟩
  rw [hermitianTorusPSU_mul_unipotent, mul_inv_cancel_right]

/-- Every Sylow two-subgroup of the actual projective unitary matrix group
has a normalizer element whose centralizer in that Sylow subgroup is trivial. -/
public theorem unitary_exists_fixedPointFree_sylow_normalizer
    (n : ℕ) (hn : 2 ≤ n) (J : HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {z : E // J.conj z = z} = 2^n)
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ d : ProjectiveSpecialUnitaryMatrixGroup J,
      d ∈ normalizer (P : Set _) ∧ ∀ x ∈ P, Commute d x → x = 1 := by
  let : CharP E 2 := BenderSuzuki.Converse.charP_two_of_card
    (n := n * 2) (by omega) (by rw [hcard, pow_mul])
  have h4 : 4 ≤ Nat.card (BenderSuzuki.Converse.psuFix J) := by
    rw [hfixed]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn
  obtain ⟨k, hkfix, hk0, hk1⟩ := BenderSuzuki.Converse.exists_fixed_ne_zero_one J h4
  let u : Eˣ := Units.mk0 k hk0
  let d := hermitianTorusPSU J hJ u
  let S := InternalRigidity.UnitarySylow.rootSylow J hJ (by omega : n ≠ 0) hcard hfixed
  have hS : (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = rootImage J hJ := rfl
  have hd : d ∈ normalizer (S : Set _) := by
    change d ∈ normalizer ((S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : Set _)
    rw [hS]
    exact torus_normalizes_root J hJ u
  have hf : ∀ x ∈ S, Commute d x → x = 1 := by
    intro x hx hc
    change x ∈ (S : Subgroup _) at hx
    rw [hS] at hx
    obtain ⟨z, rfl⟩ := hx
    exact torus_fixed_root J hJ u hkfix hk1 z hc
  -- Conjugate both the root Sylow subgroup and its torus element.
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) S P
  let e := MulAut.conj g
  have hmap : (S : Subgroup _).map e.toMonoidHom = (P : Subgroup _) := by
    exact congrArg Sylow.toSubgroup hg
  refine ⟨e d, ?_, ?_⟩
  · change e d ∈ normalizer ((P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : Set _)
    rw [← hmap, ← Subgroup.map_equiv_normalizer_eq]
    exact mem_map_of_mem e.toMonoidHom hd
  · intro x hx hc
    change x ∈ (P : Subgroup _) at hx
    rw [← hmap] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hyc : Commute d y := by
      apply e.injective
      rw [map_mul, map_mul]
      exact hc.eq
    rw [hf y hy hyc, map_one]

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
