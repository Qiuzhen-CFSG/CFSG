module

public import BenderSuzuki.MatrixGroups.SuzukiZero
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.LinearQuotient

/-!
# Two-cores of the binary Ree local quotient targets

The actual Suzuki matrix group Sz(2) has a cyclic root subgroup of order four
and index five. A normal two-subgroup lies in that Sylow subgroup and in its
Weyl conjugate. The latter is lower triangular; two matrix entries show the
intersection is trivial. For PSL₂(2), use the existing characteristic-two
matrix proof, which includes the binary field and uses no simplicity theorem.

These are target calculations for Aschbacher–Smith F.1.12(I)(5), printed
pp.263–264 of `refs/quasithin.pdf`. Construction of the maps from the full
Ree fixed group’s local seeds is a separate obligation. Sz(2) here has order
20, unlike the dihedral quotient for the Tits group in F.1.12(I)(9).
-/

public section

open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII BenderSuzuki.External Subgroup

noncomputable section
namespace ReeF4.Parabolics.Binary

private def weyl : SuzukiMatrixGroup 0 :=
  ⟨SuzukiWeylGL 0, Subgroup.subset_closure (Or.inr (Or.inr rfl))⟩

private def rootSubgroup : Subgroup (SuzukiMatrixGroup 0) :=
  (Subgroup.closure
    {A | ∃ a b : BinaryGaloisField 1, A = SuzukiRootGL 0 a b}).comap
      (SuzukiMatrixGroup 0).subtype

private theorem root_coordinates {x : SuzukiMatrixGroup 0}
    (hx : x ∈ rootSubgroup) :
    ∃ a b : BinaryGaloisField 1, x.val = SuzukiRootGL 0 a b := by
  let K := BinaryGaloisField 1
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 1
  have hpi : ∀ x : K, pi x = x ^ 2 := by
    intro x
    simpa [pi] using iterateFrobeniusEquiv_def K 2 1 x
  have hpiSq : ∀ x : K, pi (pi x) = x ^ 2 := by
    exact binaryGaloisField_tits_formula_sq 0 pi (by
      intro x
      simpa using hpi x)
  exact (suzukiRootGL_mem_closure_iff 0 pi hpiSq hpi x.val).mp hx

private def rootElement (z : BinaryGaloisField 1 × BinaryGaloisField 1) :
    rootSubgroup :=
  ⟨⟨SuzukiRootGL 0 z.1 z.2, Subgroup.subset_closure (Or.inl ⟨z.1, z.2, rfl⟩)⟩,
    Subgroup.subset_closure ⟨z.1, z.2, rfl⟩⟩

private theorem rootSubgroup_card : Nat.card rootSubgroup = 4 := by
  have hi : Function.Injective rootElement := by
    intro x y h
    have h01 := congrArg (fun A : rootSubgroup =>
      ((A.val.val : Matrix (Fin 4) (Fin 4) (BinaryGaloisField 1)) 0 1)) h
    have h02 := congrArg (fun A : rootSubgroup =>
      ((A.val.val : Matrix (Fin 4) (Fin 4) (BinaryGaloisField 1)) 0 2)) h
    apply Prod.ext
    · simpa [rootElement, SuzukiRootGL, SuzukiRootMatrix] using h01
    · simpa [rootElement, SuzukiRootGL, SuzukiRootMatrix] using h02
  have hs : Function.Surjective rootElement := by
    intro x
    obtain ⟨a, b, hab⟩ := root_coordinates x.property
    exact ⟨(a, b), Subtype.ext (Subtype.ext hab.symm)⟩
  have hc : Nat.card (BinaryGaloisField 1) = 2 := by
    simpa [BinaryGaloisField] using GaloisField.card 2 1 (by decide)
  rw [← Nat.card_congr (Equiv.ofBijective rootElement ⟨hi, hs⟩), Nat.card_prod, hc]

private theorem root_eq_one_of_conj_mem {x : SuzukiMatrixGroup 0}
    (hx : x ∈ rootSubgroup)
    (hwx : weyl * x * weyl⁻¹ ∈ rootSubgroup) : x = 1 := by
  obtain ⟨a, b, hab⟩ := root_coordinates hx
  obtain ⟨c, d, hcd⟩ := root_coordinates hwx
  have hmatrix : SuzukiWeylGL 0 * SuzukiRootGL 0 a b * (SuzukiWeylGL 0)⁻¹ =
      SuzukiRootGL 0 c d := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, weyl, hab] using hcd
  have h32 := congrArg (fun A : GL (Fin 4) (BinaryGaloisField 1) =>
    (A : Matrix (Fin 4) (Fin 4) (BinaryGaloisField 1)) 3 2) hmatrix
  have h31 := congrArg (fun A : GL (Fin 4) (BinaryGaloisField 1) =>
    (A : Matrix (Fin 4) (Fin 4) (BinaryGaloisField 1)) 3 1) hmatrix
  have ha : a = 0 := by
    simpa [SuzukiWeylGL, SuzukiWeylMatrix, SuzukiRootGL, SuzukiRootMatrix,
      Matrix.mul_apply, Fin.sum_univ_four] using h32
  have hb : b = 0 := by
    simpa [SuzukiWeylGL, SuzukiWeylMatrix, SuzukiRootGL, SuzukiRootMatrix,
      Matrix.mul_apply, Fin.sum_univ_four] using h31
  apply Subtype.ext
  simpa only [ha, hb, suzukiRootGL_zero_zero, Subgroup.coe_one] using hab

/-- The solvable order-20 Suzuki matrix group has trivial two-core. -/
theorem suzuki_twoCore_eq_bot : pCore 2 (SuzukiMatrixGroup 0) = ⊥ := by
  have hRp : IsPGroup 2 rootSubgroup :=
    IsPGroup.of_card (n := 2) rootSubgroup_card
  have hi : rootSubgroup.index = 5 := by
    have h := rootSubgroup.card_mul_index
    rw [rootSubgroup_card, suzukiZero_card] at h
    omega
  have hle : pCore 2 (SuzukiMatrixGroup 0) ≤ rootSubgroup :=
    pCore_isPGroup.le_sylow_of_normal (hRp.toSylow (by rw [hi]; decide))
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro x hx
  exact root_eq_one_of_conj_mem (hle hx)
    (hle ((inferInstance : (pCore 2 (SuzukiMatrixGroup 0)).Normal).conj_mem x hx weyl))

/-- The exact projective linear target over the binary Ree field has trivial two-core. -/
theorem linear_twoCore_eq_bot : pCore 2 (LargeLocalSeeds.LinearQuotient 0) = ⊥ :=
  Atlas.RankOneFieldAutomorphisms.psl_twoCore_eq_bot

end ReeF4.Parabolics.Binary
