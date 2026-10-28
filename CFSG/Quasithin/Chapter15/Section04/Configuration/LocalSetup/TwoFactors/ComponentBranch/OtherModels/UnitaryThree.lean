module

public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Theory.GroupAction.FourGroupOddCenter
public import Theory.GroupAction.FourGroupSylowCentralizer
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.OtherModels.UnitaryThree.SylowGeometry
public import Mathlib.GroupTheory.IsPerfect

/-!
# The unitary-three fixed-action obstruction

In F.6.18(10)–(11), the unitary alternative has a prime fixed-field order
`p ≡ 3 mod 8`. Its matrix field has order `p²`; the fixed field of the stored
Hermitian conjugation has order `p`. These two cardinalities must remain
separate throughout the model theorems.

The source lists the component Sylow model `C₄ ≀ C₂`, of order 32 with cyclic
center. The Sylow calculation holds for every nondegenerate Hermitian form.
Every involution fixing such a subgroup pointwise is inner: normalization of
an outer involution identifies its fixed subgroup with a subgroup of a
ternary orthogonal group whose order is not divisible by 32. A faithful
four-group action is then excluded by uniqueness of the involution in the
cyclic Sylow center. For SU₃, the nontrivial odd center supplies the fixed-subgroup
obstruction directly. If its center is trivial, the natural projective map
is an actual isomorphism and transports the faithful action and its Sylow
subgroup.

The final theorems discharge both local inputs, including arbitrary-automorphism
coverage and arbitrary-form transport, and establish the intrinsic obstruction
for the SU₃ and PSU₃ components in F.6.18(10)–(11). Simplicity and perfectness
are inherited from the source component. Compatible actions of the graph
extension and quotient transport are handled by the parent component argument.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, F.6.18(10)–(11), printed pp.309–310 (PDF pp.320–321),
and the component argument of 15.4.18, printed pp.1162–1163.
-/

open Subgroup
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.OtherModels
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
variable {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]

/-- The nontrivial-center case for the actual SU₃ model, when its projective image is centerless. -/
public theorem special_unitary_nontrivial_center_fixed_action_obstruction
    (hZ : center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥)
    (hne : center J.specialSubgroup ≠ ⊥)
    (hA : Nat.card A = 4) (ρ : A →* MulAut J.specialSubgroup) :
    ∃ a : A, a ≠ 1 ∧
      ¬ centralizer (pCore 2 (ρ a).fixedSubgroup : Set (ρ a).fixedSubgroup) ≤
        pCore 2 (ρ a).fixedSubgroup := by
  apply Theory.GroupAction.exists_fixedSubgroup_not_selfCentralizing_twoCore_of_odd_center
    ?_ hne hA ρ
  rw [← J.specialToProjective_ker_eq_center hZ]
  exact J.odd_card_specialToProjective_ker

/-- Transfer a proved projective exclusion to SU₃: use its odd center or transport the action through the actual special-to-projective isomorphism. The projective exclusion remains an explicit premise. -/
public theorem special_unitary_fixed_action_obstruction_of_projective_exclusion
    (hZ : center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥)
    (hprojective : ∀ (Q : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
      (σ : A →* MulAut (ProjectiveSpecialUnitaryMatrixGroup J)),
      (∀ a : A, ∀ x : Q, σ a x = x) → ¬ Function.Injective σ)
    (P : Sylow 2 J.specialSubgroup) (hA : Nat.card A = 4)
    (ρ : A →* MulAut J.specialSubgroup) (hinj : Function.Injective ρ)
    (hfix : ∀ a : A, ∀ x : P, ρ a x = x) :
    ∃ a : A, a ≠ 1 ∧
      ¬ centralizer (pCore 2 (ρ a).fixedSubgroup : Set (ρ a).fixedSubgroup) ≤
        pCore 2 (ρ a).fixedSubgroup := by
  classical
  by_cases hcenter : center J.specialSubgroup = ⊥
  · let e := J.specialProjectiveEquivOfCenterEqBot hcenter
    let σ := (MulAut.congr e).toMonoidHom.comp ρ
    let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
    have hσ : Function.Injective σ := (MulAut.congr e).injective.comp hinj
    have hσfix : ∀ a : A, ∀ x : Q, σ a x = x := by
      intro a x
      have hx : x.val ∈ (P : Subgroup J.specialSubgroup).map e.toMonoidHom := x.property
      obtain ⟨y, hy, hxy⟩ := hx
      change e (ρ a (e.symm x.val)) = x.val
      rw [← hxy]
      change e (ρ a (e.symm (e y))) = e y
      rw [e.symm_apply_apply, hfix a ⟨y, hy⟩]
    exact (hprojective Q σ hσfix hσ).elim
  · exact special_unitary_nontrivial_center_fixed_action_obstruction J hZ hcenter hA ρ


private theorem center_eq_bot_of_perfect_simple {K : Type*} [Group K]
    [Group.IsPerfect K] [IsSimpleGroup K] : center K = ⊥ := by
  rcases (inferInstance : (center K).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative K (center_eq_top_iff.mp h)).elim

/-- Conditional projective exclusion from the Sylow calculation and the innerness of involutions fixing a subgroup of order 32. The final odd-prime theorem below supplies both model premises. -/
public theorem projective_unitary_not_injective_of_local_involutions
    [Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J)]
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hgeometry : ∀ P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
      Nat.card P = 32 ∧ IsCyclic (center P))
    (hinner : ∀ Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J), Nat.card Q = 32 →
      ∀ α : MulAut (ProjectiveSpecialUnitaryMatrixGroup J), α ^ 2 = 1 →
      (∀ x : Q, α x = x) → ∃ x, α = MulAut.conj x)
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (hA : Nat.card A = 4) (ρ : A →* MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hfix : ∀ a : A, ∀ x : P, ρ a x = x) : ¬ Function.Injective ρ := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let : IsCyclic (center P) := (hgeometry P).2
  exact Theory.GroupAction.not_injective_elementaryFour_fixing_sylow_of_inner P
    center_eq_bot_of_perfect_simple
    (hinner P (hgeometry P).1) hA ρ hfix

/-- Conditional special-unitary assembly from the same two projective local inputs. Perfectness is inherited from the source component; no extra automorphism-lifting premise is needed. -/
public theorem special_unitary_fixed_action_obstruction_of_local_involutions
    [Group.IsPerfect J.specialSubgroup]
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hgeometry : ∀ P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
      Nat.card P = 32 ∧ IsCyclic (center P))
    (hinner : ∀ Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J), Nat.card Q = 32 →
      ∀ α : MulAut (ProjectiveSpecialUnitaryMatrixGroup J), α ^ 2 = 1 →
      (∀ x : Q, α x = x) → ∃ x, α = MulAut.conj x)
    (P : Sylow 2 J.specialSubgroup) (hA : Nat.card A = 4)
    (ρ : A →* MulAut J.specialSubgroup) (hinj : Function.Injective ρ)
    (hfix : ∀ a : A, ∀ x : P, ρ a x = x) :
    ∃ a : A, a ≠ 1 ∧
      ¬ centralizer (pCore 2 (ρ a).fixedSubgroup : Set (ρ a).fixedSubgroup) ≤
        pCore 2 (ρ a).fixedSubgroup := by
  let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Group.IsPerfect.ofSurjective J.specialToProjective_surjective
  exact special_unitary_fixed_action_obstruction_of_projective_exclusion J
    center_eq_bot_of_perfect_simple
    (fun Q σ hf => projective_unitary_not_injective_of_local_involutions J
      hgeometry hinner Q hA σ hf) P hA ρ hinj hfix

/-- No elementary abelian group of order four acts faithfully on the actual
PSU₃(p) model while fixing a Sylow two-subgroup pointwise, for prime
`p ≡ 3 (mod 8)`. Both field cardinalities are explicit; the Hermitian form
and the automorphisms are arbitrary. -/
public theorem projective_unitary_not_injective_fixing_sylow
    [Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J)]
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3)
    (hcard : Nat.card E = p ^ 2) (hfixed : Nat.card {x : E // J.conj x = x} = p)
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (hA : Nat.card A = 4) (ρ : A →* MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hfix : ∀ a : A, ∀ x : P, ρ a x = x) : ¬ Function.Injective ρ := by
  let : Fact p.Prime := ⟨hp⟩
  exact projective_unitary_not_injective_of_local_involutions J
    (projective_unitary_sylow_geometry J p hp8 hcard hfixed)
    (HermitianForm.OddPrimeSylow.inner_of_involutive_fixing_order_thirtyTwo
      J hp hp8 hcard hfixed) P hA ρ hfix

/-- The intrinsic PSU₃(p) fixed-action obstruction needed for the unitary
component in F.6.18(10)–(11). In fact, the faithful action itself is excluded. -/
public theorem projective_unitary_fixed_action_obstruction
    [Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J)]
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3)
    (hcard : Nat.card E = p ^ 2) (hfixed : Nat.card {x : E // J.conj x = x} = p)
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (hA : Nat.card A = 4) (ρ : A →* MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hinj : Function.Injective ρ) (hfix : ∀ a : A, ∀ x : P, ρ a x = x) :
    ∃ a : A, a ≠ 1 ∧
      ¬ centralizer (pCore 2 (ρ a).fixedSubgroup : Set (ρ a).fixedSubgroup) ≤
        pCore 2 (ρ a).fixedSubgroup := by
  exact (projective_unitary_not_injective_fixing_sylow J hp hp8 hcard hfixed
    P hA ρ hfix hinj).elim

/-- The intrinsic SU₃(p) fixed-action obstruction for prime `p ≡ 3 (mod 8)`.
The nontrivial odd center gives a fixed central element outside the two-core;
if the center is trivial, the actual special-to-projective isomorphism
transports the action to the excluded PSU₃(p) case. -/
public theorem special_unitary_fixed_action_obstruction
    [Group.IsPerfect J.specialSubgroup]
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3)
    (hcard : Nat.card E = p ^ 2) (hfixed : Nat.card {x : E // J.conj x = x} = p)
    (P : Sylow 2 J.specialSubgroup) (hA : Nat.card A = 4)
    (ρ : A →* MulAut J.specialSubgroup) (hinj : Function.Injective ρ)
    (hfix : ∀ a : A, ∀ x : P, ρ a x = x) :
    ∃ a : A, a ≠ 1 ∧
      ¬ centralizer (pCore 2 (ρ a).fixedSubgroup : Set (ρ a).fixedSubgroup) ≤
        pCore 2 (ρ a).fixedSubgroup := by
  let : Fact p.Prime := ⟨hp⟩
  exact special_unitary_fixed_action_obstruction_of_local_involutions J
    (projective_unitary_sylow_geometry J p hp8 hcard hfixed)
    (HermitianForm.OddPrimeSylow.inner_of_involutive_fixing_order_thirtyTwo
      J hp hp8 hcard hfixed) P hA ρ hinj hfix

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.OtherModels
