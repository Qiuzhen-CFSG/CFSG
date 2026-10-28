module

public import Theory.SpecificGroups.Triality.FullParabolicActions
public import Theory.GroupTheory.Commutator.PerfectClassTwoAction
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# Restrictions on all arms-parabolic candidates

A perfect actor centralizes the special radical's center: its image in the
cyclic full-parabolic quotient is trivial. If its whole radical commutator
has exponent two, the class-two commutator lemma kills that action. The
full-parabolic centralizer bound and the radical's two-group structure then
make the perfect actor trivial. Applying this to a candidate's solvable
residual proves solvability without assuming subnormality or two-perfection.

A subnormal candidate therefore has full-Levi image centralizing the genuine
simple PSL₂(q³) subsystem. This keeps the full torus and includes q = 2.
It does not assert that an O²-perfect subgroup lies in O²′ of the parabolic.
The remaining central-torus action calculation is separate.

Sources: Aschbacher--Smith C.1.7/C.1.12, E.6.8 and F.1.11--12
(`refs/quasithin.pdf`, pp.123--124, 247--248, 262--264);
GLS3 §2.6 (`refs/KGroup/GLS3/chapter2.tex`).
-/

public section

open Subgroup
open scoped commutatorElement
noncomputable section
namespace Triality.Standard.Parabolics
open RadicalCoordinates RadicalCoordinates.Centers

private theorem abelian_of_squares {G : Type*} [Group G] (N : Subgroup G)
    (hsq : ∀ n ∈ N, n ^ 2 = 1) : ⁅N, N⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro x hx
  apply mem_centralizer_iff.mpr
  intro y hy
  have hi (n : G) (hn : n ∈ N) : n⁻¹ = n :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hsq n hn)
  calc
    y * x = (x * y)⁻¹ := by rw [mul_inv_rev, hi x hx, hi y hy]
    _ = x * y := hi _ (N.mul_mem hx hy)

private theorem perfect_le_localFactor (P : Parameters) (hp : P.prime = 2)
    (X : Subgroup (parabolic P .arms)) [Group.IsPerfect X] :
    X ≤ (localFactor P .arms).subgroupOf (parabolic P .arms) := by
  let : IsCyclic (parabolic P .arms ⧸
      (localFactor P .arms).subgroupOf (parabolic P .arms)) :=
    parabolic_quotient_isCyclic P hp .arms
  let : CommGroup (parabolic P .arms ⧸
      (localFactor P .arms).subgroupOf (parabolic P .arms)) := IsCyclic.commGroup
  exact le_of_isPerfect_of_solvable_quotient _ _

/-- Even without subnormality, a perfect candidate with square-one radical
commutator is trivial. -/
theorem arms_perfect_eq_bot_of_commutator_squares
    (P : Parameters) (hp : P.prime = 2)
    (X : Subgroup (parabolic P .arms)) [Group.IsPerfect X]
    (hsq : ∀ z ∈ ⁅(radical P .arms).subgroupOf (parabolic P .arms), X⁆,
      (z : parabolic P .arms) ^ 2 = 1) : X = ⊥ := by
  let D := parabolic P .arms
  let R := radical P .arms
  let E := X.map D.subtype
  let : Group.IsPerfect E := Group.IsPerfect.map D.subtype
  have hED : E ≤ D := map_subtype_le X
  have hEL : E ≤ localFactor P .arms := by
    rintro x ⟨y, hy, rfl⟩
    exact perfect_le_localFactor P hp X hy
  have hmap : (⁅R.subgroupOf D, X⁆).map D.subtype = ⁅R, E⁆ := by
    rw [map_commutator, map_subgroupOf_eq_of_le (radical_le_parabolic P .arms)]
  have hab : ⁅⁅R, E⁆, ⁅R, E⁆⁆ = ⊥ := by
    apply abelian_of_squares
    intro z hz
    rw [← hmap] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact congrArg Subtype.val (hsq w hw)
  have hclass : ⁅R, R⁆ ≤ highestRoot P := by
    rw [← embedded_center_radical_arms P hp, center_radical_arms_eq_commutator P hp,
      map_subtype_commutator]
  have hcenter : R ⊓ centralizer (R : Set (Carrier P)) ≤ highestRoot P := by
    rw [← embedded_center_radical_arms P hp]
    rintro x ⟨hx, hc⟩
    refine ⟨⟨x, hx⟩, mem_center_iff.mpr ?_, rfl⟩
    intro r
    exact Subtype.ext (mem_centralizer_iff.mp hc r.val r.property)
  have hfix : ⁅highestRoot P, E⁆ = ⊥ := by
    rw [commutator_comm]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [← embedded_center_unipotent P hp]
    exact hEL.trans (localFactor_arms_le_centralizer_center_unipotent P hp)
  have hRE : ⁅R, E⁆ = ⊥ :=
    commutator_eq_bot_of_perfect_abelian_classTwo_action R (highestRoot P) E
      (hED.trans ((normal_subgroupOf_iff_le_normalizer
        (radical_le_parabolic P .arms)).mp (radical_normal P .arms)))
      hclass hcenter hfix hab
  have hER : E ≤ R := by
    apply le_trans (le_inf hED ?_) (parabolic_centralizer_radical_le P hp .arms)
    rw [commutator_comm] at hRE
    exact commutator_eq_bot_iff_le_centralizer.mp hRE
  have hE : E = ⊥ := by
    by_contra he
    let : Nontrivial E := (nontrivial_iff_ne_bot E).mpr he
    let : Group.IsNilpotent E := (radical_isPGroup P hp .arms).to_le hER |>.isNilpotent
    exact Group.IsPerfect.not_isNilpotent E inferInstance
  exact le_bot_iff.mp (((map_eq_bot_iff X).mp hE).trans_eq
    ((MonoidHom.ker_eq_bot_iff D.subtype).mpr D.subtype_injective))

/-- Every square-one candidate is solvable; no subnormality or two-perfection
is used in this restriction. -/
theorem arms_candidate_isSolvable_of_commutator_squares
    (P : Parameters) (hp : P.prime = 2)
    (X : Subgroup (parabolic P .arms))
    (hsq : ∀ z ∈ ⁅(radical P .arms).subgroupOf (parabolic P .arms), X⁆,
      (z : parabolic P .arms) ^ 2 = 1) : Group.IsSolvable X := by
  let E := (solvableResidual X).map X.subtype
  let : Group.IsPerfect E := Group.IsPerfect.map X.subtype
  have he : E = ⊥ := arms_perfect_eq_bot_of_commutator_squares P hp E
    (fun z hz => hsq z (commutator_mono le_rfl (map_subtype_le _) hz))
  have hres : solvableResidual X = ⊥ := by
    exact map_injective X.subtype_injective (by simpa using he)
  obtain ⟨n, hn⟩ := exists_derivedSeries_eq_solvableResidual (G := X)
  exact ⟨n, hn.trans hres⟩

private theorem armsLevi_simple (P : Parameters) (hp : P.prime = 2) :
    IsSimpleGroup (levi P .arms) := by
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ExtensionField P)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [card_extensionField]
      exact (by decide : 4 ≤ 2 ^ 3).trans (Nat.pow_le_pow_left P.q_ge_two 3))
  exact (leviArmsEquivPSL2 P hp).isSimpleGroup

/-- A subnormal candidate's image in the full Levi centralizes its simple
subsystem. The torus and all original radical components are retained. -/
theorem arms_candidate_fullLeviImage_centralizes_levi
    (P : Parameters) (hp : P.prime = 2)
    (X : Subgroup (parabolic P .arms)) (hsub : X.IsSubnormal)
    (hsq : ∀ z ∈ ⁅(radical P .arms).subgroupOf (parabolic P .arms), X⁆,
      (z : parabolic P .arms) ^ 2 = 1) :
    X.map (fullLeviProjection P hp .arms) ≤ centralizer
      ((levi P .arms).subgroupOf (fullLevi P .arms) : Set (fullLevi P .arms)) := by
  let L := (levi P .arms).subgroupOf (fullLevi P .arms)
  have hLF : levi P .arms ≤ fullLevi P .arms := descendSubgroup_mono P le_sup_left
  have hn : L.Normal := by
    apply normal_subgroupOf_of_le_normalizer
    rw [fullLevi_eq P hp .arms]
    exact sup_le (levi P .arms).le_normalizer (torus_le_normalizer_levi P hp .arms)
  let e := subgroupOfEquivOfLe hLF
  let : IsSimpleGroup (levi P .arms) := armsLevi_simple P hp
  let : Group.IsPerfect (levi P .arms) := levi_arms_isPerfect P hp
  let : IsSimpleGroup L := e.isSimpleGroup
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
    e.symm.surjective
  let : Group.IsSolvable X := arms_candidate_isSolvable_of_commutator_squares P hp X hsq
  let Y := X.map (fullLeviProjection P hp .arms)
  let : Group.IsSolvable Y := Group.isSolvable_of_surjective
    ((fullLeviProjection P hp .arms).subgroupMap_surjective X)
  rcases simple_subnormal_dichotomy L Y hn.isSubnormal
      (hsub.map (fullLeviProjection_surjective P hp .arms)) with h | h
  · let : Group.IsSolvable L := Group.isSolvable_of_isSolvable_injective
      (inclusion_injective h)
    exact (Group.IsPerfect.not_isSolvable L inferInstance).elim
  · exact commutator_eq_bot_iff_le_centralizer.mp (by rwa [commutator_comm] at h)

end Triality.Standard.Parabolics
