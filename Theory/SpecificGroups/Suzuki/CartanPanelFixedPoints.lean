module
public import Theory.GroupAction.CartanPanelFixedPoints
public import Theory.SpecificGroups.Suzuki.SplitNormalizerGeometry
public import BenderSuzuki.MatrixGroups.SuzukiZero
public import Mathlib.GroupTheory.IsPerfect

/-!
# Suzuki Cartan elements with exactly two fixed cosets

For a positive Suzuki parameter, the split torus has nonidentity elements,
each fixing exactly infinity and zero on the ovoid. A supplied supplement
contains an element outside the root group. The existing root-commutator
bijection conjugates this element into the split torus. Transport through
the actual orbit map and Sylow conjugacy gives the left-coset statement for
any supplied odd complement. The solvable group Sz(2) is excluded using
perfectness, so the zero parameter remains accounted for.

Source: Huppert--Blackburn III, XI.3.3, XI.3.6 and XI.3.10; the normalizer
and natural-action conventions are those of `RootOvoidGeometry`.
-/

public section
open scoped Pointwise
namespace BenderSuzuki.MatrixGroups
open Theory.CartanPanel

/-- Any supplement to the root group in the standard Borel contains a sharp
fixed-pair element. In particular the supplied odd complement need not be chosen
in standard coordinates. -/
theorem suzuki_supplement_two_fixed (m : ℕ) (hm : 0 < m)
    (D : Subgroup (SuzukiMatrixGroup m))
    (hD : D ≤ SuzukiBorelSubgroup m)
    (hsup : SuzukiRootSubgroup m ⊔ D = SuzukiBorelSubgroup m) :
    ∃ d ∈ D, ∃ β : SuzukiOvoid m, β ≠ suzukiOvoidInfinity m ∧
      ∀ ω : SuzukiOvoid m, d • ω = ω ↔ ω = suzukiOvoidInfinity m ∨ ω = β := by
  have hcard : 1 < Nat.card (SuzukiSplitTorus m) := by
    rw [suzukiSplitTorus_card m hm]
    have hq : 2 ^ 3 ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  let : Nontrivial (SuzukiSplitTorus m) := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨u, hu⟩ := exists_ne (1 : SuzukiSplitTorus m)
  have huR : (u : SuzukiMatrixGroup m) ∉ SuzukiRootSubgroup m := by
    intro hur
    exact hu (Subtype.ext (Subgroup.mem_bot.mp
      ((suzukiRootSubgroup_disjoint_splitTorus m hm).le_bot ⟨hur, u.property⟩)))
  have hex : ∃ d ∈ D, d ∉ SuzukiRootSubgroup m := by
    by_contra! h
    apply huR
    have hle : SuzukiBorelSubgroup m ≤ SuzukiRootSubgroup m := by
      rw [← hsup]
      exact sup_le le_rfl h
    apply hle
    rw [suzukiBorelSubgroup_eq_sup]
    exact (show SuzukiSplitTorus m ≤ SuzukiRootSubgroup m ⊔ SuzukiSplitTorus m from
      le_sup_right) u.property
  obtain ⟨d, hd, hdR⟩ := hex
  obtain ⟨r, hr⟩ := suzukiBorelSubgroup_conjugate_into_split m hm d (hD hd) hdR
  let t : SuzukiMatrixGroup m := (r : SuzukiMatrixGroup m)⁻¹ * d * r
  have ht : t ≠ 1 := by
    intro he
    have he' := congrArg (fun x : SuzukiMatrixGroup m => (r : SuzukiMatrixGroup m) * x *
      (r : SuzukiMatrixGroup m)⁻¹) he
    have hd1 : d = 1 := by simpa [t, mul_assoc] using he'
    exact hdR (hd1 ▸ (SuzukiRootSubgroup m).one_mem)
  have hrfix := suzukiRootSubgroup_fix_infinity m hm (r : SuzukiMatrixGroup m) r.property
  refine ⟨d, hd, (r : SuzukiMatrixGroup m) • suzukiOvoidZero m, ?_, ?_⟩
  · intro he
    exact (suzukiOvoidInfinity_ne_zero m).symm
      ((MulAction.injective (r : SuzukiMatrixGroup m)) (he.trans hrfix.symm))
  · intro ω
    have hh := suzukiSplitTorus_fixed_pair m hm t hr ht
      ((r : SuzukiMatrixGroup m)⁻¹ • ω)
    change _ ↔ _ = suzukiOvoidInfinity m ∨ _ = suzukiOvoidZero m at hh
    simpa only [t, mul_smul, smul_inv_smul, (MulAction.injective
      (r : SuzukiMatrixGroup m)⁻¹).eq_iff, inv_smul_eq_iff, hrfix] using hh

/-- The complete arbitrary-Sylow, supplied-complement assertion for positive Suzuki parameters. -/
theorem suzuki_sylow_two_fixed_cosets (m : ℕ) (hm : 0 < m)
    (T : Sylow 2 (SuzukiMatrixGroup m)) : SylowHasTwoFixedCosets T := by
  obtain ⟨P, hP⟩ := suzukiRootSubgroup_isSylow m hm
  apply all_sylows P _ T
  intro D hD _hodd _hdis hsup
  have hN : Subgroup.normalizer (P : Set (SuzukiMatrixGroup m)) =
      SuzukiBorelSubgroup m := by
    change Subgroup.normalizer ((P : Subgroup (SuzukiMatrixGroup m)) : Set (SuzukiMatrixGroup m)) = _
    rw [hP, suzukiRootSubgroup_normalizer m hm]
  apply two_fixed_cosets _ D (suzukiOvoidInfinity m)
    (hN.trans (suzukiBorelSubgroup_eq_stabilizer m hm))
    (fun x => MulAction.exists_smul_eq (SuzukiMatrixGroup m) _ x)
  apply suzuki_supplement_two_fixed m hm D (hN ▸ hD)
  simpa only [hP, hN] using hsup

/-- Perfectness excludes Sz(2); no source constructor is discarded. -/
theorem suzuki_parameter_pos_of_perfect (m : ℕ) [Group.IsPerfect (SuzukiMatrixGroup m)] :
    0 < m := by
  by_contra hm
  have hm0 : m = 0 := by omega
  subst m
  have : Nontrivial (SuzukiMatrixGroup 0) := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [suzukiZero_card]
    decide
  exact Group.IsPerfect.not_isSolvable (SuzukiMatrixGroup 0) suzukiZero_isSolvable

/-- Perfect Suzuki models have the requested two-fixed-coset element in every supplied complement. -/
theorem suzuki_perfect_sylow_two_fixed_cosets (m : ℕ)
    [Group.IsPerfect (SuzukiMatrixGroup m)] (T : Sylow 2 (SuzukiMatrixGroup m)) :
    SylowHasTwoFixedCosets T :=
  suzuki_sylow_two_fixed_cosets m (suzuki_parameter_pos_of_perfect m) T
end BenderSuzuki.MatrixGroups
