module

public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.RootSubgroups
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.LinearQuotient
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.Commutator.PerfectQuotient

/-!
# From linear Ree root calculations to the intrinsic two-core

Let K be the fixed local factor defined by the end nodes of F₄, and R its
specified root-generated radical. A surjection K → PSL₂(q) with kernel R,
the two-group property of R, the generation R ≤ [R,K], and an actual
noncommuting pair in R suffice for all the intrinsic local conclusions.

The quotient is simple by `linearQuotient_simple` and perfect by the usual
SL₂ transvection calculation. Thus its two-core is trivial, which identifies
R with O₂(K). Perfectness lifts because R lies in the derived subgroup. If
C_K(R) were not contained in R, simplicity of the quotient would give
K = C_K(R) R; then R ≤ [R,K] = [R,R] would make a nontrivial finite two-group
perfect. Finally the noncommuting pair makes [R,R], and hence [[R,K],R],
nontrivial.

These are conditional assembly lemmas. They do not construct the projection,
prove the radical is a two-group, or supply the root commutators. Their extra
premises must be discharged before asserting the concrete local result.

Source: Aschbacher–Smith, F.1.12(I)(5) and (II), printed pp.263–264, and the
local block exclusion in 2.3.9(7), printed p.526. The field-generator proof
of PSL₂ perfectness follows Mathlib's `PSL/PSL2.lean`.
-/

public section

open Subgroup
open scoped commutatorElement
namespace ReeF4.LargeLocalSeeds

/-- The actual PSL₂ quotient target is perfect for every large Ree field. -/
theorem linearQuotient_perfect (m : ℕ) (hm : 1 ≤ m) : Group.IsPerfect (LinearQuotient m) := by
  have hcard : 4 ≤ Nat.card (CoefficientField m) := by
    rw [field_card]
    exact pow_le_pow_right₀ (by decide : 1 ≤ 2) (by omega : 2 ≤ 2 * m + 1)
  obtain ⟨x, hx⟩ : IsCyclic (CoefficientField m)ˣ := inferInstance
  apply Group.IsPerfect.mk
  apply SL2Simple.PSL_commutator_eq_top
  refine ⟨x, Units.ne_zero x, fun h ↦ ?_⟩
  grw [Nat.card_eq_card_units_add_one (CoefficientField m),
    ← orderOf_eq_card_of_forall_mem_zpowers hx,
    orderOf_le_of_pow_eq_one zero_lt_two (Units.ext <| by simpa using h)] at hcard
  omega

/-- Simplicity and perfectness rule out a nontrivial normal two-subgroup. -/
theorem linearQuotient_twoCore (m : ℕ) (hm : 1 ≤ m) :
    pCore 2 (LinearQuotient m) = ⊥ := by
  let := linearQuotient_simple m hm
  let := linearQuotient_perfect m hm
  rcases (inferInstance : (pCore 2 (LinearQuotient m)).Normal).eq_bot_or_eq_top
    with h | h
  · exact h
  · have hp : IsPGroup 2 (⊤ : Subgroup (LinearQuotient m)) :=
      h ▸ (pCore_isPGroup (p := 2) (G := LinearQuotient m))
    exact False.elim (Group.IsPerfect.not_isNilpotent (LinearQuotient m)
      (hp.of_equiv Subgroup.topEquiv).isNilpotent)

private theorem centralizer_le_kernel_of_full_commutator
    {G H : Type*} [Group G] [Finite G] [Group H] [IsSimpleGroup H]
    (f : G →* H) (hf : Function.Surjective f)
    (hP : IsPGroup 2 f.ker) (hne : f.ker ≠ ⊥)
    (hfull : f.ker ≤ ⁅f.ker, (⊤ : Subgroup G)⁆) :
    centralizer (f.ker : Set G) ≤ f.ker := by
  let C : Subgroup G := centralizer (f.ker : Set G)
  have hn : (C.map f).Normal := Subgroup.Normal.map inferInstance f hf
  rcases hn.eq_bot_or_eq_top with h | h
  · exact (Subgroup.map_eq_bot_iff C).mp h
  · have hgen : C ⊔ f.ker = ⊤ := by
      simpa only [Subgroup.comap_map_eq, Subgroup.comap_top] using
        congrArg (Subgroup.comap f) h
    have hderived : ⁅f.ker, f.ker⁆ = f.ker := by
      apply le_antisymm (Subgroup.commutator_le_self _)
      apply hfull.trans
      apply Subgroup.commutator_le.mpr
      intro q hq g _
      obtain ⟨c, hc, r, hr, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp
        (hgen ▸ (Subgroup.mem_top g))
      have hqr : ⁅q, r⁆ ∈ ⁅f.ker, f.ker⁆ :=
        Subgroup.commutator_mem_commutator hq hr
      have hqrR : ⁅q, r⁆ ∈ f.ker := Subgroup.commutator_le_self _ hqr
      have hqc : Commute q c := Subgroup.mem_centralizer_iff.mp hc q hq
      have hcqr : c * ⁅q, r⁆ * c⁻¹ = ⁅q, r⁆ :=
        mul_inv_eq_iff_eq_mul.mpr
          (Subgroup.mem_centralizer_iff.mp hc _ hqrR).symm
      rw [commutatorElement_mul_right_eq_mul_conj, hqc.commutator_eq, one_mul, hcqr]
      exact hqr
    let : Nontrivial f.ker := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    let : Group.IsPerfect f.ker := Subgroup.isPerfect_iff.mpr hderived
    exact False.elim (Group.IsPerfect.not_isNilpotent f.ker hP.isNilpotent)

/-- A concrete surjection with the specified two-group kernel identifies the
root-defined radical with the intrinsic two-core. -/
theorem seedRadical_linear_eq_twoCore_of_projection {m : ℕ} (hm : 1 ≤ m)
    (d : LocalBlockInput m)
    (f : standardSeed d .linear →* LinearQuotient m)
    (hf : Function.Surjective f)
    (hker : f.ker = seedRadical d .linear)
    (hP : IsPGroup 2 (seedRadical d .linear)) :
    seedRadical d .linear = pCore 2 (standardSeed d .linear) := by
  have hpker : IsPGroup 2 f.ker := hker ▸ hP
  have h := f.comap_pCore_of_ker_isPGroup hf hpker
  rw [linearQuotient_twoCore m hm] at h
  change f.ker = _ at h
  exact hker.symm.trans h

/-- The first isomorphism theorem produces the required quotient equivalence
once a concrete projection and its two-group kernel have been calculated. -/
noncomputable def linearCoreQuotientEquivOfProjection {m : ℕ} (hm : 1 ≤ m)
    (d : LocalBlockInput m)
    (f : standardSeed d .linear →* LinearQuotient m)
    (hf : Function.Surjective f)
    (hker : f.ker = seedRadical d .linear)
    (hP : IsPGroup 2 (seedRadical d .linear)) :
    (standardSeed d .linear ⧸ pCore 2 (standardSeed d .linear)) ≃*
      LinearQuotient m :=
  (QuotientGroup.quotientMulEquivOfEq
    ((seedRadical_linear_eq_twoCore_of_projection hm d f hf hker hP).symm.trans
      hker.symm)).trans (QuotientGroup.quotientKerEquivOfSurjective f hf)

/-- The first-isomorphism equivalence acts on representatives by the given
projection. This equation is the public computation interface. -/
@[simp] theorem linearCoreQuotientEquivOfProjection_mk {m : ℕ} (hm : 1 ≤ m)
    (d : LocalBlockInput m)
    (f : standardSeed d .linear →* LinearQuotient m)
    (hf : Function.Surjective f)
    (hker : f.ker = seedRadical d .linear)
    (hP : IsPGroup 2 (seedRadical d .linear)) (x : standardSeed d .linear) :
    linearCoreQuotientEquivOfProjection hm d f hf hker hP
      (QuotientGroup.mk' (pCore 2 (standardSeed d .linear)) x) = f x := by
  rfl

/-- A perfect quotient and radical commutator generation make the local factor
perfect; no central-cover or splitting assumption is needed. -/
theorem linearSeed_perfect_of_projection_and_full_commutator
    {m : ℕ} (hm : 1 ≤ m) (d : LocalBlockInput m)
    (f : standardSeed d .linear →* LinearQuotient m)
    (hf : Function.Surjective f)
    (hker : f.ker = seedRadical d .linear)
    (hfull : seedRadical d .linear ≤
      ⁅seedRadical d .linear, (⊤ : Subgroup (standardSeed d .linear))⁆) :
    Group.IsPerfect (standardSeed d .linear) := by
  let := linearQuotient_perfect m hm
  have hk : f.ker ≤ commutator (standardSeed d .linear) := by
    rw [hker]
    exact hfull.trans (Subgroup.commutator_mono le_top le_rfl)
  have h := CentralExtension.ker_sup_commutator_eq_top_of_surjective f hf
  rw [sup_eq_right.mpr hk] at h
  exact ⟨h⟩

/-- Conditional assembly of all six linear-side conclusions from a concrete
projection, radical commutator generation, and a noncommuting radical pair.
The hypotheses are outstanding root calculations, not source conclusions. -/
theorem linearCore_conclusions_of_root_calculations
    {m : ℕ} (hm : 1 ≤ m) (d : LocalBlockInput m)
    (f : standardSeed d .linear →* LinearQuotient m)
    (hf : Function.Surjective f)
    (hker : f.ker = seedRadical d .linear)
    (hP : IsPGroup 2 (seedRadical d .linear))
    (hfull : seedRadical d .linear ≤
      ⁅seedRadical d .linear, (⊤ : Subgroup (standardSeed d .linear))⁆)
    (x y : standardSeed d .linear) (hx : x ∈ seedRadical d .linear)
    (hy : y ∈ seedRadical d .linear) (hxy : x * y ≠ y * x) :
    seedRadical d .linear = pCore 2 (standardSeed d .linear) ∧
      pCore 2 (standardSeed d .linear) ≠ ⊥ ∧
      centralizer (pCore 2 (standardSeed d .linear) : Set (standardSeed d .linear)) ≤
        pCore 2 (standardSeed d .linear) ∧
      Group.IsPerfect (standardSeed d .linear) ∧
      Nonempty ((standardSeed d .linear ⧸ pCore 2 (standardSeed d .linear)) ≃*
        LinearQuotient m) ∧
      ⁅⁅pCore 2 (standardSeed d .linear), (⊤ : Subgroup (standardSeed d .linear))⁆,
        pCore 2 (standardSeed d .linear)⁆ ≠ ⊥ := by
  have hR : seedRadical d .linear ≠ ⊥ := by
    intro h
    have hx1 : x = 1 := Subgroup.mem_bot.mp (h ▸ hx)
    exact hxy (by rw [hx1, one_mul, mul_one])
  have hRR : ⁅seedRadical d .linear, seedRadical d .linear⁆ ≠ ⊥ := by
    intro h
    have hmem := Subgroup.commutator_mem_commutator hx hy
    rw [h, Subgroup.mem_bot] at hmem
    exact hxy (commutatorElement_eq_one_iff_mul_comm.mp hmem)
  have hcore := seedRadical_linear_eq_twoCore_of_projection hm d f hf hker hP
  have hcentral : centralizer (seedRadical d .linear : Set (standardSeed d .linear)) ≤
      seedRadical d .linear := by
    let := linearQuotient_simple m hm
    have hpker : IsPGroup 2 f.ker := hker ▸ hP
    have hnker : f.ker ≠ ⊥ := hker ▸ hR
    have hfullker : f.ker ≤ ⁅f.ker, (⊤ : Subgroup (standardSeed d .linear))⁆ :=
      hker ▸ hfull
    simpa only [hker] using
      centralizer_le_kernel_of_full_commutator f hf hpker hnker hfullker
  refine ⟨hcore, hcore ▸ hR, hcore ▸ hcentral,
    linearSeed_perfect_of_projection_and_full_commutator hm d f hf hker hfull,
    ⟨linearCoreQuotientEquivOfProjection hm d f hf hker hP⟩, ?_⟩
  rw [← hcore]
  intro h
  apply hRR
  exact bot_unique (h ▸ Subgroup.commutator_mono hfull (le_refl (seedRadical d .linear)))

end ReeF4.LargeLocalSeeds

end
