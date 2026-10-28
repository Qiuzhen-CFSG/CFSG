module

public import Stellmacher.SectionOne.OneSevenTransvectionSupportSelection
public import Stellmacher.SectionOne.OneSevenFactorOrbitTransitivity

/-!
# No Sylow-fixed rank-one displacement with two factors

In the rank-two (1.7) decomposition used on printed p.50 of Stellmacher's
`refs/files/stellmacher-n-group.pdf`, an order-two actor subgroup with a
rank-one action commutator cannot have that commutator fixed by the Sylow
subgroup. A nonidentity point selects a factor support. If Sylow-fixed,
the point belongs to every Sylow-conjugate support. Sylow transitivity and
disjointness of distinct supports force all factors to coincide, contrary
to the factor count of two.
-/

namespace Stellmacher.SectionOne

universe u

public theorem oneSeven_rank_one_not_sylow_fixed
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [Nontrivial V] [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (hyp : Hypotheses K V) (sylow : Sylow 2 K)
    (hgen : oneE (V := V) (sylow : Subgroup K) ⊔ (sylow : Subgroup K) = ⊤)
    (hunique : IsUniqueMaximalContaining (sylow : Subgroup K) ⊤)
    (hcount : (oneSevenFactors (G := K) (V := V)).card = 2)
    (actors : Subgroup K) (hle : actors ≤ (sylow : Subgroup K))
    (hcard : Nat.card actors = 2) (hrank : Nat.card (commutatorAction actors V) = 2) :
    ¬ commutatorAction actors V ≤ FixedPoints.subgroup (sylow : Subgroup K) V := by
  classical
  intro hfixed
  obtain ⟨factor, ⟨hfactor, hsupport⟩, _⟩ :=
    oneSeven_order_two_rank_one_support hyp sylow actors hle hcard hrank
  obtain ⟨point, hpne, _⟩ :=
    (Nat.card_eq_two_iff' (1 : commutatorAction actors V)).mp hrank
  have hpointne : (point : V) ≠ 1 := fun heq => hpne (Subtype.ext heq)
  have hpoint : (point : V) ∈ commutatorAction factor V := hsupport point.property
  have hevery : ∀ other ∈ oneSevenFactors (G := K) (V := V), other = factor := by
    intro other hother
    obtain ⟨actor, hconj⟩ := oneSeven_factor_orbit_transitive hyp sylow hgen hunique
      factor ((mem_oneSevenFactors_iff factor).mpr hfactor) other hother
    have hfix : (actor : K) • (point : V) = point := by
      have hmem := hfixed point.property
      rw [FixedPoints.mem_subgroup] at hmem
      exact hmem actor
    have hotherpoint : (point : V) ∈ commutatorAction other V := by
      rw [← hconj, ← RankOneThreeGroupAssembly.commutatorAction_conjBy factor actor]
      exact ⟨point, hpoint, hfix⟩
    by_contra hne
    exact hpointne ((oneSevenFactor_support_disjoint_of_ne hyp other factor
      ((mem_oneSevenFactors_iff other).mp hother) hfactor hne).le_bot
        ⟨hotherpoint, hpoint⟩)
  have hbound : (oneSevenFactors (G := K) (V := V)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro first hfirst second hsecond
    exact (hevery first hfirst).trans (hevery second hsecond).symm
  omega

end Stellmacher.SectionOne
