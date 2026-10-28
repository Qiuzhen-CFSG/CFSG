module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.MovedPrime.Cover.PrimeAutomizer.Models
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.MovedPrime.Cover.PrimeAutomizer.FiveSeed
public import Theory.SpecificGroups.PSL2.PrimeInvolutionCentralizerMaximal
public import Theory.SpecificGroups.PSL2.InvolutionCentralizerSolvable
public import Theory.GroupTheory.CentralizerEquivBounds
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# Inner prime-field automizer covers

Choose a central involution of the prescribed full Sylow subgroup. For
p > 9 its centralizer is a maximal solvable subgroup. A second maximal
Sylow overgroup is either solvable itself or an actual A₅; in the latter
case its Sylow normalizer is a solvable seed escaping that centralizer.
The resulting pair generates. If there is no second maximal overgroup,
the ambient group is a genuine minimal parabolic. For p = 7 all proper
subgroups are solvable by Dickson's classification.

Source application: Aschbacher--Smith E.1.12 and 10.3.3, pp.214 and 756.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Cover.PrimeAutomizer
variable {G : Type*} [Group G] [Finite G]

private theorem central_involution (R : Sylow 2 G) (hR : (R : Subgroup G) ≠ ⊥) :
    ∃ t : G, t ∈ R ∧ orderOf t = 2 ∧
      (R : Subgroup G) ≤ centralizer ({t} : Set G) := by
  let : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot _).mpr hR
  let : Nontrivial (center R) := R.isPGroup'.center_nontrivial
  have hd : 2 ∣ Nat.card (center R) :=
    (R.isPGroup'.to_subgroup (center R)).card_eq_or_dvd.resolve_left
      (ne_of_gt (Finite.one_lt_card : 1 < Nat.card (center R)))
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center R) 2 hd
  refine ⟨z.val.val, z.val.property, ?_, ?_⟩
  · simpa only [Subgroup.orderOf_coe] using hz
  · intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (congrArg (fun y : R => (y : G)) (mem_center_iff.mp z.property ⟨x, hx⟩))

omit [Finite G] in
private theorem cover_of_maximal_escape (R : Subgroup G) (D B : Subgroup G)
    (hD : IsCoatom D) (hsD : Group.IsSolvable D) (hsB : Group.IsSolvable B)
    (hnD : R ≤ normalizer (D : Set G)) (hnB : R ≤ normalizer (B : Set G))
    (hescape : ¬ B ≤ D) : HasSolvableNormalizedCover ⊤ R := by
  have hgen : D ⊔ B = ⊤ := by
    by_contra h
    exact hescape ((hD.le_iff_eq h).mp le_sup_left ▸ le_sup_right)
  exact cover_of_pair ⊤ R D B le_top le_top hsD hsB hnD hnB hgen

/-- Large inner prime-field groups admit either unique Sylow maximality or solvable invariant seeds. -/
theorem inner_large_prime_dichotomy
    (R : Sylow 2 G) (hn : ¬ (R : Subgroup G).Normal)
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hp : 9 < p) (hF : Nat.card F = p) (e : G ≃* PSL(2,F)) :
    ChapterB.IsMinimalParabolicOver R ⊤ ∨
      HasSolvableNormalizedCover ⊤ (R : Subgroup G) := by
  classical
  have hR : (R : Subgroup G) ≠ ⊥ := by
    intro h
    exact hn (h ▸ inferInstanceAs ((⊥ : Subgroup G).Normal))
  obtain ⟨t, htR, ht, hRC⟩ := central_involution R hR
  let D := centralizer ({t} : Set G)
  have ht' : GorensteinWalter.IsInvolution (e t) :=
    (orderOf_eq_prime_iff.mp ((e.orderOf_eq t).trans ht)).symm
  have hD : IsCoatom D := (isCoatom_centralizer_equiv_iff e t).mp
    (Theory.PSL2.prime_involution_centralizer_isCoatom_of_nine_lt ho hF hp (e t) ht')
  have hsD : Group.IsSolvable D := by
    let := Theory.PSL2.involution_centralizer_isSolvable
      (show GorensteinWalter.IsOddPrimePower (Nat.card F) from
        ⟨p, 1, Fact.out, ho, by decide, by simpa using hF⟩) (e t) ht'
    let c := CentralizerSmallKernelTransport.centralizerEquiv e t
    exact Group.isSolvable_of_isSolvable_injective (f := c.toMonoidHom) c.injective
  have hnD : (R : Subgroup G) ≤ normalizer (D : Set G) := hRC.trans D.le_normalizer
  by_cases hu : ∀ M : Subgroup G, IsCoatom M ∧ (R : Subgroup G) ≤ M → M = D
  · exact Or.inl ((ChapterB.isMinimalParabolicOver_top_iff R).mpr
      ⟨⟨D, ⟨hD, hRC⟩, hu⟩, hn⟩)
  · push Not at hu
    obtain ⟨M, ⟨hM, hRM⟩, hne⟩ := hu
    have hnot : ¬ M ≤ D := fun h => hne ((hM.le_iff_eq hD.1).mp h).symm
    have hnM : (R : Subgroup G) ≤ normalizer (M : Set G) := hRM.trans M.le_normalizer
    by_cases hsM : Group.IsSolvable M
    · exact Or.inr (cover_of_maximal_escape R D M hD hsD hsM hnD hnM hnot)
    · obtain ⟨_, ⟨a⟩⟩ := nonsolvable_proper_prime_model ho hF e M hM.1 hsM
      let P := R.subtype hRM
      have hP : (P : Subgroup M).map M.subtype = (R : Subgroup G) ⊓ M := by
        rw [Sylow.coe_subtype, subgroupOf_map_subtype, inf_comm]
      obtain ⟨B, _, hsB, hnB, hescape⟩ := five_sylow_normalizer_seed M R hnM P hP a t ht (hRM htR)
      exact Or.inr (cover_of_maximal_escape R D B hD hsD hsB hnD hnB hescape)

/-- The exceptional small prime has no nonsolvable proper subgroup. -/
theorem inner_seven_dichotomy
    (R : Sylow 2 G) (hn : ¬ (R : Subgroup G).Normal)
    {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 7) (e : G ≃* PSL(2,F)) :
    ChapterB.IsMinimalParabolicOver R ⊤ ∨
      HasSolvableNormalizedCover ⊤ (R : Subgroup G) := by
  have hp : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply dichotomy_of_solvable_intersections ⊤ R (by simp) hn
  intro M hM _
  have hsM : Group.IsSolvable M := by
    by_contra hns
    have hd := (nonsolvable_proper_prime_model (by decide : Odd 7) hF e M hM.1 hns).1
    norm_num at hd
  let := hsM
  exact Group.isSolvable_of_isSolvable_injective
    (f := inclusion (show M ⊓ ⊤ ≤ M from inf_le_left)) (inclusion_injective _)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Cover.PrimeAutomizer
