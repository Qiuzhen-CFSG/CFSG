module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.Symmetry
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.Projections
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.FixedQuotient
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.AdditiveBound
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.Flags
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.MinimumDegree
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.FixedCodimension
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.FewFactors
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.EqualityCounts

/-!
# The chief-factor contradiction in B.5.9

Choose the component of larger field degree m by exchanging the actual
components and their natural seeds. The invariant chief flag has c>2
noncentral factors, each costing at least m in A-fixed codimension. Hence
m(A)>2m and B=C_A(L) is nontrivial. The nontrivial L-action on V/C_V(B)
gives dimension at least 3m; the original seed contributes another m.
This proves the lower chain (!!).

The actual product-rank upper bound (*) forces equality throughout:
m(A)=m(V/C_V(A))=4m, m(V/C_V(B))=3m, and m(U/C_U(A))=m.
The proved projection equality then gives B=A_C and A≤LB. In a chief flag
through C_V(B), dimension and perfectness give exactly one noncentral
factor above that term. The local two-core calculation and the irreducible
commutator U=[C_V(B),L] give exactly one below it. Thus c=2, contradicting
c>2. This uses the central quotient C_V(B)/U and retains the original seed.

`secondComponent_false` proves the requested conditional exclusion from
`Setup`, the original component and commutator equality, its natural seed,
and the given `SecondComponent`. No further source implication is added.
Construction of the second component and the final U=W assembly remain
with the surrounding natural-closure argument.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9,
printed p.108, final paragraph.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
open QuasisimpleSource
set_option backward.isDefEq.respectTransparency false
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Inequality (!) and the exclusion of at most two factors force a
nontrivial kernel B of the actual first-component projection. -/
theorem SecondComponent.rank_gt_component_bound
    {K : GroupClass} {A L : Subgroup G} (setup : Setup ρ K A)
    (hL : IsComponent G L) (hLA : ⁅L,A⁆ = L)
    (s : NaturalSeed ρ A L) (d : SecondComponent ρ A L)
    (f : InvariantChiefFlag ρ A L ⊤) :
    2 * s.field.degree < rank A := by
  let : Module.Finite (ZMod 2) V := setup.hypothesis.finite_module
  have hc := FewFactors.two_lt_noncentral_card ρ hL d f
  have hcm := f.count_mul_le_rank ρ setup hL hLA s d
  have hthree := Nat.mul_le_mul_right s.field.degree
    (show 3 ≤ f.noncentral.card by omega)
  have hm := s.field.degree_pos
  omega

/-- The literal lower chain (!!), with its quotient and seed estimates
proved from the original second-component configuration. -/
theorem SecondComponent.sharp_additive_lower_bound
    {K : GroupClass} {A L : Subgroup G} (setup : Setup ρ K A)
    (hL : IsComponent G L) (hLA : ⁅L,A⁆ = L)
    (s : NaturalSeed ρ A L) (d : SecondComponent ρ A L)
    (f : InvariantChiefFlag ρ A L ⊤) :
    4 * s.field.degree ≤ fixedCodim ρ (A ⊓ centralizer (L : Set G)) +
        fixedCodim s.space.toRepresentation (A.subgroupOf (L ⊔ A)) ∧
      fixedCodim ρ (A ⊓ centralizer (L : Set G)) +
        fixedCodim s.space.toRepresentation (A.subgroupOf (L ⊔ A)) ≤ fixedCodim ρ A ∧
      fixedCodim ρ A ≤ rank A := by
  let : Module.Finite (ZMod 2) V := setup.hypothesis.finite_module
  have hgt := d.rank_gt_component_bound ρ setup hL hLA s f
  have hB := d.centralizer_fixedCodim_lower ρ setup s hL hgt
  have hU := seed_fixedCodim_lower ρ setup hL hLA s d
  exact ⟨by omega, seed_additive_bound ρ s setup.minimal.1.1.2,
    (setup.minimal.1.isOffender ρ).2⟩

/-- Comparing (*) and (!!) forces equality in every dimension bound,
including the literal quotient dimension 3m and seed codimension m. -/
theorem SecondComponent.sharp_equalities_of_degree_le
    {K : GroupClass} {A L : Subgroup G} (setup : Setup ρ K A)
    (hL : IsComponent G L) (hLA : ⁅L,A⁆ = L)
    (s : NaturalSeed ρ A L) (d : SecondComponent ρ A L)
    (horder : d.seed.field.degree ≤ s.field.degree)
    (f : InvariantChiefFlag ρ A L ⊤) :
    rank A = 4 * s.field.degree ∧ fixedCodim ρ A = 4 * s.field.degree ∧
      fixedCodim ρ (A ⊓ centralizer (L : Set G)) = 3 * s.field.degree ∧
      fixedCodim s.space.toRepresentation (A.subgroupOf (L ⊔ A)) = s.field.degree := by
  let : Module.Finite (ZMod 2) V := setup.hypothesis.finite_module
  have hgt := d.rank_gt_component_bound ρ setup hL hLA s f
  have hB := d.centralizer_fixedCodim_lower ρ setup s hL hgt
  have hU := seed_fixedCodim_lower ρ setup hL hLA s d
  obtain ⟨hlower, hadd, hoff⟩ := d.sharp_additive_lower_bound ρ setup hL hLA s f
  have hu := d.rank_bound ρ s hL setup.minimal.1.1
  omega

/-- For the larger field degree the sharp rank equality gives B=A_C,
while the adapted flag has c-1 noncentral factors below C_V(B). The
original seed and the actual local two-core give exactly one there,
contradicting the proved c>2. -/
theorem SecondComponent.false_of_degree_le
    {K : GroupClass} {A L : Subgroup G} (setup : Setup ρ K A)
    (hL : IsComponent G L) (hLA : ⁅L,A⁆ = L)
    (s : NaturalSeed ρ A L) (d : SecondComponent ρ A L)
    (horder : d.seed.field.degree ≤ s.field.degree) : False := by
  let : Module.Finite (ZMod 2) V := setup.hypothesis.finite_module
  obtain ⟨f, r, hr, hstop⟩ :=
    exists_invariantChiefFlag_through_offenderCentralizerFixed ρ setup hL s d
  obtain ⟨hA, _, hB, _⟩ := d.sharp_equalities_of_degree_le ρ setup hL hLA s horder f
  obtain ⟨_, _, hsplit, _⟩ := d.split_of_rank_lower ρ s hL setup.minimal.1.1 horder hA.ge
  have hnon := d.centralizerQuotient_nontrivial_of_rank_gt ρ setup s hL
    (d.rank_gt_component_bound ρ setup hL hLA s f)
  obtain ⟨_, hcount, _⟩ := f.centralizerFixed_counts_of_sharp_bound s hL hr hstop hB hnon
  have hone := noncentralFactors_of_split ρ s hL setup.minimal hsplit
    f.term f.monotone r f.start hstop
  have hthree := FewFactors.two_lt_noncentral_card ρ hL d f
  omega

/-- The chief-factor contradiction in the final paragraph of B.5.9.
The symmetry theorem exchanges the actual components and their natural
seeds if necessary, so no ordering of their field degrees is assumed.
The cross action already implies properness of each seed. -/
theorem secondComponent_false
    {K : GroupClass} {A L : Subgroup G} (setup : Setup ρ K A)
    (hL : IsComponent G L) (hLA : ⁅L,A⁆ = L)
    (s : NaturalSeed ρ A L) (d : SecondComponent ρ A L) : False := by
  let : Module.Finite (ZMod 2) V := setup.hypothesis.finite_module
  obtain ⟨J, t, e, hJ, hJA, _, horder⟩ := exists_ordered_components ρ s hL hLA d
  exact e.false_of_degree_le ρ setup hJ hJA t horder

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
