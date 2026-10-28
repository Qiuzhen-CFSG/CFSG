module
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.CoreActionRigidity.Structure
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.CoreActionRigidity.SquareDetection
public import Theory.GroupTheory.Commutator.PerfectSolvableSupplement
public import Theory.GroupTheory.PResidual.Defs

/-!
# Full linear Ree core-action rigidity

A subnormal subgroup of the full linear parabolic has either trivial or full
image in the actual simple SL₂ factor. In the full-image case it contains the
perfect seed: the commutator removes the complementary abelian torus, and the
solvable projection kernel lets subnormality absorb the seed. In the other
case, detecting the torus coordinate on radical commutator squares places the
subgroup in a two-group; two-perfection then makes it trivial.

`linear_rigidity` discharges both premises of the retained conditional reduction
`linear_rigidity_of_square_calculations` using the actual seed commutator with
nonidentity square and the complementary-torus calculation, including arbitrary
radical factors. Thus every subnormal two-perfect subgroup whose commutators
with the intrinsic two-core all square to one is trivial. The exported
structural calculations also prove both full-parabolic core centralizer bounds
and Suzuki-side three-freeness, without additional model assumptions.

Sources: Aschbacher–Smith F.1.12(I)(5) and (II), printed pp.263–264, the Ree
exclusion in 2.3.9(7), printed p.526, and its application to invariant parabolics
in E.6.8, printed pp.247–248 (`refs/quasithin.pdf`, 1 March 2004 manuscript).
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace ReeF4.ConverseParabolics.CoreActionRigidity

-- A perfect subgroup in B times a solvable normal subgroup is absorbed by subnormal B.
private theorem perfect_le_subnormal_of_le_sup_solvable {G : Type*} [Group G] [Finite G] (K B R : Subgroup G)
    [Group.IsPerfect K] [R.Normal] [Group.IsSolvable R]
    (hs : B.IsSubnormal) (hK : K ≤ B ⊔ R) : K ≤ B := by
  let M := B ⊔ R
  have hKM : K ≤ M := hK
  let : Group.IsPerfect (K.subgroupOf M) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hKM).symm.toMonoidHom)
      (subgroupOfEquivOfLe hKM).symm.surjective
  let eR := subgroupOfEquivOfLe (show R ≤ M from le_sup_right)
  let : Group.IsSolvable (R.subgroupOf M) :=
    Group.isSolvable_of_isSolvable_injective (f := eR.toMonoidHom) eR.injective
  have hle : K.subgroupOf M ≤ B.subgroupOf M :=
    (le_solvableResidual_of_isPerfect _).trans
      (hs.subgroupOf.solvableResidual_le_of_sup_eq_top (R.subgroupOf M)
        (codisjoint_subgroupOf_sup B R).eq_top)
  intro k hk
  exact hle (show (⟨k, hKM hk⟩ : M) ∈ K.subgroupOf M from hk)

-- A subgroup mapping onto a perfect group also maps onto that group through its commutator.
private theorem product_lift_of_perfect_image {G S T : Type*} [Group G] [Group S] [CommGroup T]
    [Group.IsPerfect S] (f : G →* S × T) (B : Subgroup G)
    (hB : B.map ((MonoidHom.fst S T).comp f) = ⊤) (s : S) :
    (s, 1) ∈ B.map f := by
  let g : B →* S := ((MonoidHom.fst S T).comp f).comp B.subtype
  have hg : g.range = ⊤ := by
    rw [MonoidHom.range_comp, B.range_subtype]
    exact hB
  have hc : (_root_.commutator B).map g = ⊤ := by
    rw [map_commutator_eq, hg]
    exact Group.IsPerfect.commutator_eq_top
  obtain ⟨b, hb, hbs⟩ := mem_map.mp (hc.symm ▸ mem_top s)
  have ht : (f b.val).2 = 1 :=
    Abelianization.commutator_subset_ker (((MonoidHom.snd S T).comp f).comp B.subtype) hb
  refine mem_map.mpr ⟨b.val, b.property, ?_⟩
  exact Prod.ext hbs ht

private theorem eq_bot_of_isPPerfect_of_le_twoGroup {G : Type*} [Group G] (B R : Subgroup G)
    (hB : IsPPerfect 2 B) (hR : IsPGroup 2 R) (hle : B ≤ R) : B = ⊥ := by
  have hp := hR.to_le hle
  have hz : (⊥ : Subgroup B) = ⊤ := hB _ inferInstance
    (hp.of_surjective (QuotientGroup.mk' ⊥) (QuotientGroup.mk'_surjective _))
  apply eq_bot_iff.mpr
  intro b hb
  exact congrArg Subtype.val (mem_bot.mp (show (⟨b, hb⟩ : B) ∈ (⊥ : Subgroup B) from
    hz.symm ▸ mem_top _))

private theorem perfect_le_sup_kernel {G S T : Type*} [Group G] [Group S] [CommGroup T]
    (f : G →* S × T) (K B : Subgroup G)
    [Group.IsPerfect K]
    (hlift : ∀ s : S, (s, 1) ∈ B.map f) : K ≤ B ⊔ f.ker := by
  have hK : ∀ k : K, (f k.val).2 = 1 := by
    intro k
    apply Abelianization.commutator_subset_ker
      (((MonoidHom.snd S T).comp f).comp K.subtype)
    rw [Group.IsPerfect.commutator_eq_top]
    trivial
  intro k hk
  have him : f k ∈ B.map f := by
    have he : f k = ((f k).1, 1) := Prod.ext rfl (hK ⟨k, hk⟩)
    rw [he]
    exact hlift _
  exact (show (B.map f).comap f ≤ B ⊔ f.ker by rw [comap_map_eq]) him

/-- The genuine SL₂ coordinate of the full parabolic projection. -/
def simpleProjection {m : ℕ} (hm : 1 ≤ m) :
    parabolic m .linear →* Matrix.SpecialLinearGroup (Fin 2) (CoefficientField m) :=
  (MonoidHom.fst _ _).comp (linearProjection hm)

theorem simpleProjection_surjective {m : ℕ} (hm : 1 ≤ m) :
    Function.Surjective (simpleProjection hm) := by
  intro g
  obtain ⟨x, hx⟩ := linearProjection_surjective hm (g, 1)
  exact ⟨x, congrArg Prod.fst hx⟩

private theorem linearSL_simple {m : ℕ} (hm : 1 ≤ m) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (CoefficientField m)) := by
  let := LargeLocalSeeds.linearQuotient_simple m hm
  exact (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := CoefficientField m)).isSimpleGroup

private theorem linearSL_perfect {m : ℕ} (hm : 1 ≤ m) :
    Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (CoefficientField m)) := by
  let := LargeLocalSeeds.linearQuotient_perfect m hm
  exact Group.IsPerfect.ofSurjective
    (f := (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := CoefficientField m)).symm.toMonoidHom)
    (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := CoefficientField m)).symm.surjective

/-- A subnormal subgroup with full SL₂ image contains the actual perfect seed.
The solvable supplement is the two-group projection kernel, inside the full parabolic. -/
theorem linearSeed_le_of_simple_image_eq_top {m : ℕ} (hm : 1 ≤ m)
    (B : Subgroup (parabolic m .linear)) (hs : B.IsSubnormal)
    (hfull : B.map (simpleProjection hm) = ⊤) : linearSeed m ≤ B := by
  let := linearSeed_perfect hm
  let := linearSL_perfect hm
  let f := linearProjection hm
  let : Group.IsNilpotent f.ker := (linearProjection_ker_isPGroup hm).isNilpotent
  apply perfect_le_subnormal_of_le_sup_solvable (linearSeed m) B f.ker hs
  exact perfect_le_sup_kernel f (linearSeed m) B
    (product_lift_of_perfect_image f B hfull)

/-- A reduction to two concrete square calculations. The first detects the seed;
the second detects the complementary torus after the SL₂ coordinate vanishes.
No block predicate or ambient simplicity is assumed. -/
theorem linear_rigidity_of_square_calculations {m : ℕ} (hm : 1 ≤ m)
    (hseed : ∃ q ∈ intrinsicRadical m .linear, ∃ b ∈ linearSeed m,
      (⁅q, b⁆ : parabolic m .linear) ^ 2 ≠ 1)
    (htorus : ∀ b : parabolic m .linear, (linearProjection hm b).1 = 1 →
      (∀ q ∈ intrinsicRadical m .linear, (⁅q, b⁆ : parabolic m .linear) ^ 2 = 1) →
      (linearProjection hm b).2 = 1)
    (B : Subgroup (parabolic m .linear)) (hs : B.IsSubnormal) (hp : IsPPerfect 2 B)
    (hsquare : ∀ q ∈ pCore 2 (parabolic m .linear), ∀ b ∈ B,
      (⁅q, b⁆ : parabolic m .linear) ^ 2 = 1) : B = ⊥ := by
  let := linearSL_simple hm
  have hRcore := intrinsicRadical_le_pCore (linear_parabolic_le_radical_normalizer m)
  rcases (hs.map (simpleProjection_surjective hm)).eq_bot_or_top_of_isSimpleGroup
      inferInstance with hz | ht
  · apply eq_bot_of_isPPerfect_of_le_twoGroup B (intrinsicRadical m .linear) hp
      (intrinsicRadical_isPGroup m .linear)
    intro b hb
    have hb1 : (linearProjection hm b).1 = 1 := by
      exact mem_bot.mp (hz ▸ mem_map_of_mem (simpleProjection hm) hb)
    have hb2 := htorus b hb1 (fun q hq => hsquare q (hRcore hq) b hb)
    rw [← linearProjection_ker hm]
    exact Prod.ext hb1 hb2
  · have hK := linearSeed_le_of_simple_image_eq_top hm B hs ht
    obtain ⟨q, hq, b, hb, hneq⟩ := hseed
    exact (hneq (hsquare q (hRcore hq) b (hK hb))).elim

/-- A subnormal two-perfect subgroup of the full linear parabolic is trivial
if all its commutators with the intrinsic two-core square to one.
Both the seed and complementary-torus square calculations are discharged;
no ambient simplicity or quasisimplicity assumption is needed. -/
theorem linear_rigidity {m : ℕ} (hm : 1 ≤ m)
    (B : Subgroup (parabolic m .linear)) (hs : B.IsSubnormal) (hp : IsPPerfect 2 B)
    (hsquare : ∀ q ∈ pCore 2 (parabolic m .linear), ∀ b ∈ B,
      (⁅q, b⁆ : parabolic m .linear) ^ 2 = 1) : B = ⊥ :=
  linear_rigidity_of_square_calculations hm
    (linear_exists_seed_commutator_square_ne_one hm)
    (linear_torus_eq_one_of_commutator_squares hm) B hs hp hsquare

end ReeF4.ConverseParabolics.CoreActionRigidity
