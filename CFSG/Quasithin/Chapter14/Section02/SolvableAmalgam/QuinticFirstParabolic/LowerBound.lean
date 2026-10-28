module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.CentralKernel
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.AlgebraicLowerBound
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.SmallCore
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.SmallCoreGeometry
public import Theory.GroupAction.RankTwoCosetGeometry.PathOrderLowerBound

/-!
# Counting the original quintic Sylow subgroup

The unconditional source bounds are |T|≥2048 and |H|≥10240. The Sz(2)
quotient branch follows from the faithful commutator action. If the bound
failed in the D₁₀ branch, the core would have order 512 and the original
closure U would have order 32. The imported conjugate-intersection argument
forces U to be normal in both parabolics, contradicting the trivial common
core. These bounds discharge the numerical premise of the separately
owned first-parabolic reconstruction from generating relations.

The original geometric route is retained: the quintic root has 5120
nonbacktracking eight-edge paths, and eight-path transitivity together
with its nontrivial radius-four ball kernel also gives the same bounds.
Eight-path transitivity remains a separate obligation of the consolidated
owner. The older disjunctive reductions are preserved as public interfaces.

Source: Aschbacher--Smith F.1.11--12, pp.262--264, and 14.2.20--21,
pp.988--989, with the path-action conventions of F.3.3--5, pp.270--272.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterF.Section07 Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] [Finite G]

/-- The original index-five hypotheses imply the required Sylow order bound. -/
theorem source_quintic_sylow_lower
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    : 2048 ≤ Nat.card (T : Subgroup G) :=
  source_quintic_sylow_lower_via_small_core hG T hempty hM hu hmany hcard e H hH hi

/-- The unconditional order bound for the literal first parabolic. -/
theorem source_quintic_first_lower
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    : 10240 ≤ Nat.card H := by
  have h := source_quintic_sylow_lower hG T hempty hM hu hmany hcard e H hH hi
  have hc := ((T : Subgroup G).subgroupOf H).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hH.1.1.2).toEquiv] at hc
  change (T : Subgroup G).relIndex H * Nat.card (T : Subgroup G) = Nat.card H at hc
  rw [hi] at hc
  omega

/-- Exact path count for the original source graph, before any endpoint or
path-action recognition. The true root is the quintic vertex H. -/
theorem source_quintic_eight_path_count
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    Nat.card {p : BasedWalk (Geometry.graph X H) 8 (Geometry.base X H true) //
      p.Nonbacktracking} = 5120 := by
  obtain ⟨hthree, hfive, _⟩ := source_quintic_graph_indices
    hG T hempty hM hu hmany hcard e H hH hi
  exact card_eight_paths_of_indices_three_five _ hthree hfive true

/-- The original Sylow bound follows from the geometric eight-path input.
There is no endpoint, generating-presentation or stabilizer-order premise. -/
theorem source_quintic_sylow_lower_of_eight_paths
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hpaths : let X := sourceResidual M Mc ⊔ (T : Subgroup G)
      RootPathTransitive (Geometry.graph X H) (X ⊔ H : Subgroup G)
        (Geometry.base X H true) 8) :
    2048 ≤ Nat.card (T : Subgroup G) := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let F := Geometry.family X H
  obtain ⟨hthree, hfive, hmap⟩ := source_quintic_graph_indices
    hG T hempty hM hu hmany hcard e H hH hi
  have hkernel := source_quintic_four_ball_kernel_ne_bot
    hG T hempty hM hu hmany hcard e H hH hi
  have h := common_card_ge_2048_of_quintic_paths F hthree hfive hpaths hkernel
  have hc := card_map_of_injective (K := F false ⊓ F true) (X ⊔ H).subtype_injective
  rw [hmap] at hc
  exact h.trans_eq hc.symm

/-- The same geometric input supplies the literal first-parabolic order
bound used to prove injectivity of the relation-defined map. -/
theorem source_quintic_first_lower_of_eight_paths
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hpaths : let X := sourceResidual M Mc ⊔ (T : Subgroup G)
      RootPathTransitive (Geometry.graph X H) (X ⊔ H : Subgroup G)
        (Geometry.base X H true) 8) :
    10240 ≤ Nat.card H := by
  have h := source_quintic_sylow_lower_of_eight_paths
    hG T hempty hM hu hmany hcard e H hH hi hpaths
  have hc := ((T : Subgroup G).subgroupOf H).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hH.1.1.2).toEquiv] at hc
  change (T : Subgroup G).relIndex H * Nat.card (T : Subgroup G) = Nat.card H at hc
  rw [hi] at hc
  omega

/-- An unconditional reduction of the numerical target to the remaining intrinsic
class-three dihedral configuration. The unconditional theorem above now excludes
the second alternative. -/
theorem source_quintic_sylow_lower_or_class_three_dihedral
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    2048 ≤ Nat.card (T : Subgroup G) ∨
      (Nonempty ((H ⧸ pCore 2 H) ≃* DihedralGroup 5) ∧
        Nat.card (T : Subgroup G) = 1024 ∧ Nat.card (pCore 2 H) = 512 ∧
        Nat.card (conjugateSpanBy (localModule T M) H) = 32 ∧
        H ⊓ centralizer (conjugateSpanBy (localModule T M) H : Set G) =
          conjugateSpanBy (localModule T M) H ∧
        (center (H.pCoreIn 2)).map (H.pCoreIn 2).subtype = centralInvolutions T ∧
        Group.nilpotencyClass (H.pCoreIn 2) = 3 ∧ Monoid.exponent (H.pCoreIn 2) = 4) := by
  by_cases hbound : 2048 ≤ Nat.card (T : Subgroup G)
  · exact Or.inl hbound
  · have hsmall := Nat.lt_of_not_ge hbound
    obtain ⟨hD,hT,hQ,hU⟩ := source_quintic_small_sylow_configuration
      hG T hempty hM hu hmany hcard e H hH hi hsmall
    exact Or.inr ⟨hD,hT,hQ,hU,
      source_quintic_small_centralizer hG T hempty hM hu hmany hcard e H hH hi hsmall,
      source_quintic_small_core_center hG T hempty hM hu hmany hcard e H hH hi hsmall,
      source_quintic_small_core_class_and_exponent
        hG T hempty hM hu hmany hcard e H hH hi hsmall⟩

/-- The remaining small dihedral alternative has the literal closure U as all
three characteristic layers of its core. This preserved reduction packages the order-five action
and third-commutator obstruction used by the completed small-core exclusion. -/
theorem source_quintic_sylow_lower_or_frattini_dihedral
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let Q := H.pCoreIn 2
    let U := conjugateSpanBy (localModule T M) H
    2048 ≤ Nat.card (T : Subgroup G) ∨
      (Nonempty ((H ⧸ pCore 2 H) ≃* DihedralGroup 5) ∧
        Nat.card (T : Subgroup G) = 1024 ∧ Nat.card (pCore 2 H) = 512 ∧
        Nat.card U = 32 ∧ H ⊓ centralizer (U : Set G) = U ∧
        (center Q).map Q.subtype = centralInvolutions T ∧
        Group.nilpotencyClass Q = 3 ∧ Monoid.exponent Q = 4 ∧
        ⁅Q,Q⁆ = U ∧ (frattini Q).map Q.subtype = U ∧
        (Subgroup.upperCentralSeries Q 2).map Q.subtype = U ∧
        Nat.card (Q ⧸ frattini Q) = 16 ∧
        ∀ a : MulAut Q, orderOf (quotientAut (frattini Q) a) ≠ 15) := by
  rcases source_quintic_sylow_lower_or_class_three_dihedral
      hG T hempty hM hu hmany hcard e H hH hi with hbound | hconf
  · exact Or.inl hbound
  · obtain ⟨hD,hT,hQ,hU,hC,hZ,hcl,hexp⟩ := hconf
    have hsmall : Nat.card (T : Subgroup G) < 2048 := by omega
    obtain ⟨hcomm,hPhi,hupper,hquot⟩ := source_quintic_small_core_characteristic_layers
      hG T hempty hM hu hmany hcard e H hH hi hsmall
    exact Or.inr ⟨hD,hT,hQ,hU,hC,hZ,hcl,hexp,hcomm,hPhi,hupper,hquot,
      source_quintic_small_core_no_fifteen hG T hempty hM hu hmany hcard e H hH hi hsmall⟩

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
