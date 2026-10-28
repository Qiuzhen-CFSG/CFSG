module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorOddPrime
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.MovedPrime
public import Theory.SpecificGroups.SL2.SmallOddComparisons

/-!
# Prime-five reduction in the original tensor point centralizer

For every odd prime at least seven, the original component joined with T
has E-generation one. The completed plane-fixed centralizer bound and the
zeroth weak-closure normalizer then force that join into M, contradicting
component escape. The order-three model is excluded by its failure of
perfection. Thus the original component quotient is PSL₂(5).

The Source application retains the original factorization, cubic Sylow,
commutator and exchanged component marking. The remaining assertions of
8.3.10, tensor recognition, strict r bound, point-core containment and both
quiet exclusions stay with the selected-module owner.
Source: Aschbacher--Smith 8.3.10(1), printed pp.725--726, using E.1.14(6)
and E.3.19. No bound on C_M(V) or later ambient equality is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE Chapter8.Section03 Chapter1 Chapter1.XiEmbedding
open BinaryTensorThree.PlaneFixed
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- The original odd-prime component/Sylow join has generation one for
primes at least seven, with its full two-core and original quotient marking. -/
theorem quiet_tensor_odd_prime_join_generation
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    {K : Subgroup G} (hK : K ∈ cComponentsIn (centralizer ({z} : Set G)))
    (hq : IsQuasisimple (XiQuotient K))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hp7 : 7 ≤ p)
    (hm : ClassicalGroup.IsPSL (XiQuotient K) 2 p) :
    IsEGenerated 1 (K ⊔ (T : Subgroup G) : Subgroup G) := by
  let H := K ⊔ (T : Subgroup G)
  have hHGz : H ≤ centralizer ({z} : Set G) := sup_le hK.1 hzT
  have hz2 : orderOf z = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian z hzV) hz1
  have hH : IsSQTK KnownSimple.IsKnownSimple H :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hHGz)).mp
      ((D.simpleQTKE.twoLocal_sqtk (isTwoLocal_involution_centralizer hz2)).subgroup _)
  let A := K.subgroupOf H
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  have hA : A.IsCComponent := hK.2.subgroupOf_of_le le_sup_left hHGz
  let a := subgroupOfEquivOfLe (show K ≤ H from le_sup_left)
  let b := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let : IsQuasisimple (XiQuotient K) := hq
  have hqA : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv b.symm
  have hAS : A ⊔ (S : Subgroup H) = ⊤ := by
    change K.subgroupOf H ⊔ (T : Subgroup G).subgroupOf H = ⊤
    rw [←subgroupOf_sup (show K ≤ H from le_sup_left)
      (show (T : Subgroup G) ≤ H from le_sup_right)]
    exact subgroupOf_self H
  exact SourceLinearThreeReplacement.Overgroups.ModelGeneration.oddPrimeOrbitGeneration_of_moved
    SourceLinearThreeReplacement.Overgroups.ModelGeneration.movedOddPrimeGeneration
    H hH S A hA hqA hAS p hp ho hp7 (hm.of_mulEquiv b)

/-- Source 8.3.10's prime-five reduction follows from the completed ambient
centralizer bound and generation on the original KT. No prime-divisor bound
on C_M(V), nor the later equality M=L₀T, is used. -/
theorem quiet_tensor_point_prime_eq_five
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩))
    {K : Subgroup G} (hK : K ∈ cComponentsIn (centralizer ({z} : Set G)))
    (hKM : ¬ K ≤ D.maximalLocal) (hq : IsQuasisimple (XiQuotient K))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient K) 2 p) : p = 5 := by
  by_contra hp5
  have hp3 : p ≠ 3 := by
    intro he
    let : IsQuasisimple (XiQuotient K) := hq
    obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
    exact Matrix.ProjectiveSpecialLinearGroup.not_perfect_of_card_three (he ▸ hF)
      (Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective)
  have hp7 : 7 ≤ p := by
    have hh := Nat.odd_iff.mp ho
    have hh' := hp.two_le
    omega
  let H := K ⊔ (T : Subgroup G)
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  have hgen := quiet_tensor_odd_prime_join_generation D hzV hz1 hzT hK hq hp ho hp7 hm
  obtain ⟨q,b,hqsurj,hker,hT,hb,hR,hzU,hTU,hthree⟩ :=
    quiet_tensor_plane_fixed_geometry D hn e hbase hzV hz1 hzT
  have hC := quiet_tensor_point_three_free_le D hmany hmin hn hJ cL e hbase
    hzV hz1 hzT P (centralizer (originalFixed D.fullModule (localJoin T L) q : Set G))
    (centralizer_le (Set.singleton_subset_iff.mpr hzU))
    (hTU.trans (normalizer_le_normalizer_centralizer _)) hthree
  have hs := (quiet_tensor_source_parameters D hn e hbase).2.2
  have hU := quiet_tensor_plane_fixed_le_weakCentralizer D hs q hqsurj b hT hb
  have hC1 := (centralizer_le hU).trans hC
  have hmap : (S : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hHM : H ≤ D.maximalLocal := by
    apply WeakCentralizerContainment.le_of_isEGenerated_one (V := D.fullModule) S (hgen S)
    · rw [hmap]
      exact quiet_tensor_weakClosure_zero_normalizer D hs q b hT hb
    · rw [hmap]
      exact inf_le_right.trans hC1
    · rw [hs]
      decide
  exact hKM (le_sup_left.trans hHM)

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
