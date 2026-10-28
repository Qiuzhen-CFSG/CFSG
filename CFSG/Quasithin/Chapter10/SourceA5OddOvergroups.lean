module
public import CFSG.Quasithin.Chapter10.SourceA5MinimalParabolic
public import Theory.GroupTheory.CComponent.A5PairOddOvergroups

/-!
# Odd subgroups in proper A₅ local-join overgroups

The original nonnormal A₅ component and prescribed Sylow subgroup generate
the local join. Its component normalizer has index two. The exchanged-pair
prime-support theorem therefore makes every proper Sylow overgroup a
{2,3}-group. Every odd-order subgroup of such an overgroup is a three-group.
The full two-core is retained throughout.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
10.2.3, printed pp.744–745. This supplies the order bound used after placing the
Hall actor in a proper Sylow overgroup; faithfulness and that placement are
separate source conclusions.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G]

variable {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
include D e

private theorem source_a5_internal :
    (L.subgroupOf (localJoin T L)).IsCComponent ∧
    Nonempty (((L.subgroupOf (localJoin T L)) ⧸ pCore 2 (L.subgroupOf (localJoin T L)))
      ≃* alternatingGroup (Fin 5)) ∧
    L.subgroupOf (localJoin T L) ⊔
      ((T.subtype (show (T : Subgroup G) ≤ localJoin T L from le_sup_right) :
        Sylow 2 (localJoin T L)) : Subgroup (localJoin T L)) = ⊤ := by
  let H := localJoin T L
  have hLH : L ≤ H := (le_componentOrbit L T).trans le_sup_left
  have hA : (L.subgroupOf H).IsCComponent := by
    change (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G))).IsCComponent
    rw [componentOrbit_sup]
    exact D.maximal.1.1
  let a := subgroupOfEquivOfLe hLH
  let b := a.toMonoidHom.pCoreQuotientEquiv (p := 2) a.surjective
    (by rw [a.toMonoidHom.ker_eq_bot a.injective]; exact IsPGroup.of_bot)
  refine ⟨hA, ⟨b.trans e⟩, ?_⟩
  change L.subgroupOf H ⊔ (T : Subgroup G).subgroupOf H = ⊤
  rw [← subgroupOf_sup hLH (show (T : Subgroup G) ≤ H from le_sup_right)]
  have hh : L ⊔ (T : Subgroup G) = H := (componentOrbit_sup L (T : Subgroup G)).symm
  rw [hh, subgroupOf_self]

omit e in
private theorem source_a5_nonnormal_index
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (normalizer (L.subgroupOf (localJoin T L) : Set (localJoin T L))).index = 2 := by
  have hi := source_nonnormal_normalizer_index D.simpleQTKE D.maximal.1 hn
  change (normalizer (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔
    (T : Subgroup G)) : Set (componentOrbit L (T : Subgroup G) ⊔
    (T : Subgroup G) : Subgroup G))).index = 2
  rw [componentOrbit_sup]
  exact hi

/-- Every proper overgroup of the original Sylow subgroup inside the
nonnormal A₅ local join has prime divisors among two and three. -/
theorem source_a5_proper_overgroup_six
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (P : Subgroup G) (hTP : (T : Subgroup G) ≤ P) (hP : P < localJoin T L) :
    IsPGroup 6 P := by
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let A := L.subgroupOf H
  obtain ⟨hA, ⟨eA⟩, hgen⟩ := source_a5_internal D e
  have hSP : (S : Subgroup H) ≤ P.subgroupOf H := by
    intro x hx
    exact hTP hx
  have hPne : P.subgroupOf H ≠ ⊤ := fun he => hP.not_ge (subgroupOf_eq_top.mp he)
  exact (hA.a5_pair_proper_overgroup_six S A eA
    (source_a5_nonnormal_index D hn) hgen (P.subgroupOf H) hSP hPne).of_equiv
    (subgroupOfEquivOfLe hP.le)

/-- The actual odd Hall actor is a three-group once it lies in a proper
overgroup of the prescribed Sylow subgroup. -/
theorem source_a5_odd_subgroup_isThreeGroup
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (P B : Subgroup G) (hTP : (T : Subgroup G) ≤ P) (hP : P < localJoin T L)
    (hBP : B ≤ P) (hBodd : Odd (Nat.card B)) : IsPGroup 3 B := by
  have h6 := (source_a5_proper_overgroup_six D e hn P hTP hP).to_le hBP
  obtain ⟨n, hn⟩ := h6.exists_card_dvd_pow
  have hn' : Nat.card B ∣ 2 ^ n * 3 ^ n := by
    simpa only [← mul_pow, show 2 * 3 = 6 by decide] using hn
  exact IsPGroup.of_card_dvd_pow ((hBodd.coprime_two_right.pow_right n).dvd_of_dvd_mul_left hn')

omit e in
/-- An original HStar member meets the local join properly, by uniqueness
of the maximal two-local subgroup above that join. -/
theorem source_hstar_inf_localJoin_lt
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    H ⊓ localJoin T L < localJoin T L := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  have hHN : H ≤ normalizer (H.pCoreIn 2 : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  apply lt_of_le_of_ne inf_le_right
  intro he
  have hjoinH : localJoin T L ≤ H := by rw [← he]; exact inf_le_left
  exact hH.1.2 (hHN.trans (normalizer_le_of_unique_maximalTwoLocal
    (D.lemma_3_2_3_uniqueness hu).2.2 (isPGroup_pCoreIn 2 H) hH.1.1.1
    (hjoinH.trans hHN)))

/-- The odd Hall actor in an actual HStar subgroup is a three-group as soon
as its original ambient image lies in the local join. Properness is supplied
by source uniqueness, so it is not an extra premise. -/
theorem source_a5_hstar_odd_subgroup_isThreeGroup
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (B : Subgroup G) (hBH : B ≤ H) (hBJ : B ≤ localJoin T L)
    (hBodd : Odd (Nat.card B)) : IsPGroup 3 B :=
  source_a5_odd_subgroup_isThreeGroup D e hn (H ⊓ localJoin T L) B
    (le_inf hH.1.1.2 le_sup_right) (source_hstar_inf_localJoin_lt D hH)
    (le_inf hBH hBJ) hBodd

end CFSG.Quasithin.Chapter10
