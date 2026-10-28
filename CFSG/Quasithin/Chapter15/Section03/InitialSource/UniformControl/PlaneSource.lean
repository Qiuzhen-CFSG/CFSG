module
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl.SeedSource
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.AlternatingThree.Complete
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.Single.FixedSource
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan

/-!
# The original natural-plane branch of 14.1.11

Use the same universal characteristic pair in the original M. Failure of
its characteristic-normalizer factorization makes the intrinsic pair control
proper, since the first seed's centralizer is C_M(V)T. The actual natural-plane
quotient has abelian Sylow image. Fixed-pair C.1.28 therefore constructs a
moving A₃ block in this same M, contradicted by the proved 14.1.10 source.

All pair restriction, local subgroup selection, quotient solvability, action
coordinates and preceding A/C/13.9.1 implications are discharged. The hypothesis
|V(M)|=4 is the original rank-two branch of 14.1.7; the independent orthogonal
branch remains separate. Source: Aschbacher--Smith 14.1.11, printed p.978.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl
open ChapterB ChapterC.GlaubermanNiles
open ChapterC.RankOne.ChiProduct.FixedPairSolvable
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem restricted_omegaClosure (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) :
    normalClosure (omegaOneCenterAmbient (T.subtype hTM : Subgroup M) : Set M) =
      (localModule T M).subgroupOf M := by
  have hz : omegaOneCenterAmbient (T.subtype hTM : Subgroup M) =
      (omegaOneCenterAmbient (T : Subgroup G)).subgroupOf M := by
    apply map_injective M.subtype_injective
    rw [←omegaOneCenterAmbient_map_injective M.subtype M.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM]
    exact (map_subgroupOf_eq_of_le (show omegaOneCenterAmbient (T : Subgroup G) ≤ M from
      fun _ hx => hTM ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1)).symm
  rw [hz,normalClosure_subgroupOf_eq_conjugateSpanBy _ M
    (show omegaOneCenterAmbient (T : Subgroup G) ≤ M from
      fun _ hx => hTM ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1)]
  rfl

private theorem plane_sylow_image_abelian {H : Type*} [Group H] [Finite H]
    (S : Sylow 2 H) (C : Subgroup H) [C.Normal]
    (e : (H ⧸ C) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :
    IsMulCommutative ((S : Subgroup H).map (QuotientGroup.mk' C)) := by
  let P := (S : Subgroup H).map (QuotientGroup.mk' C)
  have hc : Nat.card (H ⧸ C) = 6 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card]
    decide
  have hd : Nat.card P ∣ 2*3 := by simpa only [hc] using P.card_subgroup_dvd_card
  have hp : Nat.Coprime (Nat.card P) 3 := by
    obtain ⟨n,hn⟩ := (S.isPGroup'.map (QuotientGroup.mk' C)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  exact (isCyclic_of_card_dvd_prime (p := 2) (hp.dvd_mul_right.mp hd)).isMulCommutative

/-- The full characteristic-normalizer factorization in the original natural-plane branch. -/
theorem source_plane_factorization
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcase : M ≠ Mc ∨ Nat.card (centralInvolutions T) = 2)
    (hcard : Nat.card (localModule T M) = 4)
    (D : CharacteristicPair (baumann (T : Subgroup G))) (hD : D.Universal.{u,u}) :
    M = (M ⊓ centralizer (localModule T M : Set G)) ⊔
      (M ⊓ normalizer (D.second.map (baumann (T : Subgroup G)).subtype : Set G)) := by
  let : D.second.Characteristic := D.second_characteristic
  by_cases hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)
  · exact source_centralizing_factorization hG T hM hJ D.second
  let hH : M ∈ Chapter1.HOver G (T : Set G) := ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1,hM.2⟩
  let U := (localModule T M).subgroupOf M
  let := (localModule_reduced_from_source hG T hH).normal
  let := (localModule_reduced_from_source hG T hH).elementary
  have he : Nonempty ((M ⧸ centralizer (U : Set M)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) := by
    rcases local_natural_action_from_source
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
      hG T hempty hM hu hcase hJ with h | h
    · obtain ⟨_,e,_⟩ := h
      exact ⟨e⟩
    · obtain ⟨d⟩ := h
      have hc := d.card_vector
      omega
  obtain ⟨e⟩ := he
  by_contra hfail
  let S := T.subtype hM.2
  let DM := subtypePair T D M hM.2
  have hproper : control S DM ≠ ⊤ := by
    intro ht
    apply hfail
    apply le_antisymm
    · have hm := subtypePair_control_map_le_relative T D M hM.2
      rw [show control (T.subtype hM.2) (subtypePair T D M hM.2) = ⊤ from ht,
        ←MonoidHom.range_eq_map,range_subtype] at hm
      exact hm.trans (sup_le
        (source_noncentral_seed_le_characteristic_supplement hG T hempty hM hu hcase hJ D)
        le_sup_right)
    · exact sup_le inf_le_left inf_le_left
  let ec := QuotientGroup.quotientMulEquivOfEq
    (congrArg (fun W : Subgroup M => centralizer (W : Set M))
      (restricted_omegaClosure T M hM.2))
  have hs : Group.IsSolvable (M ⧸ centralizer
      (normalClosure (omegaOneCenterAmbient (S : Subgroup M) : Set M) : Set M)) := by
    let : Group.IsSolvable (M ⧸ centralizer (U : Set M)) := reduced_action_isSolvable
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
      hG T hempty hH U (localModule_reduced_from_source hG T hH)
    exact Group.isSolvable_of_isSolvable_injective (f := ec.toMonoidHom) ec.injective
  have ha : IsMulCommutative ((S : Subgroup M).map (QuotientGroup.mk' (centralizer
      (normalClosure (omegaOneCenterAmbient (S : Subgroup M) : Set M) : Set M)))) := by
    exact plane_sylow_image_abelian S _ (ec.trans e)
  obtain ⟨X,hb,hx,hm,_,_⟩ := Single.exists_moving_alternatingThree_of_fixed_pair_escape S
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mpr (hG.evenCharacteristic T M hM.1 hM.2))
    DM (subtypePair_universal T D hD M hM.2) hproper
    ((hG.twoLocal_sqtk hM.1.1).stronglyQuasithin 3 Nat.prime_three (by decide)) hs ha
  exact alternating_three_excluded_from_source hG T hM hu hmany X (S : Subgroup M) hb
    (pCore_isPGroup.le_sylow_of_normal S) le_rfl hm hcase hx

end CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl
