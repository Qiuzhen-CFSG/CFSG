module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticTrack
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticModuleMarking
public import CFSG.Quasithin.ChapterF.Section07.CriticalPairs.Completion

/-!
# The original cubic--quintic graph before its order bound

Restrict X=YT and H to their generated subgroup, with false=X and true=H.
The original F.1.1 intersection and local quotient give degrees three and
five, and the common stabilizer maps to the prescribed Sylow T. The
elementary H-span of the plane lies in O₂(H), so its actual critical track
exceeds one. No endpoint identification or parabolic order is assumed.

Source: Aschbacher--Smith 14.2.20--21, pp.988--989; F.7.6--11,
pp.312--313. These are inputs to the remaining quintic path-action argument.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterF.Section07
variable {G : Type*} [Group G] [Finite G]

/-- The literal graph has the asserted local indices, and its common
subgroup maps to the original Sylow, not just an isomorphic copy. -/
theorem source_quintic_graph_indices
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
    let F := Geometry.family X H
    ((F true).subgroupOf (F false)).index = 3 ∧
      ((F false).subgroupOf (F true)).index = 5 ∧
      (F false ⊓ F true).map (X ⊔ H).subtype = (T : Subgroup G) := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let F := Geometry.family X H
  have hm := source_index_five_models hG T hempty hM hu hmany hcard e H hH.1 hi
  have hsmall : SmallSolvableModel (H ⧸ pCore 2 H) := hm.elim Or.inl (Or.inr ∘ Or.inl)
  have hHX := (source_hypothesis_F_1_1 hG T hempty hM hu hmany hcard e H hH hsmall).2.1
  have hXH : X ⊓ H = (T : Subgroup G) := (inf_comm X H).trans hHX
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  obtain ⟨_, ⟨eX⟩⟩ := source_residualSylow_quotient hG T hempty hM hu hmany hcard e
  have hthree : (T : Subgroup G).relIndex X = 3 :=
    SymmetricThreeTwoCore.sylow_index_three eX (T.subtype hTX)
  have hmap : (F false ⊓ F true).map (X ⊔ H).subtype = (T : Subgroup G) := by
    rw [map_inf _ _ _ (X ⊔ H).subtype_injective]
    change (X.subgroupOf (X ⊔ H)).map (X ⊔ H).subtype ⊓
      (H.subgroupOf (X ⊔ H)).map (X ⊔ H).subtype = _
    rw [map_subgroupOf_eq_of_le le_sup_left, map_subgroupOf_eq_of_le le_sup_right, hXH]
  refine ⟨?_, ?_, hmap⟩
  · change (H.subgroupOf (X ⊔ H)).relIndex (X.subgroupOf (X ⊔ H)) = 3
    rw [relIndex_subgroupOf (show X ≤ X ⊔ H from le_sup_left),
      ← inf_relIndex_left X H, hXH]
    exact hthree
  · change (X.subgroupOf (X ⊔ H)).relIndex (H.subgroupOf (X ⊔ H)) = 5
    rw [relIndex_subgroupOf (show H ≤ X ⊔ H from le_sup_right),
      ← inf_relIndex_right X H, hXH]
    exact hi

/-- The original elementary closure places the plane in the true vertex
core. Consequently the constructed source track has length greater than one. -/
theorem source_quintic_track_gt_one
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
    let L := X ⊔ H
    let F : Bool → Subgroup L := fun i => if i then H.subgroupOf L else X.subgroupOf L
    ∃ (D : Track.SourceSetup F) (hne : D.V ≠ ⊥),
      D.seed.map L.subtype = localModule T M ∧
      (D.sylow false : Subgroup (F false)).map
        (L.subtype.comp (F false).subtype) = (T : Subgroup G) ∧
      D.seed ≤ (F true).pCoreIn 2 ∧ 1 < D.track hne := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let L := X ⊔ H
  let F : Bool → Subgroup L := fun i => if i then H.subgroupOf L else X.subgroupOf L
  obtain ⟨D, hne, hseed, hsylow⟩ :=
    source_residual_vertex_track hG T hempty hM hu hmany hcard e H hH
  let U := conjugateSpanBy (localModule T M) H
  have he := (source_index_five_closure_structure hG T hempty hM hu hmany hcard e H hH.1 hi).1
  let : IsElementaryAbelian 2 U := he
  have hred := Chapter15.Section03.InitialSource.localModule_reduced_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1, hM.1.2⟩
  have hVT : localModule T M ≤ (T : Subgroup G) := by
    have h := (map_mono hred.le_pCore).trans (pCoreIn_le_sylow M (T.subtype hM.1.2))
    simpa only [map_subgroupOf_eq_of_le (localModule_le T hM.1.2),
      Sylow.coe_subtype, map_subgroupOf_eq_of_le hM.1.2] using h
  have hVH : localModule T M ≤ H := hVT.trans hH.1.1.2
  have hU : U ≤ H.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup (p := 2) (G := U))
    (conjugateSpanBy_le_self hVH) (le_normalizer_conjugateSpanBy _ _)
  have hcore : D.seed ≤ (F true).pCoreIn 2 := by
    apply (map_le_map_iff_of_injective L.subtype_injective).mp
    rw [hseed, ← AmalgamLocalCores.pCoreIn_map_of_injective 2 _ L.subtype_injective]
    change localModule T M ≤ ((H.subgroupOf L).map L.subtype).pCoreIn 2
    rw [map_subgroupOf_eq_of_le (show H ≤ L from le_sup_right)]
    exact (le_conjugateSpanBy _ _).trans hU
  exact ⟨D, hne, hseed, hsylow, hcore,
    CriticalPairs.Completion.one_lt_track_of_true_core F D hne hcore⟩

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
