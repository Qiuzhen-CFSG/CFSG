module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.AlgebraicLowerBound
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.EightPathAction.CoreMovement
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.EightPathAction.DihedralExclusion
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.EightPathAction.EvenActors
public import Theory.GroupAction.RankTwoCosetGeometry.QuinticThreePathEscape
/-!
# The first odd extension in the original quintic graph

Put X=YT and K=O₂(H)∩O₂(X). The cubic core has index two in T and
the quintic core moves the original plane, so K has index two in O₂(H).
If H normalized K, then K would centralize the entire H-span U of the plane.
The faithful-action bound |O₂(H)|≥16|C_H(U)| excludes this. Since T has
prime index five in H and normalizes K, N_H(K)=T.

The literal coset maps identify K with the intersection of the two base
ball kernels. Distinct adjacent conjugates of this intersection are not
contained in one another. Their transport along any three-edge path gives
a pointwise fixer outside the cubic endpoint kernel. This result retains
both the D₁₀ and Sz(2) quotient alternatives. `EightPathAction` applies it
to the Sz(2) three-path action to prove four-path transitivity.

Only the length-three odd extension is proved here. The length-five and
length-seven extensions, the remaining even actors, and D₁₀ exclusion
remain with the consolidated owner qt-e-quintic-sylow-lower.
Source: Aschbacher--Smith14.2.6,14.2.20--21, pp.982,988--989;
F.3.2--4 and F.7.3, pp.270 and311--312.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
/-- The crossing core intersection has exactly the prescribed Sylow as its
normalizer inside H, in both original quotient branches. -/
theorem source_quintic_core_intersection_normalizer
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
    let K := H.pCoreIn 2 ⊓ X.pCoreIn 2
    H ⊓ normalizer (K : Set G) = (T : Subgroup G) := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let Q := H.pCoreIn 2
  let B := X.pCoreIn 2
  let K := Q ⊓ B
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  let SX := T.subtype hTX
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using
      pCoreIn_le_sylow H (T.subtype hTH)
  have hBT : B ≤ (T : Subgroup G) := by
    simpa only [SX, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTX] using
      pCoreIn_le_sylow X SX
  obtain ⟨hB, ⟨eX⟩⟩ := source_residualSylow_quotient hG T hempty hM hu hmany hcard e
  have hBC : B ≤ centralizer (localModule T M : Set G) := by
    change X.pCoreIn 2 ≤ _
    rw [hB]
    exact inf_le_right
  have hBi : B.relIndex (T : Subgroup G) = 2 := by
    change (X.pCoreIn 2).relIndex (T : Subgroup G) = 2
    have hm := relIndex_mul_index (pCore_isPGroup.le_sylow_of_normal SX)
    rw [SymmetricThreeTwoCore.sylow_index_three eX SX,
      SymmetricThreeTwoCore.core_index eX] at hm
    have hi' : (pCore 2 X).relIndex (SX : Subgroup X) = 2 := by omega
    have hmap : (SX : Subgroup X).map X.subtype = (T : Subgroup G) :=
      map_subgroupOf_eq_of_le hTX
    rw [←hmap, pCoreIn, relIndex_map_map_of_injective _ _ X.subtype_injective]
    exact hi'
  have hmove : ¬ Q ≤ centralizer (localModule T M : Set G) := by
    rcases source_index_five_models hG T hempty hM hu hmany hcard e H hH.1 hi with hd | hs
    · exact (source_dihedral_core_configuration hG T hempty hM hu hmany hcard e H hH hi hd.some).2.2.2.2
    · exact source_suzuki_core_moves_plane hG T hempty hM hu hmany hcard e H hH hi hs.some
  have hKi : K.relIndex Q = 2 := by
    change (Q ⊓ B).relIndex Q = 2
    rw [inf_relIndex_left]
    have hu : B.relIndex Q ≤ 2 := by
      simpa only [hBi] using relIndex_le_of_le_right (H := B) hQT (by rw [hBi]; decide)
    have hp : B.relIndex Q ≠ 0 := index_ne_zero_of_finite
    have hn : B.relIndex Q ≠ 1 := by
      intro he
      apply hmove
      have hh := relIndex_eq_one.mp he
      exact hh.trans hBC
    omega
  have hnQ : H ≤ normalizer (Q : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hnB : X ≤ normalizer (B : Set G) := X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hnK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (le_inf (hTH.trans hnQ) (hTX.trans hnB)).trans inf_normalizer_le_normalizer_inf
  have hnot : ¬ H ≤ normalizer (K : Set G) := by
    intro hn
    have hKC : K ≤ centralizer (conjugateSpanBy (localModule T M) H : Set G) :=
      le_centralizer_conjugateSpanBy_of_normalizes K (localModule T M) H hn
        (inf_le_right.trans hBC)
    have hl := source_quintic_action_core_lower hG T hempty hM hu hmany hcard e H hH hi
    have hc : Nat.card K ≤ Nat.card (H ⊓ centralizer (conjugateSpanBy (localModule T M) H : Set G) : Subgroup G) :=
      card_le_of_le (le_inf (inf_le_left.trans (pCoreIn_le 2 H)) hKC)
    have hQcard : Nat.card Q = Nat.card (pCore 2 H) := card_map_of_injective H.subtype_injective
    have hm := (K.subgroupOf Q).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe (show K ≤ Q from inf_le_left)).toEquiv] at hm
    change K.relIndex Q * Nat.card K = Nat.card Q at hm
    rw [hKi, hQcard] at hm
    have hp : 0 < Nat.card K := Nat.card_pos
    omega
  have hTN : (T : Subgroup G) ≤ H ⊓ normalizer (K : Set G) := le_inf hTH hnK
  apply le_antisymm ?_ hTN
  have hm := relIndex_mul_relIndex (T : Subgroup G)
    (H ⊓ normalizer (K : Set G)) H hTN inf_le_left
  rw [hi] at hm
  rcases Nat.prime_mul_iff.mp (hm ▸ (by decide : Nat.Prime 5)) with hp | hp
  · exact (hnot ((relIndex_eq_one.mp hp.2).trans inf_le_right)).elim
  · exact relIndex_eq_one.mp hp.2
open ChapterF.Section07 Subgroup.CosetGeometry.RankTwo

/-- The intrinsic normalizer equality in the literal coset graph. -/
theorem source_quintic_kernel_intersection_normalizer
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
    F true ⊓ normalizer
      ((ballKernel F (base F false) 1 ⊓ ballKernel F (base F true) 1 : Subgroup (X ⊔ H : Subgroup G)) : Set (X ⊔ H : Subgroup G)) =
      F false ⊓ F true := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let L := X ⊔ H
  let F := Geometry.family X H
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hTL : (T : Subgroup G) ≤ L := hTX.trans le_sup_left
  let SL := T.subtype hTL
  have hSL (i : Bool) : (SL : Subgroup L) ≤ F i := by
    cases i
    · exact fun x hx => hTX hx
    · exact fun x hx => hTH hx
  let S (i : Bool) := SL.subtype (hSL i)
  obtain ⟨hthree, hfive, hmap⟩ := source_quintic_graph_indices
    hG T hempty hM hu hmany hcard e H hH hi
  have hSi (i : Bool) : ((S i : Subgroup (F i))).map (F i).subtype = F false ⊓ F true := by
    apply map_injective L.subtype_injective
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le (hSL i)]
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTL, hmap]
  have hk (i : Bool) : ballKernel F (base F i) 1 = (F i).pCoreIn 2 :=
    base_kernel_eq_core F i (S i) (hSi i)
  have hXmap : (ballKernel F (base F false) 1).map L.subtype = X.pCoreIn 2 := by
    rw [hk, ←AmalgamLocalCores.pCoreIn_map_of_injective 2 _ L.subtype_injective]
    change ((X.subgroupOf L).map L.subtype).pCoreIn 2 = _
    rw [map_subgroupOf_eq_of_le (show X ≤ L from le_sup_left)]
  have hHmap : (ballKernel F (base F true) 1).map L.subtype = H.pCoreIn 2 := by
    rw [hk, ←AmalgamLocalCores.pCoreIn_map_of_injective 2 _ L.subtype_injective]
    change ((H.subgroupOf L).map L.subtype).pCoreIn 2 = _
    rw [map_subgroupOf_eq_of_le (show H ≤ L from le_sup_right)]
  let K := ballKernel F (base F false) 1 ⊓ ballKernel F (base F true) 1
  let A := X.pCoreIn 2 ⊓ H.pCoreIn 2
  have hAL : A ≤ L := inf_le_right.trans ((pCoreIn_le 2 H).trans le_sup_right)
  have hK : K = A.subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [map_inf _ _ _ L.subtype_injective, hXmap, hHmap, map_subgroupOf_eq_of_le hAL]
  have hN : H ⊓ normalizer (A : Set G) = (T : Subgroup G) := by
    simpa only [A, inf_comm (X.pCoreIn 2) (H.pCoreIn 2)] using
      source_quintic_core_intersection_normalizer hG T hempty hM hu hmany hcard e H hH hi
  change F true ⊓ normalizer (K : Set L) = F false ⊓ F true
  rw [hK, ←subgroupOf_normalizer_eq hAL]
  apply map_injective L.subtype_injective
  change ((H ⊓ normalizer (A : Set G)).subgroupOf L).map L.subtype = _
  rw [map_subgroupOf_eq_of_le
    (show H ⊓ normalizer (A : Set G) ≤ L from inf_le_left.trans le_sup_right), hN, hmap]

/-- Every three-edge nonbacktracking path from H has a pointwise fixer
outside the radius-one kernel at its cubic endpoint. Both quotient rows remain. -/
theorem source_quintic_three_path_kernel_escape
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
    ∀ p : SimpleGraph.BasedWalk (graph F) 3 (base F true), p.Nonbacktracking →
      ¬ pathStabilizer F p ≤ ballKernel F p.endpoint 1 := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let F := Geometry.family X H
  have hn := source_quintic_kernel_intersection_normalizer
    hG T hempty hM hu hmany hcard e H hH hi
  change ∀ p : SimpleGraph.BasedWalk (graph F) 3 (base F true), p.Nonbacktracking →
    ¬ pathStabilizer F p ≤ ballKernel F p.endpoint 1
  intro p hp
  exact three_path_kernel_escape_of_intersection_normalizer F hn p hp

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
