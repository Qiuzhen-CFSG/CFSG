module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.EightPathAction.CorePairing

/-!
# First and second kernels in the original quintic graph

The full Sylow overlap identifies the two base kernels with the literal
embedded two-cores. Transport along an incident edge shows that every
cubic neighbor kernel cuts out an index-two subgroup of the quintic kernel.
The source central commutator relation puts every square in the first
quintic kernel into the second kernel. In the Suzuki row, the first
kernel has one quarter of the prescribed Sylow order at every quintic vertex.

The four-path consumer in `EightPathAction` uses these identities with its
proved path count to locate the whole fixer in the middle first kernel
and identify its elementary quotient by the middle second kernel.
No path-transitivity, endpoint model or stabilizer-order premise is assumed
in these transport results. Final path assembly remains with
qt-e-quintic-sylow-lower.

Source: Aschbacher--Smith F.3.2--4 and F.7.3, pp.270,311--312;
F.9.7, p.321;14.2.6 and14.2.20--21, pp.982,988--989.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterF.Section07 SimpleGraph Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G]

private theorem source_base_kernel_maps
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
    (ballKernel F (base F false) 1).map (X ⊔ H).subtype = X.pCoreIn 2 ∧
      (ballKernel F (base F true) 1).map (X ⊔ H).subtype = H.pCoreIn 2 := by
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
  obtain ⟨_, _, hmap⟩ := source_quintic_graph_indices
    hG T hempty hM hu hmany hcard e H hH hi
  have hSi (i : Bool) : ((S i : Subgroup (F i))).map (F i).subtype = F false ⊓ F true := by
    apply map_injective L.subtype_injective
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le (hSL i)]
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTL, hmap]
  have hk (i : Bool) : ballKernel F (base F i) 1 = (F i).pCoreIn 2 :=
    base_kernel_eq_core F i (S i) (hSi i)
  constructor
  · rw [hk, ←AmalgamLocalCores.pCoreIn_map_of_injective 2 _ L.subtype_injective]
    change ((X.subgroupOf L).map L.subtype).pCoreIn 2 = _
    rw [map_subgroupOf_eq_of_le (show X ≤ L from le_sup_left)]
  · rw [hk, ←AmalgamLocalCores.pCoreIn_map_of_injective 2 _ L.subtype_injective]
    change ((H.subgroupOf L).map L.subtype).pCoreIn 2 = _
    rw [map_subgroupOf_eq_of_le (show H ≤ L from le_sup_right)]

/-- Each incident cubic kernel cuts out an index-two subgroup of the quintic kernel. -/
theorem source_quintic_neighbor_kernel_index
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
    ∀ v w : Subgroup.CosetGeometry.Vertex F, v.type = true → (graph F).Adj v w →
      (ballKernel F w 1).relIndex (ballKernel F v 1) = 2 := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let F := Geometry.family X H
  obtain ⟨hx,hh⟩ := source_base_kernel_maps hG T hempty hM hu hmany hcard e H hH hi
  have hi0 : (ballKernel F (base F false) 1).relIndex (ballKernel F (base F true) 1) = 2 := by
    rw [←relIndex_map_map_of_injective _ _ (X ⊔ H).subtype_injective, hx, hh]
    rw [←inf_relIndex_left]
    exact source_quintic_crossing_core_index hG T hempty hM hu hmany hcard e H hH hi
  change ∀ v w : Subgroup.CosetGeometry.Vertex F, v.type = true → (graph F).Adj v w → _
  intro v w hv hadj
  have hw : w.type = false := by
    have hh := hadj.1
    rw [hv] at hh
    cases ht : w.type <;> simp_all
  obtain ⟨g,hgv,hgw⟩ := incident_common_translate F hadj.2
  rw [hv] at hgv
  rw [hw] at hgw
  rw [←hgv,←hgw,ballKernel_translate,ballKernel_translate,
    relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
  exact hi0

/-- At every quintic vertex, squares in the first kernel lie in the second kernel. -/
theorem source_quintic_first_kernel_squares
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
    ∀ v : Subgroup.CosetGeometry.Vertex F, v.type = true →
      ∀ x ∈ ballKernel F v 1, x ^ 2 ∈ ballKernel F v 2 := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let F := Geometry.family X H
  have hmap := (source_base_kernel_maps hG T hempty hM hu hmany hcard e H hH hi).2
  have hsquare : ∀ x ∈ ballKernel F (base F true) 1,
      x ^ 2 ∈ ballKernel F (base F true) 2 := by
    intro x hx
    apply (mem_map_iff_mem (f := (X ⊔ H).subtype) (X ⊔ H).subtype_injective).mp
    rw [source_quintic_second_ball_kernel hG T hempty hM hu hmany hcard e H hH hi]
    have hxQ : (x:G) ∈ H.pCoreIn 2 := hmap ▸ mem_map_of_mem (X ⊔ H).subtype hx
    exact source_quintic_core_square_centralizes hG T hempty hM hu hmany hcard e H hH hi x hxQ
  change ∀ v : Subgroup.CosetGeometry.Vertex F, v.type = true →
    ∀ x ∈ ballKernel F v 1, x ^ 2 ∈ ballKernel F v 2
  intro v hv x hx
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  rw [hv] at hg
  rw [←hg,ballKernel_translate,mem_map_equiv] at hx ⊢
  simpa only [map_pow] using hsquare _ hx

/-- The first quintic kernel has one quarter of the original Sylow order in the Suzuki row. -/
theorem source_quintic_first_kernel_card_of_suzuki
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (eH : (H ⧸ pCore 2 H) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let F := Geometry.family X H
    ∀ v : Subgroup.CosetGeometry.Vertex F, v.type = true →
      4 * Nat.card (ballKernel F v 1) = Nat.card (T : Subgroup G) := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let F := Geometry.family X H
  have hquot : Nat.card (H ⧸ pCore 2 H) = 20 :=
    (Nat.card_congr eH.toEquiv).trans BenderSuzuki.MatrixGroups.suzukiZero_card
  have hc := (pCore 2 H).index_mul_card
  change Nat.card (H ⧸ pCore 2 H) * Nat.card (pCore 2 H) = Nat.card H at hc
  rw [hquot] at hc
  have ht := ((T : Subgroup G).subgroupOf H).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hH.1.1.2).toEquiv] at ht
  change (T : Subgroup G).relIndex H * Nat.card (T : Subgroup G) = Nat.card H at ht
  rw [hi] at ht
  have hb : Nat.card (ballKernel F (base F true) 1) = Nat.card (pCore 2 H) := by
    have hm := congrArg (fun A : Subgroup G => Nat.card A)
      (source_base_kernel_maps hG T hempty hM hu hmany hcard e H hH hi).2
    rw [card_map_of_injective (X ⊔ H).subtype_injective] at hm
    exact hm.trans (card_map_of_injective H.subtype_injective)
  change ∀ v : Subgroup.CosetGeometry.Vertex F, v.type = true → _
  intro v hv
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  rw [hv] at hg
  rw [←hg,ballKernel_translate,card_map_of_injective (MulAut.conj g).injective,hb]
  omega

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
