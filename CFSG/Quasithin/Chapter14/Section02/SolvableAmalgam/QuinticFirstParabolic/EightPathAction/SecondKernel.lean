module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.EightPathAction.KernelIntersections
public import Theory.GroupAction.RankTwoCosetGeometry.SecondBallKernel

/-!
# The original quintic second-ball kernel

For X=YT, let K=O₂(H)∩O₂(X) and U=⟨Vᴴ⟩. The normal core of K in H
is exactly C_H(U): a normal subgroup centralizing V centralizes U, while
the original action on U/Z places C_H(U) in O₂(H). The identity
O₂(X)=X∩C_G(V) gives the reverse containment. Transport through the
literal coset maps identifies C_H(U) with the second-ball kernel at H.

In the Suzuki quotient branch the earlier faithful-action bound gives
64 |G_H^[2]| ≤ |T|, at every quintic vertex. The four-path consumer in
`EightPathAction` consequently has at least four distinct cosets modulo
its intersection with any quintic second-ball kernel. This measures the
remaining local movement without assuming a four-cycle at the endpoint.

Source: Aschbacher--Smith F.3.2--4 and F.7.3, pp.270,311--312;
12.8.4, p.850;14.2.6 and14.2.20--21, pp.982,988--989.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

/-- The crossing core has normal core exactly the original span centralizer. -/
theorem source_quintic_crossing_core_normalCore
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let K := H.pCoreIn 2 ⊓ X.pCoreIn 2
    (K.subgroupOf H).normalCore.map H.subtype =
      H ⊓ centralizer (conjugateSpanBy (localModule T M) H : Set G) := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let K := Q ⊓ X.pCoreIn 2
  let C := H ⊓ centralizer (U : Set G)
  let N := (K.subgroupOf H).normalCore.map H.subtype
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] using
      pCoreIn_le_sylow H (T.subtype hTH)
  have hB := (source_residualSylow_quotient hG T hempty hM hu hmany hcard e).1
  have hKle : K ≤ H := inf_le_left.trans (pCoreIn_le 2 H)
  have hnN : H ≤ normalizer (N : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,H.range_subtype] using
      (K.subgroupOf H).normalCore.le_normalizer_map H.subtype
  have hNK : N ≤ K := by
    have hh := map_mono (f := H.subtype) (K.subgroupOf H).normalCore_le
    rwa [map_subgroupOf_eq_of_le hKle] at hh
  have hNC : N ≤ C := le_inf (map_subtype_le _)
    (le_centralizer_conjugateSpanBy_of_normalizes N (localModule T M) H hnN
      ((hNK.trans inf_le_right).trans (hB.le.trans inf_le_right)))
  have hCQ : C ≤ Q := by
    obtain ⟨he,F,hp,_,_,hloc⟩ := source_lemma_14_2_6 hG T hempty hM hu hmany hcard e
    let := he
    obtain ⟨hHF,_,_,_,_,hk⟩ := hloc H hH.1
    intro c hc
    have hcQ : (⟨c,hc.1⟩ : H) ∈ pCore 2 H := by
      rw [←hk]
      apply (F.mem_localTildeAction_ker_iff H hHF _).mpr
      intro u hu
      have huU : u ∈ U := by
        change u ∈ conjugateSpanBy (rankTwoSeed T M) H at hu
        simpa only [rankTwoSeed_eq_localModule] using hu
      rw [commutatorElement_eq_one_iff_mul_comm.mpr
        (mem_centralizer_iff.mp hc.2 u huU).symm]
      exact one_mem _
    exact mem_map_of_mem H.subtype hcQ
  have hCK : C ≤ K := by
    apply le_inf hCQ
    rw [hB]
    exact le_inf (hCQ.trans (hQT.trans le_sup_right))
      (inf_le_right.trans (centralizer_le (le_conjugateSpanBy _ _)))
  have hnC : H ≤ normalizer (C : Set G) :=
    (le_inf H.le_normalizer ((le_normalizer_conjugateSpanBy _ _).trans
      (normalizer_le_normalizer_centralizer U))).trans inf_normalizer_le_normalizer_inf
  let : (C.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hnC
  have hCN : C ≤ N := by
    have hh : C.subgroupOf H ≤ (K.subgroupOf H).normalCore :=
      normal_le_normalCore.mpr (fun c hc => hCK hc)
    have hm := map_mono (f := H.subtype) hh
    rwa [map_subgroupOf_eq_of_le (show C ≤ H from inf_le_left)] at hm
  exact le_antisymm hNC hCN
open ChapterF.Section07 Subgroup.CosetGeometry.RankTwo

/-- The literal second-ball kernel is the centralizer of the original H-span. -/
theorem source_quintic_second_ball_kernel
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
    (ballKernel F (base F true) 2).map (X ⊔ H).subtype =
      H ⊓ centralizer (conjugateSpanBy (localModule T M) H : Set G) := by
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
  have hKmap : K.map L.subtype = A := by
    rw [map_inf _ _ _ L.subtype_injective,hXmap,hHmap]
  have hKmem (x : F true) : (x:L) ∈ K ↔ ((x:L):G) ∈ A := by
    rw [←hKmap]
    exact (mem_map_iff_mem (f := L.subtype) L.subtype_injective).symm
  let d : F true ≃* H := subgroupOfEquivOfLe (show H ≤ L from le_sup_right)
  have hm : (K.subgroupOf (F true)).normalCore.map
      (L.subtype.comp (F true).subtype) = (A.subgroupOf H).normalCore.map H.subtype := by
    ext g
    constructor
    · rintro ⟨x,hx,rfl⟩
      refine ⟨d x,?_,rfl⟩
      intro a
      obtain ⟨b,rfl⟩ := d.surjective a
      exact (hKmem (b*x*b⁻¹)).mp (hx b)
    · rintro ⟨x,hx,rfl⟩
      refine ⟨d.symm x,?_,?_⟩
      · intro b
        apply (hKmem (b*d.symm x*b⁻¹)).mpr
        have hh := hx (d b)
        change ((d b*x*(d b)⁻¹ : H) : G) ∈ A at hh
        change (d (b*d.symm x*b⁻¹) : G) ∈ A
        simpa only [map_mul,map_inv,d.apply_symm_apply] using hh
      · exact congrArg H.subtype (d.apply_symm_apply x)
  have hh := congrArg (fun B : Subgroup (F true) =>
    B.map (L.subtype.comp (F true).subtype)) (base_ballKernel_two F true)
  rw [←map_map,map_subgroupOf_eq_of_le (show ballKernel F (base F true) 2 ≤ F true by
    exact (ballKernel_le_stabilizer F (base F true) 2).trans
      (show stabilizer F (base F true) ≤ F true from (Subgroup.CosetGeometry.stabilizer_base F true).le))] at hh
  change (ballKernel F (base F true) 2).map L.subtype = _ at hh
  rw [hm] at hh
  exact hh.trans (by
    simpa only [A,inf_comm (X.pCoreIn 2) (H.pCoreIn 2)] using
      source_quintic_crossing_core_normalCore hG T hempty hM hu hmany hcard e H hH)

/-- Every quintic second-ball kernel has order at most a sixty-fourth of
the original Sylow order in the Suzuki branch. -/
theorem source_quintic_second_ball_kernel_card_of_suzuki
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
    ∀ v : Vertex F, v.type = true →
      64 * Nat.card (ballKernel F v 2) ≤ Nat.card (T : Subgroup G) := by
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
  have hl := source_quintic_action_core_lower hG T hempty hM hu hmany hcard e H hH hi
  have hbase : Nat.card (ballKernel F (base F true) 2) =
      Nat.card (H ⊓ centralizer (conjugateSpanBy (localModule T M) H : Set G) : Subgroup G) := by
    rw [←source_quintic_second_ball_kernel hG T hempty hM hu hmany hcard e H hH hi,
      card_map_of_injective (X ⊔ H).subtype_injective]
  change ∀ v : Vertex F, v.type = true →
    64 * Nat.card (ballKernel F v 2) ≤ Nat.card (T : Subgroup G)
  intro v hv
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  rw [hv] at hg
  rw [←hg,ballKernel_translate,card_map_of_injective (MulAut.conj g).injective,hbase]
  omega

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
