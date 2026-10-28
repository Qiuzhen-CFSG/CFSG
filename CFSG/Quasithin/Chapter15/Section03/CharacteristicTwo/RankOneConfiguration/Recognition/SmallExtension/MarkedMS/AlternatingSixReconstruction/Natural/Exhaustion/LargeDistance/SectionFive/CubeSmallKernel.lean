module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeSmallSeeds
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.BackwardRigidity

/-!
# The full reverse kernel in the three-pair branch

On either permitted six-letter cover, the fixed hyperplane of a transposition
has a commutator of dimension at most two with the three-pair group. On the
augmentation cover, the two complementary pair-vectors span that commutator.
The proof checks only the permutations' action on the three pairs and then
uses coordinate identities for arbitrary vectors. Equivariant transport and
the last edge give an order-four bound for the full reverse critical kernel's
commutator with the second predecessor core. The incident central seed remains
in the full kernel and contributes no additional commutators.

The actual nonsylow replacement application refines the two-seed selection.
It either constructs the backward critical walk, retaining every overlapping
vertex, or produces a commutator of order two or four in both endpoint seeds.
This subgroup centralizes the starting radius but is noncentral at the backward
vertex. The same generating seed pair, cubic and failure of normalization
are retained in both alternatives. The proof derives the original three-pair image, full symmetric action
and central layer; both moved-cover orders sixteen and thirty-two are retained.

The nonzero alternative still requires exclusion before the small-image shift
and the terminal distance argument can be assembled. This is not a proof of
MS93 (5.7) or of unconditional distance two. In particular, the order-two bound
for a point-core image is not silently transferred to the three-pair image.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3)(ii), (5.2)(ii) and the kernel calculation in (5.7), printed
pp.866--867,914--915,919. This extends the full-cover and last-edge transport in
SmallBackward and BackwardFixedCore to the original nonsylow three-pair branch.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags CoreCrossing
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
namespace CubeSmallKernel
local notation "ρ" => coreRepresentation (Fin 6)
private def firstWord (i : Fin 3) : C := ![pairWord 2 3,pairWord 0 1,pairWord 0 1] i
private def secondWord (i : Fin 3) : C := ![pairWord 4 5,pairWord 4 5,pairWord 2 3] i

private theorem swaps_in_cube (t : S) (ht : t ∈ D 6) (hs : t.IsSwap) :
    ∃ i : Fin 3, t = pairSwap 6 i := by
  obtain ⟨j,rfl⟩ := (mem_disjointTranspositions_iff (3 : Fin 4) t).mp ht
  have hc : ∀ j : Fin 8, (initialWords 3 j).cycleType = {2} → ∃ i : Fin 3, initialWords 3 j = pairSwap 6 i := by
    decide +kernel
  exact hc j (Equiv.Perm.isSwap_iff_cycleType.mp hs)

private def leftCoord (i : Fin 3) : Fin 6 := ⟨2*i.val,by omega⟩
private def rightCoord (i : Fin 3) : Fin 6 := ⟨2*i.val+1,by omega⟩
private def firstCoord (i : Fin 3) : Fin 6 := ![2,0,0] i
private def secondCoord (i : Fin 3) : Fin 6 := ![4,4,2] i
private theorem cube_pair_action (j : Fin 8) (i : Fin 3) :
    ((initialWords 3 j).symm (leftCoord i)=leftCoord i ∧
      (initialWords 3 j).symm (rightCoord i)=rightCoord i) ∨
    ((initialWords 3 j).symm (leftCoord i)=rightCoord i ∧
      (initialWords 3 j).symm (rightCoord i)=leftCoord i) := by
  have h : ∀ j : Fin 8, ∀ i : Fin 3,
    ((initialWords 3 j).symm (leftCoord i)=leftCoord i ∧
      (initialWords 3 j).symm (rightCoord i)=rightCoord i) ∨
    ((initialWords 3 j).symm (leftCoord i)=rightCoord i ∧
      (initialWords 3 j).symm (rightCoord i)=leftCoord i) := by decide +kernel
  exact h j i

private theorem displacement_certificate
    (i : Fin 3) (j : Fin 8) (v : Full (Fin 6))
    (hv : representation (Fin 6) (pairSwap 6 i) v=v) :
    ∃ a b : ZMod 2, representation (Fin 6) (initialWords 3 j) v-v =
      a • (firstWord i).val + b • (secondWord i).val := by
  let w := representation (Fin 6) (initialWords 3 j) v-v
  have hp (k : Fin 3) : w (leftCoord k)=w (rightCoord k) := by
    change v ((initialWords 3 j).symm (leftCoord k))-v (leftCoord k)=
      v ((initialWords 3 j).symm (rightCoord k))-v (rightCoord k)
    rcases cube_pair_action j k with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · rw [h1,h2,sub_self,sub_self]
    · rw [h1,h2,CharTwo.sub_eq_add,CharTwo.sub_eq_add,add_comm]
  have hvpair : v (rightCoord i)=v (leftCoord i) := by
    have hh := congrFun hv (leftCoord i)
    simpa only [representation_apply,pairSwap,Equiv.symm_swap,Equiv.swap_apply_left,
      leftCoord,rightCoord] using hh
  have hz : w (leftCoord i)=0 := by
    change v ((initialWords 3 j).symm (leftCoord i))-v (leftCoord i)=0
    rcases cube_pair_action j i with ⟨h1,_⟩ | ⟨h1,_⟩
    · rw [h1,sub_self]
    · rw [h1,hvpair,sub_self]
  have h01 : w 0=w 1 := hp 0
  have h23 : w 2=w 3 := hp 1
  have h45 : w 4=w 5 := hp 2
  have he : w=w 0 • (pairWord 0 1).val+w 2 • (pairWord 2 3).val+w 4 • (pairWord 4 5).val := by
    ext k
    fin_cases k <;> simp [pairWord,h01,h23,h45]
  refine ⟨w (firstCoord i),w (secondCoord i),?_⟩
  change w=_
  conv_lhs => rw [he]
  fin_cases i
  · change w 0 • (pairWord 0 1).val+w 2 • (pairWord 2 3).val+w 4 • (pairWord 4 5).val =
      w 2 • (pairWord 2 3).val+w 4 • (pairWord 4 5).val
    have hz0 : w 0=0 := hz
    rw [hz0,zero_smul,zero_add]
  · change w 0 • (pairWord 0 1).val+w 2 • (pairWord 2 3).val+w 4 • (pairWord 4 5).val =
      w 0 • (pairWord 0 1).val+w 4 • (pairWord 4 5).val
    have hz2 : w 2=0 := hz
    rw [hz2,zero_smul,add_zero]
  · change w 0 • (pairWord 0 1).val+w 2 • (pairWord 2 3).val+w 4 • (pairWord 4 5).val =
      w 0 • (pairWord 0 1).val+w 2 • (pairWord 2 3).val
    have hz4 : w 4=0 := hz
    rw [hz4,zero_smul,add_zero]

private theorem core_displacement (i : Fin 3) (g : S) (hg : g ∈ D 6)
    (v : C) (hv : ρ (pairSwap 6 i) v=v) :
    ∃ a b : ZMod 2, ρ g v-v = a • firstWord i+b • secondWord i := by
  obtain ⟨j,rfl⟩ := (mem_disjointTranspositions_iff (3 : Fin 4) g).mp hg
  obtain ⟨a,b,hv⟩ := displacement_certificate i j v.val (congrArg Subtype.val hv)
  exact ⟨a,b,Subtype.ext hv⟩

private theorem core_fixed_displacement (u t : S)
    (ht : t ∈ (D 6).map (MulAut.conj u).toMonoidHom) (hs : t.IsSwap) :
    Module.finrank (ZMod 2) (subspaceCommutator ρ (fixedSpace ρ (zpowers t))
      ((D 6).map (MulAut.conj u).toMonoidHom)) ≤ 2 := by
  obtain ⟨t₀,ht₀,he⟩ := ht
  have hs₀ : t₀.IsSwap := by
    have hh : IsConj t₀ t := isConj_iff.mpr ⟨u,he⟩
    exact Equiv.Perm.isSwap_iff_cycleType.mpr
      ((Equiv.Perm.isConj_iff_cycleType_eq.mp hh).trans (Equiv.Perm.isSwap_iff_cycleType.mp hs))
  obtain ⟨i,rfl⟩ := swaps_in_cube t₀ ht₀ hs₀
  have hle : subspaceCommutator ρ (fixedSpace ρ (zpowers t))
      ((D 6).map (MulAut.conj u).toMonoidHom) ≤
      Submodule.span (ZMod 2) {ρ u (firstWord i),ρ u (secondWord i)} := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,v,hv,rfl⟩
    obtain ⟨k,hk,hkg⟩ := hg
    change u*k*u⁻¹=g at hkg
    rw [←hkg]
    let w := ρ u⁻¹ v
    have hw : ρ (pairSwap 6 i) w=w := by
      have hh := (mem_fixedSpace_zpowers_iff _ _ _).mp hv
      rw [←he] at hh
      change ρ (u * pairSwap 6 i * u⁻¹) v = v at hh
      have hh' := congrArg (ρ u⁻¹) hh
      simpa only [map_mul,Module.End.mul_apply,(ρ).inv_self_apply] using hh'
    obtain ⟨a,b,hmove⟩ := core_displacement i k hk w hw
    have heq := congrArg (ρ u) hmove
    rw [map_sub,map_add,map_smul,map_smul] at heq
    have heq' : ρ (u*k*u⁻¹) v-v = a • ρ u (firstWord i)+b • ρ u (secondWord i) := by
      simpa only [w,map_mul,Module.End.mul_apply,(ρ).self_inv_apply] using heq
    rw [heq']
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  apply (Submodule.finrank_mono hle).trans
  have hh := finrank_span_le_card
    ({ρ u (firstWord i),ρ u (secondWord i)} : Set C) (R := ZMod 2)
  apply hh.trans
  simp only [Set.toFinset_insert,Set.toFinset_singleton]
  exact Finset.card_le_two

private theorem fixed_movement_finrank_transport
    {Y W : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) S Y) (τ : Representation (ZMod 2) S W)
    (E : Y ≃ₗ[ZMod 2] W) (hE : ∀ g v, E (σ g v) = τ g (E v))
    (A P : Subgroup S) :
    Module.finrank (ZMod 2) (subspaceCommutator σ (fixedSpace σ A) P) =
      Module.finrank (ZMod 2) (subspaceCommutator τ (fixedSpace τ A) P) := by
  have hF : (fixedSpace σ A).map E.toLinearMap = fixedSpace τ A := by
    ext w
    constructor
    · rintro ⟨v,hv,rfl⟩ a
      change τ a (E v) = E v
      exact (hE a v).symm.trans (congrArg E (hv a))
    · intro hw
      obtain ⟨v,rfl⟩ := E.surjective w
      refine ⟨v,?_,rfl⟩
      intro a
      apply E.injective
      change E (σ a v) = E v
      exact (hE a v).trans (hw a)
  have hm := subspaceCommutator_map_embedding τ σ (MonoidHom.id S) E.toLinearMap
    (fun g v => (hE g v).symm) P (fixedSpace σ A)
  rw [hF,map_id] at hm
  rw [hm,LinearEquiv.finrank_map_eq]

private theorem model_fixed_movement
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (σ : Representation (ZMod 2) S Y)
    (hm : SixCover.IsNaturalOrCore σ (MonoidHom.id S))
    (u : S) (A : Subgroup S)
    (hA : A ≤ (D 6).map (MulAut.conj u).toMonoidHom)
    (hne : A ≠ ⊥) (hsmall : fixedCodim (naturalRepresentation (Fin 6)) A ≤ 1) :
    Module.finrank (ZMod 2) (subspaceCommutator σ (fixedSpace σ A)
      ((D 6).map (MulAut.conj u).toMonoidHom)) ≤ 2 := by
  rcases hm with ⟨E,hE⟩ | ⟨E,hE⟩
  · rw [fixed_movement_finrank_transport σ (naturalRepresentation (Fin 6)) E hE]
    apply (Submodule.finrank_mono (subspaceCommutator_mono_left _ le_top _)).trans
    rw [NaturalPairing.moved_finrank_eq_fixedCodim,fixedCodim_map_conj,fixedCodim_D.2.2.2]
  · rw [fixed_movement_finrank_transport σ ρ E hE]
    obtain ⟨t,ht,hs,he⟩ := PointCoreTranspositionFixed.small_image_eq_zpowers A hne hsmall
    rw [he]
    exact core_fixed_displacement u t (hA ht) hs

end CubeSmallKernel

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)
open scoped commutatorElement IsMulCommutative Pointwise
open Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality

include s in
/-- The full cover's fixed hyperplane has at most four commutators with a
three-pair radical, retaining the possible central line. -/
private theorem cube_cover_small_fixed_edge_card (u : S)
    (hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom)
    (A : Subgroup d.overgroup) (hA : A ≤ d.radical)
    (hne : ¬ A ≤ pCore 2 d.overgroup)
    (hindex : (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2) :
    Nat.card (⁅replacementMoved d ⊓ centralizer (A : Set d.overgroup),d.radical⁆ :
      Subgroup d.overgroup) ≤ 4 := by
  let := replacementMoved_normal h d
  let U := replacementMoved d
  let W := subspaceCommutator (coverAction s) (fixedSpace (coverAction s) (A.map s.projection))
    ((D 6).map (MulAut.conj u).toMonoidHom)
  let T := W.toAddSubgroup.toSubgroup'.map U.subtype
  have hsmall : fixedCodim (coverAction s) (A.map s.projection) ≤ 1 := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
      (replacementMoved d) s.projection s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm)] at hindex
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hindex
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A.map s.projection) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coverAction s) (naturalRepresentation (Fin 6))
      (coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
      (coverMap_surjective (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
      (coverMap_equivariant s) (A.map s.projection)).trans hsmall
  have hnA : A.map s.projection ≠ ⊥ := by
    intro he
    exact hne (s.projection_kernel ▸ (map_eq_bot_iff A).mp he)
  have hdim : Module.finrank (ZMod 2) W ≤ 2 :=
    CubeSmallKernel.model_fixed_movement (coverAction s) (cover_model s) u
      (A.map s.projection) ((map_mono hA).trans hR) hnA hnat
  have hc : ⁅U ⊓ centralizer (A : Set d.overgroup),d.radical⁆ ≤ T := by
    apply commutator_le.mpr
    intro v hv r hr
    have hcu : ⁅v,r⁆ ∈ U := (commutator_le_left U d.radical)
      (commutator_mem_commutator hv.1 hr)
    refine ⟨⟨⁅v,r⁆,hcu⟩,?_,rfl⟩
    change Additive.ofMul (⟨⁅v,r⁆,hcu⟩ : U) ∈ W
    rw [NormalElementaryQuotient.vector_commutator U s.projection s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm) ⟨v,hv.1⟩ r]
    apply W.neg_mem_iff.mp
    rw [neg_sub]
    apply Submodule.subset_span
    refine ⟨s.projection r,hR (mem_map_of_mem _ hr),Additive.ofMul ⟨v,hv.1⟩,?_,rfl⟩
    exact (NormalElementaryQuotient.mem_fixedSpace_image U s.projection s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm) A _).mpr hv.2
  apply (card_le_of_le hc).trans
  rw [card_map_of_injective U.subtype_injective]
  change Nat.card W ≤ 4
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  exact (Nat.pow_le_pow_right (by decide : 0<2) hdim)

include s in
/-- The fixed part of the entire endpoint seed has at most four commutators
with its incident edge kernel. No equality with the critical moved line is used. -/
private theorem cube_small_edge_fixed_card_at (hc : DistanceTwo.CentralLayer d) (u : S)
    (hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom)
    {c t : Vertex d.radical} (hcol : color d.radical c = false)
    (hct : Adjacent d.radical c t)
    (A : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ Q d.radical t)
    (hne : ¬ A ≤ Q d.radical c)
    (hindex : (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical c) ≤ 2) :
    Nat.card (⁅Z d.radical c ⊓ centralizer (A : Set (FreeAmalgam d.radical)),Q d.radical t⁆ :
      Subgroup (FreeAmalgam d.radical)) ≤ 4 := by
  have hcoords : ∃ i : d.overgroup →* FreeAmalgam d.radical, Function.Injective i ∧
      d.radical.map i = Q d.radical t ∧ (pCore 2 d.overgroup).map i = Q d.radical c ∧
      (replacementMoved d).map i = U d.radical c := by
    obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical c t).mp hct
    · rcases hg with ⟨rfl,rfl⟩
      let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM d.radical)
      refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective d.radical),?_,?_,?_⟩
      · have he := Q_act d.radical g (beta d.radical)
        rw [Q_beta] at he
        simpa only [beta,act_hVertex,one_mul,map_map] using he.symm
      · have he := Q_act d.radical g (alpha d.radical)
        rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)] at he
        simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
      · have he := U_act d.radical g (alpha d.radical)
        rw [hc.U_eq_moved] at he
        simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
    · rw [hg.1] at hcol
      cases hcol
  obtain ⟨i,hi,hiR,hiQ,hiU⟩ := hcoords
  have hAi : A ≤ i.range := hA.trans (hiR ▸ map_le_range i _)
  have hmA : (A.comap i).map i = A := map_comap_eq_self hAi
  have hAr : A.comap i ≤ d.radical := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hmA,hiR]
  have hAn : ¬ A.comap i ≤ pCore 2 d.overgroup := by
    intro hh
    apply hne
    have hm := map_mono (f := i) hh
    rwa [hmA,hiQ] at hm
  have hidx : (centralizer (A.comap i : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2 := by
    rw [←hiU,←hmA,←inf_relIndex_right,inf_comm,
      map_inf_centralizer_of_injective i hi,relIndex_map_map_of_injective _ _ hi,
      inf_relIndex_left] at hindex
    exact hindex
  have hcard := cube_cover_small_fixed_edge_card s u hR (A.comap i) hAr hAn hidx
  rw [←card_map_of_injective hi,map_commutator,
    ←map_inf_centralizer_of_injective i hi,hiU,hmA,hiR] at hcard
  let F := U d.radical c ⊓ centralizer (A : Set (FreeAmalgam d.radical))
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hct
    rw [hcol] at hh
    cases he : color d.radical t <;> simp_all
  have hseed : Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    intro x hx
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  have hseedA := hseed.trans (centralizer_le hA)
  have hseedN : Z d.radical t ≤ normalizer (U d.radical c : Set (FreeAmalgam d.radical)) :=
    ((adjacent_Z_le d.radical hcol hct).trans (Z_le_stabilizer d.radical c)).trans (U_normalized c)
  have heq : Z d.radical c ⊓ centralizer (A : Set (FreeAmalgam d.radical)) = F ⊔ Z d.radical t := by
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d hcol hct,
      sup_comm (U d.radical c),inf_centralizer_sup_of_centralizing _ _ _ hseedN hseedA]
    exact sup_comm _ _
  have hbound : ⁅F ⊔ Z d.radical t,Q d.radical t⁆ ≤ ⁅F,Q d.radical t⁆ := by
    apply commutator_le.mpr
    intro x hx r hr
    have hn : Z d.radical t ≤ normalizer (F : Set (FreeAmalgam d.radical)) :=
      (le_inf hseedN (hseedA.trans (centralizer (A : Set (FreeAmalgam d.radical))).le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
    have hp : x ∈ (F : Set (FreeAmalgam d.radical)) * (Z d.radical t : Set (FreeAmalgam d.radical)) := by
      rw [←coe_mul_of_right_le_normalizer_left F (Z d.radical t) hn]
      exact hx
    obtain ⟨w,hw,z,hz,rfl⟩ := hp
    have hzero : ⁅z,r⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr (hseed hz r hr).symm
    rw [commutatorElement_mul_left_eq_conj_mul,hzero,mul_one,mul_inv_cancel,one_mul]
    exact commutator_mem_commutator hw hr
  let := finite_Z d.radical c
  have hFU : ⁅F,Q d.radical t⁆ ≤ U d.radical c :=
    (commutator_mono (show F ≤ U d.radical c from inf_le_left) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp
        ((show Q d.radical t ≤ stabilizer d.radical c from
          fun _ hx => hx.2 _ (adjacent_symm d.radical hct)).trans (U_normalized c)))
  let : Finite (⁅F,Q d.radical t⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion (hFU.trans (DistanceEight.U_le_Z d.radical c))) (inclusion_injective _)
  rw [heq]
  exact (card_le_of_le hbound).trans hcard

include s in
/-- The last edge bounds the entire reverse critical kernel's commutator
with the second predecessor core, for either full central cover in the three-pair branch. -/
theorem cube_small_critical_kernel_predecessor_card
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤
      (D 6).map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    Nat.card (⁅Z d.radical a' ⊓ Q d.radical a,
      Q d.radical (p.walk.getVert (p.walk.length-2))⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 4 := by
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  let t := p.walk.getVert (p.walk.length-1)
  have hat : Adjacent d.radical a' t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.end_color] at hh
    cases he : color d.radical t <;> simp_all
  have hpred : Q d.radical (p.walk.getVert (p.walk.length-2)) ≤ Q d.radical t := by
    apply Q_le_adjacent_h d.radical ht
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hZt : Z d.radical a ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ p.start_color)
    rw [(replacementGeometry h d).distance_constant _ p.start_color,p.dist_start (Nat.sub_le _ _)]
    have he : p.walk.length = replacementDistance h d := p.length_eq_b
    change p.walk.length-1 < replacementDistance h d
    omega
  have hfixed : Z d.radical a' ⊓ Q d.radical a =
      Z d.radical a' ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · exact inf_le_inf_left _ (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a p.start_color)))
    · intro x hx
      refine ⟨hx.1,?_⟩
      rw [←C_eq_Q s hc a p.start_color]
      exact ⟨critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
        (by rw [(replacementGeometry h d).distance_constant a p.start_color]
            exact replacementDistance_pos h d) p.critical hx.1,hx.2⟩
  let := finite_Z d.radical a'
  let : Finite (U d.radical a') := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical a')) (inclusion_injective _)
  have hindex : (centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a') ≤ 2 := by
    have hQC : Q d.radical a ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a p.start_color))
    exact ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical a') index_ne_zero_of_finite)).trans_eq
        (small_critical_indices s hc p hsmall).2
  have hcard := cube_small_edge_fixed_card_at s hc u hR p.end_color hat
    (Z d.radical a) hZt p.critical.2 hindex
  rw [←hfixed] at hcard
  have hKt : Z d.radical a' ⊓ Q d.radical a ≤ Q d.radical t := by
    apply inf_le_left.trans
    apply (Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ p.end_color) ?_).trans
      (Q_le_adjacent_h d.radical ht hat)
    rw [SimpleGraph.dist_self,(replacementGeometry h d).distance_constant _ p.end_color]
    exact replacementDistance_pos h d
  let := finite_stabilizer d.radical t
  let : Finite (⁅Z d.radical a' ⊓ Q d.radical a,Q d.radical t⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion ((Subgroup.commutator_le_sup _ _).trans
      ((sup_le hKt le_rfl).trans (fun _ hx => hx.1)))) (inclusion_injective _)
  exact (card_le_of_le (commutator_mono le_rfl hpred)).trans hcard


include s in
private theorem cube_backward_kernel_obstruction
    (hc : DistanceTwo.CentralLayer d) (hb4 : 4 < replacementDistance h d)
    (u : S) (hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom)
    {a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hne : ⁅Z d.radical c,Z d.radical a' ⊓ Q d.radical (alpha d.radical)⁆ ≠ ⊥) :
    let H := ⁅Z d.radical c,Z d.radical a' ⊓ Q d.radical (alpha d.radical)⁆
    (Nat.card H = 2 ∨ Nat.card H = 4) ∧
      H ≤ Z d.radical c ⊓ Z d.radical a' ∧
      H ≤ centralizer (V d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
      ¬ H ≤ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) := by
  let K := Z d.radical a' ⊓ Q d.radical (alpha d.radical)
  let H := ⁅Z d.radical c,K⁆
  have hb : 2 < replacementDistance h d := by omega
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  have hcol : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases he : color d.radical c <;> simp_all
  have hKG : K ≤ stabilizer d.radical c :=
    (inf_le_right.trans (Q_le_adjacent_h d.radical ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
  have hHc : H ≤ Z d.radical c :=
    le_normalizer_iff_commutator_le_left.mp (hKG.trans (Z_normalized d.radical c))
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have het : Adjacent d.radical a' (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have hlast : color d.radical (p.walk.getVert (p.walk.length-1)) = true := by
    have hh := adjacent_color_ne d.radical het
    rw [p.end_color] at hh
    cases he : color d.radical (p.walk.getVert (p.walk.length-1)) <;> simp_all
  have hpre : Q d.radical (p.walk.getVert (p.walk.length-2)) ≤
      Q d.radical (p.walk.getVert (p.walk.length-1)) := by
    apply Q_le_adjacent_h d.radical hlast
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hce : Z d.radical c ≤ stabilizer d.radical a' :=
    (hbad.trans hpre).trans (fun _ hx => hx.2 _ (adjacent_symm d.radical het))
  have hHe : H ≤ Z d.radical a' :=
    (commutator_mono le_rfl inf_le_left).trans
      (le_normalizer_iff_commutator_le_right.mp (hce.trans (Z_normalized d.radical a')))
  let := finite_Z d.radical c
  let := finite_Z d.radical a'
  let : Finite H := Finite.of_injective (inclusion hHc) (inclusion_injective _)
  have hbigZ : ⁅K,Q d.radical (p.walk.getVert (p.walk.length-2))⁆ ≤ Z d.radical a' :=
    (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp
        ((hpre.trans (fun _ hx => hx.2 _ (adjacent_symm d.radical het))).trans
          (Z_normalized d.radical a')))
  let : Finite (⁅K,Q d.radical (p.walk.getVert (p.walk.length-2))⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion hbigZ) (inclusion_injective _)
  have hupper : Nat.card H ≤ 4 := by
    dsimp only [H]
    rw [commutator_comm]
    exact (card_le_of_le (commutator_mono le_rfl hbad)).trans
      (cube_small_critical_kernel_predecessor_card s hc hb u hR p hsmall)
  have hpos : 1 < Nat.card H := (one_lt_card_iff_ne_bot _).mpr hne
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) c hcol
  let : IsElementaryAbelian 2 H := IsElementaryAbelian.of_le hHc
  have hp : IsPGroup 2 H := IsElementaryAbelian.isPGroup 2 H
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hn2 : n ≤ 2 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    simpa only [hn] using hupper
  have hcard : Nat.card H=2 ∨ Nat.card H=4 := by
    interval_cases n
    · have hn0 : Nat.card H=1 := by simpa only [pow_zero] using hn
      omega
    · exact Or.inl (by simpa only [pow_one] using hn)
    · exact Or.inr (by norm_num only [Nat.reducePow] at hn; exact hn)
  have hdist : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t=1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t (alpha d.radical)=1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := c) (v := t) (w := alpha d.radical)
  have hZV : Z d.radical c ≤ V d.radical (alpha d.radical) :=
    (Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist)
  have hcentral : H ≤ centralizer (V d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) :=
    (commutator_mono hZV inf_le_right).trans
      (CFSG.Quasithin.ChapterC.BinaryMS.MS93.SectionFive.radius_commutator_central_of_four_lt
        d.radical (replacementGeometry h d) hb4 rfl)
  refine ⟨hcard,le_inf hHc hHe,hcentral,?_⟩
  intro hcent
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc c hcol
  let A := K.comap i
  have hmA : A.map i=K := map_comap_eq_self (hKG.trans_eq hir.symm)
  have hcA : ⁅replacementMoved d,A⁆ ≤ center d.overgroup := by
    intro z hz
    apply mem_center_iff.mpr
    intro m
    apply hi
    simp only [map_mul]
    apply hcent
    · have hh := mem_map_of_mem i hz
      rw [map_commutator,hmA,hiU] at hh
      exact commutator_mono (DistanceEight.U_le_Z d.radical c) le_rfl hh
    · rw [←hir]
      exact ⟨m,rfl⟩
  have hKQ := map_mono (f := i) (cover_central_commutator_forces_core s A hcA)
  rw [hmA,hiQ] at hKQ
  exact hne (le_bot_iff.mp ((commutator_mono le_rfl hKQ).trans_eq
    (Z_centralizes_Q d.radical c hcol)))

include e hz hn in
/-- The actual two-seed selection either supplies its backward critical path
or a noncentral reverse-kernel commutator of order two or four. The latter
lies in both literal endpoint seeds and centralizes the full starting radius.
All source choices, central covers and overlapping vertices are retained. -/
theorem nonsylow_small_backward_bounded_obstruction_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hel : ¬ U d.radical delta ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        ∃ x ∈ Ltilde d.radical (alpha d.radical),
          x ∈ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ∧
          x^3 ∈ Q d.radical (alpha d.radical) ∧
          Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') =
            stabilizer d.radical (alpha d.radical) ∧
          ∃ z, ∃ q : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
            ((z=a' ∧ ∀ i, q.walk.getVert i=p.walk.getVert i) ∨
              (z=act d.radical x a' ∧ ∀ i, q.walk.getVert i=act d.radical x (p.walk.getVert i))) ∧
            (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4 ∧
            (¬ Z d.radical z ≤ normalizer ((Z d.radical (act d.radical g delta) ⊔
              Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) ∧
            ((∃ v : CriticalPath d.radical (replacementGeometry h d) (act d.radical g delta)
                (q.walk.getVert (q.walk.length-2)), v.walk.getVert 1=t ∧
                ∀ i ≤ q.walk.length-2, v.walk.getVert (i+2)=q.walk.getVert i) ∨
              (Z d.radical (act d.radical g delta) ≤ Q d.radical (q.walk.getVert (q.walk.length-2)) ∧
                let H := ⁅Z d.radical (act d.radical g delta),Z d.radical z ⊓ Q d.radical (alpha d.radical)⁆
                (Nat.card H=2 ∨ Nat.card H=4) ∧
                H ≤ Z d.radical (act d.radical g delta) ⊓ Z d.radical z ∧
                H ≤ centralizer (V d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
                ¬ H ≤ centralizer (stabilizer d.radical (act d.radical g delta) : Set (FreeAmalgam d.radical)))) := by
  have hb : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨u,hfull⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hns
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hfull]
  obtain ⟨t,hat,g,hg,hgt,hct,x,hx,hxN,hx3,q₀,hq₀,hq₀s,hgen,hcases⟩ :=
    nonsylow_small_paired_seed_obstruction_knownSimple (e := e) (hz := hz) (hn := hn)
      hb4 hns p hsmall hdelta hel
  have hselected : ∃ z, ∃ q : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
      ((z=a' ∧ ∀ i, q.walk.getVert i=p.walk.getVert i) ∨
        (z=act d.radical x a' ∧ ∀ i, q.walk.getVert i=act d.radical x (p.walk.getVert i))) ∧
      (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4 ∧
      ¬ Z d.radical z ≤ normalizer ((Z d.radical (act d.radical g delta) ⊔
        Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
    rcases hcases with hcase | hcase
    · exact ⟨a',p,Or.inl ⟨rfl,fun _ => rfl⟩,hsmall,hcase⟩
    · exact ⟨act d.radical x a',q₀,Or.inr ⟨rfl,hq₀⟩,hq₀s,hcase⟩
  obtain ⟨z,q,hq,hqs,hnorm⟩ := hselected
  refine ⟨t,hat,g,hg,hgt,hct,x,hx,hxN,hx3,hgen,z,q,hq,hqs,hnorm,?_⟩
  by_cases hbad : Z d.radical (act d.radical g delta) ≤
      Q d.radical (q.walk.getVert (q.walk.length-2))
  · have hdist : (cosetGraph d.radical).dist (act d.radical g delta) (alpha d.radical) ≤ 2 := by
      have h1 : (cosetGraph d.radical).dist (act d.radical g delta) t=1 :=
        SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
      have h2 : (cosetGraph d.radical).dist t (alpha d.radical)=1 :=
        SimpleGraph.dist_eq_one_iff_adj.mpr
          ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
      simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
        (u := act d.radical g delta) (v := t) (w := alpha d.radical)
    have hZG : Z d.radical (act d.radical g delta) ≤ stabilizer d.radical (alpha d.radical) :=
      ((Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist)).trans
        ((replacementGeometry h d).V_local _ rfl hb)
    have hne : ⁅Z d.radical (act d.radical g delta),Z d.radical z ⊓ Q d.radical (alpha d.radical)⁆ ≠ ⊥ := by
      intro hzero
      apply hnorm
      have hmove := small_critical_predecessor_commutator s hc hb q hqs
        (Z d.radical (act d.radical g delta)) hbad (commutator_eq_bot_iff_le_centralizer.mp hzero)
      have hZmove : ⁅Z d.radical (alpha d.radical),Z d.radical z⁆ ≤ Z d.radical (alpha d.radical) :=
        ((critical_Z_commutator_le_moving (h := h) q).trans inf_le_left).trans
          (DistanceEight.U_le_Z d.radical _)
      have hh := commutator_sup_le_of_relative_normal (stabilizer d.radical (alpha d.radical))
        (Z d.radical (act d.radical g delta)) (Z d.radical (alpha d.radical)) (Z d.radical z)
        (Z d.radical (alpha d.radical)) (Z_normalized d.radical _) hZG
        (Z_le_stabilizer d.radical _) hmove hZmove
      exact le_normalizer_iff_commutator_le_left.mpr (hh.trans le_sup_right)
    exact Or.inr ⟨hbad,cube_backward_kernel_obstruction s hc hb4 u hR q hqs hat hct hbad hne⟩
  · have hcol : color d.radical (act d.radical g delta) = false := by
      have h1 := adjacent_color_ne d.radical hat
      have h2 := adjacent_color_ne d.radical hct
      change false ≠ color d.radical t at h1
      cases hc : color d.radical (act d.radical g delta) <;>
        cases ht : color d.radical t <;> simp_all
    let w : (cosetGraph d.radical).Walk (act d.radical g delta) (alpha d.radical) :=
      .cons ((cosetGraph_adj d.radical _ _).mpr hct)
        (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
    have hw : w.length=2 := rfl
    let v := q.prepend_two (Nat.le_of_lt hb) hcol w hw hbad
    have hvt : v.walk.getVert 1=t := by
      simp only [v,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
        hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
        SimpleGraph.Walk.getVert_zero]
    exact Or.inl ⟨v,hvt,fun i hi => q.prepend_two_overlap _ _ _ _ _ hi⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
