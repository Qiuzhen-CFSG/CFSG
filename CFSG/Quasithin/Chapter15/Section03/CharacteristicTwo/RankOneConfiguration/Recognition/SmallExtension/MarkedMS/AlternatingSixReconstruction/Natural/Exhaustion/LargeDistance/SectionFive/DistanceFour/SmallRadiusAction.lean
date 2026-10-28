module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SmallRadius
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeKernelLine
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeKernelLine

/-!
# Whole-radius commutators of small critical kernels

Assume all critical images at the original base have order two. On a critical
path a--c--z of length four, the whole midpoint radius W = V_c has image
contained in a conjugate of the three-disjoint-transposition subgroup. Its
endpoint seed Z_z has a transposition image in that same subgroup.

On the augmentation cover, the fixed hyperplane of one of these transpositions
has displacement contained in the two remaining pair lines. On the natural
cover the whole cube displacement already has dimension at most two. Hence
the commutator of the moving critical kernel with W has order at most four.
The existing cube comparison says that if this commutator has order greater
than two, it contains the whole moving-cover displacement modulo the critical
transposition line.

The full seed is the moving cover joined with its first-edge central seed.
That entire central attachment fixes both W and Z_z. Thus the full critical
kernel K = Z_a intersect Q_z has the same commutator as the moving kernel:
|[K,W]| <= 4, and |[K,W]| > 2 implies [Z_a,W] <= [K,W][Z_a,Z_z].
Conjugation transports the bound and comparison to every critical path.
The literal replacement application retains the existing index-two fixed
bound as well as both critical indices, with no radical-image specialization.

This is an internal continuation of the cube-kernel comparison in SectionFive;
the private import reuses its checked pair-coordinate calculation and central
attachment identity without changing their public boundary. The small-image
residual-compatible selection, the separately owned selected terminal family,
and unconditional DistanceFourInput remain to be proved.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the kernel and residual comparison of (5.8), printed pp.919--920,
and the initial selection in (5.12), p.924. The proof uses the actual symmetric
projection and both full moving covers of orders sixteen and thirty-two.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)
open Representation Representation.BinaryOffender BinaryPermutation


open Theory.SpecificGroups.SymmetricSix.BinaryFlags CoreCrossing CubeKernelLine
private abbrev S := Equiv.Perm (Fin 6)
local notation "ρ" => coreRepresentation (Fin 6)
private theorem core_fixed_commutator_dim (u t : S) (P : Subgroup S)
    (hP : P ≤ (D 6).map (MulAut.conj u).toMonoidHom)
    (ht : t ∈ (D 6).map (MulAut.conj u).toMonoidHom) (hs : t.IsSwap)
    : Module.finrank (ZMod 2)
        (subspaceCommutator ρ (fixedSpace ρ (zpowers t)) P) ≤ 2 := by
  obtain ⟨t₀,ht₀,he⟩ := ht
  have hs₀ : t₀.IsSwap := by
    have hh : IsConj t₀ t := isConj_iff.mpr ⟨u,he⟩
    exact Equiv.Perm.isSwap_iff_cycleType.mpr
      ((Equiv.Perm.isConj_iff_cycleType_eq.mp hh).trans (Equiv.Perm.isSwap_iff_cycleType.mp hs))
  obtain ⟨i,rfl⟩ := swaps_in_cube t₀ ht₀ hs₀
  let F := Submodule.span (ZMod 2) {ρ u (firstWord i),ρ u (secondWord i)}
  let K := subspaceCommutator ρ (fixedSpace ρ (zpowers t)) P
  have hKF : K ≤ F := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,v,hv,rfl⟩
    obtain ⟨k,hk,hkg⟩ := hP hg
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
  have hdim : Module.finrank (ZMod 2) F ≤ 2 := by
    apply (finrank_span_le_card ({ρ u (firstWord i),ρ u (secondWord i)} : Set C) (R := ZMod 2)).trans
    simp only [Set.toFinset_insert,Set.toFinset_singleton]
    exact Finset.card_le_two
  exact (Submodule.finrank_mono hKF).trans hdim

private theorem model_fixed_commutator_dim
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (σ : Representation (ZMod 2) S Y)
    (hm : SixCover.IsNaturalOrCore σ (MonoidHom.id S))
    (u t : S) (P : Subgroup S)
    (hP : P ≤ (D 6).map (MulAut.conj u).toMonoidHom)
    (ht : t ∈ (D 6).map (MulAut.conj u).toMonoidHom) (hs : t.IsSwap) :
    Module.finrank (ZMod 2) (subspaceCommutator σ (fixedSpace σ (zpowers t)) P) ≤ 2 := by
  have transport {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
      (τ : Representation (ZMod 2) S W) (E : Y ≃ₗ[ZMod 2] W)
      (hE : ∀ g v, E (σ g v) = τ g (E v))
      (hbound : Module.finrank (ZMod 2) (subspaceCommutator τ (fixedSpace τ (zpowers t)) P) ≤ 2) :
      Module.finrank (ZMod 2) (subspaceCommutator σ (fixedSpace σ (zpowers t)) P) ≤ 2 := by
    have hF := fixedSpace_map_equivariant σ τ (MonoidHom.id S) E hE (zpowers t)
    rw [map_id] at hF
    have hK := subspaceCommutator_map_embedding τ σ (MonoidHom.id S) E.toLinearMap
      (fun g v => (hE g v).symm) P (fixedSpace σ (zpowers t))
    rw [hF,map_id] at hK
    rwa [hK,LinearEquiv.finrank_map_eq] at hbound
  rcases hm with ⟨E,hE⟩ | ⟨E,hE⟩
  · apply transport (naturalRepresentation (Fin 6)) E hE
    have hle : subspaceCommutator (naturalRepresentation (Fin 6))
        (fixedSpace (naturalRepresentation (Fin 6)) (zpowers t)) P ≤
        subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ ((D 6).map (MulAut.conj u).toMonoidHom) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨g,hg,v,_,rfl⟩
      exact Submodule.subset_span ⟨g,hP hg,v,Submodule.mem_top,rfl⟩
    apply (Submodule.finrank_mono hle).trans
    rw [NaturalPairing.moved_finrank_eq_fixedCodim,fixedCodim_map_conj,fixedCodim_D.2.2.2]
  · exact transport ρ E hE (core_fixed_commutator_dim u t P hP ht hs)

open Representation.NormalElementaryQuotient
private theorem cover_kernel_cube_bounds (A P : Subgroup d.overgroup) (u t : S)
    (hP : P.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom)
    (ht : t ∈ (D 6).map (MulAut.conj u).toMonoidHom) (hs : t.IsSwap)
    (hA : A.map s.projection = zpowers t) :
    let K := ⁅replacementMoved d ⊓ centralizer (A : Set d.overgroup),P⁆
    Nat.card K ≤ 4 ∧ (2 < Nat.card K →
      ⁅replacementMoved d,P⁆ ≤ K ⊔ ⁅replacementMoved d,A⁆) := by
  let := replacementMoved_normal h d
  let U := replacementMoved d
  let F := U ⊓ centralizer (A : Set d.overgroup)
  let K := ⁅F,P⁆
  have hKU : K ≤ U := (commutator_mono inf_le_left le_rfl).trans (commutator_le_left U P)
  let : IsElementaryAbelian 2 K := IsElementaryAbelian.of_le hKU
  have hker := s.projection_kernel.trans (moved_centralizer s).symm
  have hF : subgroupSpace U F = fixedSpace (coverAction s) (A.map s.projection) := by
    ext v
    change ((v.toMul : d.overgroup) ∈ U ∧ (v.toMul : d.overgroup) ∈ centralizer (A : Set d.overgroup)) ↔ _
    simp only [v.toMul.property,true_and]
    exact (mem_fixedSpace_image U s.projection s.surjective hker A v).symm
  have hK : subgroupSpace U K = subspaceCommutator (coverAction s)
      (fixedSpace (coverAction s) (zpowers t)) (P.map s.projection) := by
    rw [subgroupSpace_commutator U s.projection s.surjective hker F P inf_le_left,hF,hA]
    rfl
  have hU : subgroupSpace U U = ⊤ := by ext v; exact iff_of_true v.toMul.property trivial
  have hcard : Nat.card K = 2 ^ Module.finrank (ZMod 2) (subgroupSpace U K) := by
    calc Nat.card K = Nat.card (Additive K) := rfl
         _ = Nat.card (subgroupSpace U K) := Nat.card_congr (subgroupSpaceEquiv U K hKU).toEquiv
         _ = _ := by rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  have hdim : Module.finrank (ZMod 2) (subgroupSpace U K) ≤ 2 := by
    rw [hK]
    exact model_fixed_commutator_dim (coverAction s) (cover_model s) u t _ hP ht hs
  refine ⟨?_,?_⟩
  · change Nat.card K ≤ 4
    rw [hcard]
    exact Nat.pow_le_pow_right (by decide) hdim
  · intro hlarge
    have hdim' : 1 < Module.finrank (ZMod 2) (subgroupSpace U K) := by
      change 2 < Nat.card K at hlarge
      rw [hcard] at hlarge
      exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlarge
    rw [hK] at hdim'
    have hb := CubeKernelLine.model_comparison (coverAction s) (cover_model s) u t
      (P.map s.projection) hP ht hs hdim'
    rw [←hA,←hF] at hb
    have hwhole (B : Subgroup d.overgroup) : subgroupSpace U ⁅U,B⁆ =
        subspaceCommutator (coverAction s) ⊤ (B.map s.projection) := by
      rw [subgroupSpace_commutator U s.projection s.surjective hker U B le_rfl,hU]
      rfl
    have hK' : subgroupSpace U K = subspaceCommutator (coverAction s)
        (subgroupSpace U F) (P.map s.projection) := by
      rw [subgroupSpace_commutator U s.projection s.surjective hker F P inf_le_left]
      rfl
    rw [←hwhole P,←hK',←hwhole A,←subgroupSpace_sup U hKU (commutator_le_left U A)] at hb
    intro v hv
    exact hb (show Additive.ofMul (⟨v,(commutator_le_left U P) hv⟩ : U) ∈ subgroupSpace U ⁅U,P⁆ from hv)

private theorem embedded_kernel_cube_bounds {H : Type*} [Group H]
    (i : d.overgroup →* H) (hi : Function.Injective i)
    (A P : Subgroup H) (hA : A ≤ i.range) (hP : P ≤ i.range) (u t : S)
    (hPi : (P.comap i).map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom)
    (ht : t ∈ (D 6).map (MulAut.conj u).toMonoidHom) (hs : t.IsSwap)
    (hAi : (A.comap i).map s.projection = zpowers t) :
    let K := ⁅(replacementMoved d).map i ⊓ centralizer (A : Set H),P⁆
    Nat.card K ≤ 4 ∧ (2 < Nat.card K →
      ⁅(replacementMoved d).map i,P⁆ ≤ K ⊔ ⁅(replacementMoved d).map i,A⁆) := by
  have hmA : (A.comap i).map i = A := map_comap_eq_self hA
  have hmP : (P.comap i).map i = P := map_comap_eq_self hP
  have hh := cover_kernel_cube_bounds s (A.comap i) (P.comap i) u t hPi ht hs hAi
  have hK : (⁅replacementMoved d ⊓ centralizer (A.comap i : Set d.overgroup),P.comap i⁆ :
      Subgroup d.overgroup).map i = ⁅(replacementMoved d).map i ⊓ centralizer (A : Set H),P⁆ := by
    rw [map_commutator,←map_inf_centralizer_of_injective i hi,hmA,hmP]
  have hcard : Nat.card (⁅(replacementMoved d).map i ⊓ centralizer (A : Set H),P⁆ : Subgroup H) =
      Nat.card (⁅replacementMoved d ⊓ centralizer (A.comap i : Set d.overgroup),P.comap i⁆ :
        Subgroup d.overgroup) := by
    rw [←hK,card_map_of_injective hi]
  refine ⟨by simpa only [hcard] using hh.1,?_⟩
  intro hlarge
  have hb := map_mono (f := i) (hh.2 (by simpa only [hcard] using hlarge))
  rwa [Subgroup.map_sup,hK,map_commutator,map_commutator,hmA,hmP] at hb

include s in
/-- The commutator of the whole midpoint radius with the full critical kernel
has order at most four. If this commutator has more than two elements, it contains all movement
of the starting seed modulo the original critical commutator. -/
theorem small_images_midpoint_kernel_commutator
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (hsmall : ∀ z, ∀ _p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
      (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    let N := ⁅Z d.radical (alpha d.radical) ⊓ Q d.radical a',V d.radical (p.walk.getVert 2)⁆
    Nat.card N ≤ 4 ∧ (2 < Nat.card N →
      ⁅Z d.radical (alpha d.radical),V d.radical (p.walk.getVert 2)⁆ ≤
        N ⊔ ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆) := by
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let W := V d.radical c
  have hcCol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hca : (cosetGraph d.radical).dist c (alpha d.radical) = 2 := by
    rw [SimpleGraph.dist_comm,p.dist_start (by omega)]
  have hat : Adjacent d.radical (alpha d.radical) t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical c t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have htCol : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  have hWt : W ≤ Q d.radical t := by
    apply V_le_Q_of_dist_add_two_lt d.radical hcCol
    have hdist : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    change (cosetGraph d.radical).dist c t + 2 < replacementDistance h d
    omega
  have hWbase : W ≤ stabilizer d.radical (alpha d.radical) :=
    fun _ hx => (hWt hx).2 _ (adjacent_symm d.radical hat)
  have hAW : Z d.radical a' ≤ W := by
    apply le_iSup_of_le a'
    apply le_iSup_of_le (show (cosetGraph d.radical).dist a' c ≤ 2 from ?_)
    · exact le_rfl
    · rw [SimpleGraph.dist_comm,p.dist_end,hl]
  obtain ⟨u,hu⟩ := radius_image_le_cube_of_small_critical_images s hc hb hsmall c hcCol hca.le
  obtain ⟨v,hv,hAv⟩ := small_critical_image_eq_swap s hc p (hsmall a' p)
  have hvA : v ∈ graphImage s (Z d.radical a') := by
    rw [hAv]
    exact mem_zpowers v
  have hvCube : v ∈ (D 6).map (MulAut.conj u).toMonoidHom :=
    hu ((map_mono (comap_mono hAW)) hvA)
  have hbounds := embedded_kernel_cube_bounds s (embedM d.radical) (embedM_injective d.radical)
    (Z d.radical a') W ((hAW.trans hWbase).trans_eq (stabilizer_m_base d.radical))
    (hWbase.trans_eq (stabilizer_m_base d.radical)) u v hu hvCube hv hAv
  rw [←hc.U_eq_moved] at hbounds
  have hseed : Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    intro x hx
    rw [Z,if_neg (by simp [htCol])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  have hseedW := hseed.trans (centralizer_le hWt)
  have hseedA := hseedW.trans (centralizer_le hAW)
  have hseedN : Z d.radical t ≤ normalizer (U d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) :=
    ((adjacent_Z_le d.radical rfl hat).trans (Z_le_stabilizer d.radical _)).trans (U_normalized _)
  have hfixed : Z d.radical (alpha d.radical) ⊓ Q d.radical a' =
      Z d.radical (alpha d.radical) ⊓ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · exact inf_le_inf_left _ (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a' p.end_color)))
    · apply le_inf inf_le_left
      rw [←C_eq_Q s hc a' p.end_color]
      exact le_inf (inf_le_left.trans (Z_le_stabilizer_of_dist_le (alpha d.radical) _ p.critical.1.le))
        inf_le_right
  let F := U d.radical (alpha d.radical) ⊓ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical))
  have hdecomp : Z d.radical (alpha d.radical) ⊓ Q d.radical a' = F ⊔ Z d.radical t := by
    rw [hfixed,DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d rfl hat,
      sup_comm (U d.radical (alpha d.radical)),
      inf_centralizer_sup_of_centralizing _ _ _ hseedN hseedA]
    exact sup_comm _ _
  have hNF : Z d.radical t ≤ normalizer (F : Set (FreeAmalgam d.radical)) :=
    (le_inf hseedN (hseedA.trans (centralizer (Z d.radical a' : Set (FreeAmalgam d.radical))).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hcomm : ⁅Z d.radical (alpha d.radical) ⊓ Q d.radical a',W⁆ = ⁅F,W⁆ := by
    rw [hdecomp,commutator_sup_of_central_attachment F _ W hNF hseedW]
  have hwhole (X : Subgroup (FreeAmalgam d.radical)) (hX : X ≤ W) :
      ⁅Z d.radical (alpha d.radical),X⁆ = ⁅U d.radical (alpha d.radical),X⁆ := by
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d rfl hat,
      commutator_sup_of_central_attachment _ _ X hseedN (hseedW.trans (centralizer_le hX))]
  change Nat.card (⁅Z d.radical (alpha d.radical) ⊓ Q d.radical a',W⁆ : Subgroup _) ≤ 4 ∧ _
  rw [hcomm,hwhole W le_rfl,hwhole (Z d.radical a') hAW]
  exact hbounds

include s in
/-- The order bound and whole-seed comparison on every literal critical path,
including the reversed orientation, using the same full critical kernel. -/
theorem small_images_midpoint_kernel_commutator_at
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (hsmall : ∀ z, ∀ _p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
      (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z) :
    let N := ⁅Z d.radical a ⊓ Q d.radical z,V d.radical (p.walk.getVert 2)⁆
    Nat.card N ≤ 4 ∧ (2 < Nat.card N →
      ⁅Z d.radical a,V d.radical (p.walk.getVert 2)⁆ ≤ N ⊔ ⁅Z d.radical a,Z d.radical z⁆) := by
  obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical j⁻¹ a = alpha d.radical := by
    rw [hj,act_mVertex,mul_inv_cancel]
    rfl
  have base : ∀ q : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical j⁻¹ a) (act d.radical j⁻¹ z),
      let N := ⁅Z d.radical (act d.radical j⁻¹ a) ⊓ Q d.radical (act d.radical j⁻¹ z),
        V d.radical (q.walk.getVert 2)⁆
      Nat.card N ≤ 4 ∧ (2 < Nat.card N →
        ⁅Z d.radical (act d.radical j⁻¹ a),V d.radical (q.walk.getVert 2)⁆ ≤
          N ⊔ ⁅Z d.radical (act d.radical j⁻¹ a),Z d.radical (act d.radical j⁻¹ z)⁆) := by
    rw [hbase]
    intro q
    exact small_images_midpoint_kernel_commutator s hc hb hsmall q
  have hh := base (p.act j⁻¹)
  dsimp only at hh ⊢
  simp only [CriticalPath.act,actWalk_getVert,V_act,Z_act,Q_act,inv_inv] at hh
  rw [←Subgroup.map_inf _ _ _ (MulAut.conj j).injective] at hh
  simp only [←map_commutator,←Subgroup.map_sup,
    card_map_of_injective (f := (MulAut.conj j).toMonoidHom) (MulAut.conj j).injective,
    map_le_map_iff_of_injective (f := (MulAut.conj j).toMonoidHom) (MulAut.conj j).injective] at hh
  exact hh

include e hz hn in
/-- In the actual initial-selection alternative, uniformly small critical
images give both full-kernel bounds and the whole-seed commutator comparison.
The small-image selection exclusion remains to be proved. -/
theorem initial_selection_or_small_midpoint_commutators_knownSimple
    (hb : replacementDistance h d = 4) :
    (∃ z, ∃ p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
      ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
        localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (p.walk.getVert 2))) ∨
    ((∀ z, ∀ _p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
      (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) = 2 ∧
        (Q d.radical (alpha d.radical)).relIndex (Z d.radical z) = 2) ∧
    ∀ (a z : Vertex d.radical) (p : CriticalPath d.radical (replacementGeometry h d) a z),
      let K := Z d.radical a ⊓ Q d.radical z
      let W := V d.radical (p.walk.getVert 2)
      (centralizer (W : Set (FreeAmalgam d.radical))).relIndex K ≤ 2 ∧
      Nat.card (⁅K,W⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 4 ∧
      (2 < Nat.card (⁅K,W⁆ : Subgroup (FreeAmalgam d.radical)) →
        ⁅Z d.radical a,W⁆ ≤ ⁅K,W⁆ ⊔ ⁅Z d.radical a,Z d.radical z⁆)) := by
  rcases initial_selection_or_cube_radius_knownSimple (e := e) (hz := hz) (hn := hn) hb with hsel | hsmall
  · exact Or.inl hsel
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hs : ∀ z, ∀ _p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z,
      (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4 :=
    fun z p => by rw [(hsmall.2.1 z p).1]; decide
  exact Or.inr ⟨hsmall.2.1,fun a z p =>
    ⟨(small_images_midpoint_fixed_indices_at s hc hb hs p).2,
      small_images_midpoint_kernel_commutator_at s hc hb hs p⟩⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
