module

public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticFiveFixedRoot
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticElementarySecondKernel
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SmallSuzukiElementaryPathCard

/-!
# Cyclicity of the actual five-fixed four-group

The original odd nine-path also bounds elementary subgroups of the quintic
second kernel by thirty-two. At its quintic vertex, the second kernel fixes
five consecutive vertices. One backward and four forward elementary local
actions give the bound, using the same actual odd stabilizer. This excludes
an elementary full kernel of order sixty-four.
-/

public noncomputable section
open Subgroup SimpleGraph Theory.GroupTheory Theory.GroupTheory.AmalgamGraph
open Subgroup.CosetGeometry.RankTwo
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterF.Source ChapterF.Source.DGS85
open Reduction CommutingNontrivial CommutingThreeProfile CommutingThreeProfile.ReducedLayer

private theorem elementary_quintic_second_kernel_card_on_path
    {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (eLin : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)
    (hq : Nat.card k = 2)
    {a : Vertex (reducedFamily L S)} (p : BasedWalk (graph (reducedFamily L S)) 9 a)
    (ho : Odd (Nat.card (pathStabilizer (reducedFamily L S) p)))
    (E : Subgroup (G₀ L S)) [IsElementaryAbelian 2 E]
    (hE : E ≤ ballKernel (reducedFamily L S)
      (p.2.2.1 : Vertex (reducedFamily L S)) 2) : Nat.card E ≤ 32 := by
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hstep (v w : Vertex F) (hvw : (graph F).Adj v w)
      (D : Subgroup (G₀ L S)) (hD : IsElementaryAbelian 2 D)
      (hDv : D ≤ stabilizer F v) : (stabilizer F w).relIndex D ≤ 2 := by
    let := hD
    let : Finite D := Finite.of_injective (inclusion hDv) (inclusion_injective _)
    apply (relIndex_le_of_le_left
      ((source_Z_Q_U (reduced_triple h) v).2.trans
        ((ballKernel_one_le_edge F hvw).trans inf_le_right))
      (by exact index_ne_zero_of_finite)).trans
    exact source_small_suzuki_elementary_local_index h i eLin eSuz hq v D hDv
  have hE2 : E ≤ ballKernel F (p.2.1 : Vertex F) 1 :=
    hE.trans (ballKernel_succ_le F p.2.2.1.property.symm 1)
  have hE4 : E ≤ ballKernel F (p.2.2.2.1 : Vertex F) 1 :=
    hE.trans (ballKernel_succ_le F p.2.2.2.1.property 1)
  have hE1 : E ≤ stabilizer F (p.1 : Vertex F) :=
    hE2.trans ((ballKernel_one_le_edge F p.2.1.property.symm).trans inf_le_right)
  have hE5 : E ≤ stabilizer F (p.2.2.2.2.1 : Vertex F) :=
    hE4.trans ((ballKernel_one_le_edge F p.2.2.2.2.1.property).trans inf_le_right)
  let D := E ⊓ stabilizer F a
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le (show D ≤ E from inf_le_left)
  let : Finite E := Finite.of_injective (inclusion hE1) (inclusion_injective _)
  let : Finite D := Finite.of_injective (inclusion (show D ≤ E from inf_le_left))
    (inclusion_injective _)
  have hindex : D.relIndex E ≤ 2 := by
    rw [show D = E ⊓ stabilizer F a from rfl, inf_relIndex_left]
    exact hstep p.1 a p.1.property.symm E inferInstance hE1
  let : Finite (pathStabilizer F p) := Finite.of_injective
    (inclusion (pathStabilizer_le F p)) (inclusion_injective _)
  obtain ⟨r, hr⟩ := (IsElementaryAbelian.isPGroup 2 D).exists_card_eq
  have hd : Disjoint D (pathStabilizer F p) := disjoint_of_coprime_natCard (by
    rw [hr]; exact ho.coprime_two_left.pow_left r)
  have hfix : D ⊓ pathStabilizer F p.2.2.2.2.2 = ⊥ := by
    apply bot_unique
    apply (show D ⊓ pathStabilizer F p.2.2.2.2.2 ≤ D ⊓ pathStabilizer F p from ?_).trans
      hd.eq_bot.le
    apply le_inf inf_le_left
    intro g hg z hz
    change z ∈ a :: (p.1 : Vertex F) :: (p.2.1 : Vertex F) ::
      (p.2.2.1 : Vertex F) :: (p.2.2.2.1 : Vertex F) :: p.2.2.2.2.2.vertices at hz
    simp only [List.mem_cons] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | hz
    · exact hg.1.2
    · exact hE1 hg.1.1
    · exact ballKernel_le_stabilizer F _ 1 (hE2 hg.1.1)
    · exact ballKernel_le_stabilizer F _ 2 (hE hg.1.1)
    · exact ballKernel_le_stabilizer F _ 1 (hE4 hg.1.1)
    · exact hg.2 z hz
  have hb := elementary_path_card F hstep p.2.2.2.2.2 D
    ((show D ≤ E from inf_le_left).trans hE5)
  rw [hfix, card_bot, mul_one] at hb
  have hh := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) D E bot_le inf_le_left
  rw [relIndex_bot_left, relIndex_bot_left] at hh
  calc
    Nat.card E = Nat.card D * D.relIndex E := hh.symm
    _ ≤ 2 ^ 4 * 2 := Nat.mul_le_mul hb hindex
    _ = 32 := by decide

variable {G : Type*} [Group G] [Finite G]

/-- The literal quintic second kernel has elementary rank at most five. -/
theorem source_quintic_elementary_quintic_second_kernel_card
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
    let L : Fin 2 → Subgroup G := ![H,X]
    let J := G₀ L (T : Subgroup G)
    let F := reducedFamily L (T : Subgroup G)
    ∀ E : Subgroup J, IsElementaryAbelian 2 E →
      E ≤ ballKernel F (base F false) 2 → Nat.card E ≤ 32 := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let L : Fin 2 → Subgroup G := ![H,X]
  let J := G₀ L (T : Subgroup G)
  let F := reducedFamily L (T : Subgroup G)
  dsimp only
  intro E hEA hE
  let := hEA
  obtain ⟨hF,_,hred,_,hP,_,hmaps,_⟩ :=
    source_quintic_dgs_reduced_pair hG T hempty hM hu hmany hcard e H hH hi
  change HypothesisF11 L (T : Subgroup G) at hF
  change SuzukiContainment.reducedSylow L (T : Subgroup G) = T at hred
  change ∀ j, Reduction.P₀ L (T : Subgroup G) j = L j at hP
  have hstar' (r : Fin 2) : starredParabolic L (T : Subgroup G) r =
      Reduction.P₀ L (T : Subgroup G) r := by
    have hpar : parabolic L (T : Subgroup G) r = Reduction.P₀ L (T : Subgroup G) r := by
      rw [Reduction.P₀_eq_source hF,hred]
    exact le_antisymm ((starredParabolic_le r).trans_eq hpar)
      ((hP r).le.trans (local_le_starredParabolic r))
  have hstar (j : Bool) : star L (T : Subgroup G) j = F j := by
    cases j
    · change (starredParabolic L (T : Subgroup G) 0).subgroupOf J =
        (Reduction.P₀ L (T : Subgroup G) 0).subgroupOf J
      exact congrArg (fun K : Subgroup G => K.subgroupOf J) (hstar' 0)
    · change (starredParabolic L (T : Subgroup G) 1).subgroupOf J =
        (Reduction.P₀ L (T : Subgroup G) 1).subgroupOf J
      exact congrArg (fun K : Subgroup G => K.subgroupOf J) (hstar' 1)
  have hcommon (j : Bool) : ∃ R : Sylow 2 (star L (T : Subgroup G) j),
      (R : Subgroup (star L (T : Subgroup G) j)).map
        (star L (T : Subgroup G) j).subtype = Q F (base F (!j)) ⊔ Q F (base F j) := by
    obtain ⟨R,hR⟩ :=
      (source_quintic_dgs_common_sylow hG T hempty hM hu hmany hcard e H hH hi).2.2 j
    rw [hstar j]
    refine ⟨R,?_⟩
    cases j
    · exact hR.1.trans (sup_comm _ _)
    · exact hR.1
  obtain ⟨Tlin,hTlin⟩ := hcommon true
  obtain ⟨Ry,hRy⟩ := hcommon false
  obtain ⟨_,⟨eSuz⟩⟩ := source_quintic_suzuki_zero_quotient hG T hempty hM hu hmany hcard e H hH hi
  obtain ⟨_,⟨eX⟩⟩ := Section02.source_residualSylow_quotient hG T hempty hM hu hmany hcard e
  let eLin : (X ⧸ pCore 2 X) ≃* SL(2,ZMod 2) :=
    eX.trans SLTwoPermThree.sl2Two_equiv_perm_three.some.symm
  have hfield : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  obtain ⟨ℓ,_,j,δ,_,_,_,C,_,_,_,_,_,v₀,p,hp,hm,hy,_⟩ :=
    small_suzuki_minimal_path_fixed_nine_path hF true eLin eSuz Ry hRy
  have ho := (source_quintic_nine_path_odd hG T hempty hM hu hmany hcard e H hH hi
    p hp hm hy).1
  have hEp : E ≤ ballKernel F (p.2.2.1 : Vertex F) 2 := by
    simpa only [hy, Bool.not_true] using hE
  exact elementary_quintic_second_kernel_card_on_path
    hF true eLin eSuz hfield p ho E hEp


/-- Every elementary subgroup of the original full kernel has order at most
thirty-two, with the kernel transported through its literal graph inclusion. -/
theorem source_quintic_full_kernel_elementary_card
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hEC : E ≤ H ⊓ centralizer (conjugateSpanBy (localModule T M) H : Set G)) :
    Nat.card E ≤ 32 := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let J := G₀ ![H,X] (T : Subgroup G)
  let F := reducedFamily ![H,X] (T : Subgroup G)
  let C := H ⊓ centralizer (conjugateSpanBy (localModule T M) H : Set G)
  have hmap : (ballKernel F (base F false) 2).map J.subtype = C :=
    (source_quintic_dgs_span_and_full_kernel hG T hempty hM hu hmany hcard e H hH hi).2.2
  have hCJ : C ≤ J := hmap ▸ map_subtype_le _
  have hEJ : E ≤ J := hEC.trans hCJ
  let E₀ := E.subgroupOf J
  let : IsElementaryAbelian 2 E₀ := IsElementaryAbelian.subgroupOf hEJ
  have hE₀ : E₀ ≤ ballKernel F (base F false) 2 := by
    apply (map_le_map_iff_of_injective J.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hEJ, hmap]
    exact hEC
  have hh := source_quintic_elementary_quintic_second_kernel_card
    hG T hempty hM hu hmany hcard e H hH hi E₀ inferInstance hE₀
  rwa [Nat.card_congr (subgroupOfEquivOfLe hEJ).toEquiv] at hh

/-- The involutions of the literal full kernel generate exactly the original
quintic span. The equality holds in both actual kernel/core branches. -/
theorem source_quintic_full_kernel_omega
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let U := conjugateSpanBy (localModule T M) H
    omegaOneAmbient (H ⊓ centralizer (U : Set G)) = U := by
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let C := H ⊓ centralizer (U : Set G)
  let : IsElementaryAbelian 2 U := (Section02.SolvableAmalgam.source_index_five_closure_structure
    hG T hempty hM hu hmany hcard e H hH.1 hi).1
  have hUcard : Nat.card U = 32 := (source_quintic_span_card_and_core_radical
    hG T hempty hM hu hmany hcard e H hH hi).1
  have hUQ : U ≤ Q := (source_quintic_full_core_layers
    hG T hempty hM hu hmany hcard e H hH hi).1.ge.trans (commutator_le_self Q)
  have hUC : U ≤ C := le_inf (hUQ.trans (pCoreIn_le 2 H)) (le_centralizer U)
  apply le_antisymm
  · apply (omegaOneAmbient_le_iff C U).mpr
    intro x hx hx2
    let : IsElementaryAbelian 2 (zpowers x) := IsElementaryAbelian.zpowers_of_pow_eq_one hx2
    have hcomm : zpowers x ≤ centralizer (U : Set G) := zpowers_le.mpr hx.2
    let : IsElementaryAbelian 2 (U ⊔ zpowers x : Subgroup G) :=
      IsElementaryAbelian.sup_of_le_centralizer hcomm
    have hbound := source_quintic_full_kernel_elementary_card
      hG T hempty hM hu hmany hcard e H hH hi (U ⊔ zpowers x)
      (sup_le hUC (zpowers_le.mpr hx))
    have hjoin : U = U ⊔ zpowers x := eq_of_le_of_card_ge le_sup_left (by
      rw [hUcard]
      exact hbound)
    have hxj : x ∈ U ⊔ zpowers x :=
      (show zpowers x ≤ U ⊔ zpowers x from le_sup_right) (mem_zpowers x)
    rwa [← hjoin] at hxj
  · simpa only [omegaOneAmbient_eq_self U] using omegaOneAmbient_mono hUC

/-- The actual order-four five-fixed subgroup is cyclic. Its noncyclic case
would produce an elementary subgroup of order64 in the full second kernel,
contradicting the original odd nine-path bound. -/
theorem source_quintic_large_five_fixed_isCyclic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlarge : Nat.card (H.pCoreIn 2) = 1024)
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 5) :
    IsCyclic (H.pCoreIn 2 ⊓ centralizer (A : Set G) : Subgroup G) := by
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let C := H ⊓ centralizer (U : Set G)
  let B := Q ⊓ centralizer (A : Set G)
  change IsCyclic B
  obtain ⟨_, _, hBcard, hBcomm, _, hUR, _, _⟩ :=
    source_quintic_large_five_residual hG T hempty hM hu hmany hcard e H hH hi
      hlarge A hAH hA
  have hUcard : Nat.card U = 32 := (source_quintic_span_card_and_core_radical
    hG T hempty hM hu hmany hcard e H hH hi).1
  have hZcard : Nat.card (centralInvolutions T) = 2 :=
    plane_centralInvolutions_card T M hM.1.2 hcard e
  obtain ⟨hUfixed, hQfixed⟩ := source_quintic_five_centralizers
    hG T hempty hM hu hmany hcard e H hH hi A hAH hA
  have hBC : B ≤ C := hQfixed.le.trans inf_le_left
  have hBU : B ≤ centralizer (U : Set G) := hBC.trans inf_le_right
  have hUQ : U ≤ Q := (source_quintic_full_core_layers
    hG T hempty hM hu hmany hcard e H hH hi).1.ge.trans (commutator_le_self Q)
  let : IsElementaryAbelian 2 U := (Section02.SolvableAmalgam.source_index_five_closure_structure
    hG T hempty hM hu hmany hcard e H hH.1 hi).1
  have hUC : U ≤ C := le_inf (hUQ.trans (pCoreIn_le 2 H)) (le_centralizer U)
  have hUB : U ⊓ B = centralInvolutions T := by
    change U ⊓ (Q ⊓ centralizer (A : Set G)) = _
    rw [← inf_assoc, inf_eq_left.mpr hUQ]
    exact hUfixed
  by_contra hnot
  let : IsMulCommutative B := hBcomm
  let : IsElementaryAbelian 2 B := {
    exponent_dvd_p := by
      rw [(not_isCyclic_iff_exponent_eq_prime Nat.prime_two hBcard).mp hnot] }
  let : IsElementaryAbelian 2 (U ⊔ B : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer hBU
  have hbound : Nat.card (U ⊔ B : Subgroup G) ≤ 32 :=
    source_quintic_full_kernel_elementary_card hG T hempty hM hu hmany hcard e H hH hi
      (U ⊔ B) (sup_le hUC hBC)
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes U B
    (hBU.trans (Subgroup.centralizer_le_normalizer _))
  rw [hUcard, hBcard, hUB, hZcard] at hprod
  omega

/-- The large original branch has its actual fixed cyclic-four root outside
R, and the full centralizer kernel has Frattini subgroup exactly the original
central line. Every marking is in the original ambient group. -/
theorem source_quintic_large_five_fixed_root
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlarge : Nat.card (H.pCoreIn 2) = 1024)
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 5) :
    let U := conjugateSpanBy (localModule T M) H
    let Q := H.pCoreIn 2
    let C := H ⊓ centralizer (U : Set G)
    let B := Q ⊓ centralizer (A : Set G)
    let R := ⁅Q,A⁆
    IsCyclic B ∧ (frattini C).map C.subtype = centralInvolutions T ∧
      ∃ t : G, t ∈ B ∧ t ∉ R ∧ orderOf t = 4 ∧ zpowers t = B ∧
        zpowers (t ^ 2) = centralInvolutions T ∧ R ⊔ zpowers t = Q ∧
        t ∈ centralizer (U : Set G) := by
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let C := H ⊓ centralizer (U : Set G)
  let B := Q ⊓ centralizer (A : Set G)
  let R := ⁅Q,A⁆
  let Z := centralInvolutions T
  have hcyclic : IsCyclic B := source_quintic_large_five_fixed_isCyclic
    hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA
  let : IsCyclic B := hcyclic
  obtain ⟨_, _, hBcard, _, _, _, _, _⟩ :=
    source_quintic_large_five_residual hG T hempty hM hu hmany hcard e H hH hi
      hlarge A hAH hA
  obtain ⟨hRB, hcap, _, _, _, _⟩ := source_quintic_large_five_residual_center
    hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA
  have hBC : B ≤ C := (source_quintic_five_centralizers
    hG T hempty hM hu hmany hcard e H hH hi A hAH hA).2.le.trans inf_le_left
  have hZcard : Nat.card Z = 2 := plane_centralInvolutions_card T M hM.1.2 hcard e
  have hnot : ¬ B ≤ R := by
    intro hBR
    have hBZ : B ≤ Z := by
      intro b hb
      exact hcap.le ⟨hBR hb, hb⟩
    have hh := card_le_of_le hBZ
    change Nat.card B ≤ Nat.card Z at hh
    rw [hBcard, hZcard] at hh
    omega
  obtain ⟨t, ht⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hcyclic
  have ht4B : orderOf t = 4 := ht.trans hBcard
  have ht4 : orderOf (t : G) = 4 := by simpa only [orderOf_coe] using ht4B
  have hgen : zpowers (t : G) = B :=
    eq_of_le_of_card_ge (zpowers_le.mpr t.property) (by rw [Nat.card_zpowers, ht4, hBcard])
  have htR : (t : G) ∉ R := fun hh => hnot (hgen ▸ zpowers_le.mpr hh)
  have hCQ : C ≤ Q := source_quintic_span_centralizer_le_core hG T hM H hH hi
  let : Fact (IsPGroup 2 C) := ⟨(isPGroup_pCoreIn 2 H).to_le hCQ⟩
  have hPhiZ : (frattini C).map C.subtype ≤ Z :=
    source_quintic_full_kernel_frattini_le_point hG T hempty hM hu hmany hcard e H hH hi
  have ht2Phi : (t : G) ^ 2 ∈ (frattini C).map C.subtype :=
    mem_map_of_mem C.subtype
      (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨t, hBC t.property⟩ : C))
  have hsq : zpowers ((t : G) ^ 2) = Z := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr (hPhiZ ht2Phi))
    rw [Nat.card_zpowers, orderOf_pow, ht4, hZcard]
    decide
  have hPhi : (frattini C).map C.subtype = Z :=
    le_antisymm hPhiZ (hsq ▸ zpowers_le.mpr ht2Phi)
  exact ⟨hcyclic, hPhi, t, t.property, htR, ht4, hgen, hsq,
    hgen.symm ▸ hRB, (hBC t.property).2⟩

end CFSG.Quasithin.Chapter14.Section06
