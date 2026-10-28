module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.CubicParity
public import Theory.SpecificGroups.SL2.CubicCopiesLength
/-!
# The original cubic fixed-point obstruction

The cubic centralizer of the local two-core maps trivially into the
four-letter Klein group, so it lies in the actual pair core. Natural
SL₂(4) coordinates make that core's upper quotient fixed-point-free.
Every such fixed element therefore lies in the elementary second layer,
which excludes the order-four witness supplied by the G₂ source case.
Source: Aschbacher–Smith13.5.25, printed p.925.
-/
public section
open Subgroup NoncentralChiefRefinement NoncentralChiefRefinement.CubicComparison
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.CubicFixed
open Section08.SourceCompletion NormalBranch
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks SourceFiveModule SourceUpperStructure
open ChapterG.Section02.Setup
open ChapterG.Section02.AlternatingFive.Recognition.ProjectiveGeometry
open ClosureLayers ClosureUpper
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
private theorem klein_core : pCore 2 (alternatingGroup (Fin 4))≤GLS3.Chapter5.alternatingFourKlein := by
  let U := GLS3.Chapter5.alternatingFourKlein
  let q := QuotientGroup.mk' U
  have hcard : Nat.card ((alternatingGroup (Fin 4))⧸U)=3 := by
    have hc := U.card_mul_index
    rw [GLS3.Chapter5.alternatingFourKlein_card,index_eq_card,nat_card_alternatingGroup] at hc
    norm_num at hc ⊢
    omega
  have h3 : IsPGroup 3 ((alternatingGroup (Fin 4))⧸U) := IsPGroup.of_card (n:=1) hcard
  have he : (pCore 2 (alternatingGroup (Fin 4))).map q=⊥ := by
    simpa only [inf_idem] using
      (IsPGroup.disjoint_of_coprime (pCore_isPGroup.map q)
        (h3.to_subgroup ((pCore 2 (alternatingGroup (Fin 4))).map q)) (by decide : Nat.Coprime 2 3)).eq_bot
  intro x hx
  have hh := mem_map_of_mem q hx
  rw [he,mem_bot] at hh
  exact (QuotientGroup.eq_one_iff x).mp hh

private theorem klein_fixed (B : Subgroup (alternatingGroup (Fin 4)))
    (hB : Nat.card B=3) (u : GLS3.Chapter5.alternatingFourKlein)
    (hu : ∀b∈B,b*u.val*b⁻¹=u.val) : u=1 := by
  let C := (centralizer (B:Set (alternatingGroup (Fin 4)))).subgroupOf GLS3.Chapter5.alternatingFourKlein
  have hc := GLS3.Chapter5.cubic_length_one_of_card_three B hB
  change Nat.log 4 C.index=1 at hc
  have hge := Nat.pow_log_le_self 4 (Subgroup.FiniteIndex.index_ne_zero (H:=C))
  rw [hc] at hge
  have hcard := C.card_mul_index
  rw [GLS3.Chapter5.alternatingFourKlein_card] at hcard
  have hpos : 0<Nat.card C := Nat.card_pos
  have hC : C=⊥ := eq_bot_of_card_eq C (by nlinarith)
  have huC : u∈C := by
    intro b hb
    exact mul_inv_eq_iff_eq_mul.mp (hu b hb)
  rwa [hC,mem_bot] at huC

include d
/-- The cubic fixed part of the original local two-core lies in the pair kernel. -/
theorem fixed_local_core_le_pair_core (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
    (g : D.L) (hK : NormalBranch.K D g.val≤D.L) (hL : D.L₁≤NormalBranch.K D g.val)
    (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d)=
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    (A : Subgroup G) (hAL : A≤D.L₁) (hA : Nat.card A=3) :
    D.L₁.pCoreIn 2⊓centralizer (A:Set G)≤(NormalBranch.K D g.val).pCoreIn 2 := by
  obtain ⟨f,hf,hk,hp⟩ := CubicCount.exists_residual_actor d h e g hK hL a hi
  have hB : Nat.card ((A.subgroupOf D.L₁).map f)=3 :=
    GLS3.Chapter5.cubic_image_card_of_two_kernel f hp (A.subgroupOf D.L₁)
      ((Nat.card_congr (subgroupOfEquivOfLe hAL).toEquiv).trans hA)
  rintro j ⟨⟨x,hx,rfl⟩,hj⟩
  have hxcore : f x∈pCore 2 (alternatingGroup (Fin 4)) :=
    (f.comap_pCore_of_ker_isPGroup hf hp).symm.le hx
  have hfix : (⟨f x,klein_core hxcore⟩:GLS3.Chapter5.alternatingFourKlein)=1 := by
    apply klein_fixed _ hB
    rintro _ ⟨b,hb,rfl⟩
    have he : b*x*b⁻¹=x := by
      apply Subtype.ext
      change b.val*x.val*b.val⁻¹=x.val
      have hh : b.val*x.val=x.val*b.val := mem_centralizer_iff.mp hj b.val hb
      rw [hh,mul_inv_cancel_right]
    simpa only [map_mul,map_inv] using congrArg f he
  have hxker : x∈f.ker := congrArg Subtype.val hfix
  exact hk.le hxker

theorem fixed_pair_core_le_second (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
    (htilde : D.tilde D.UH=⁅D.tilde D.UH,D.tilde D.L₁⁆)
    (hU : ¬ IsMulCommutative D.UH) (g : D.L) (hgn : g.val∉D.Gz)
    (hg : g.val∈NormalBranch.K D g.val)
    (hK : NormalBranch.K D g.val≤D.L) (hL : D.L₁≤NormalBranch.K D g.val)
    (hp : IsPPerfect 2 (NormalBranch.K D g.val)) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d)=
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Finite E]
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 5)) E)
    (c : Representation.BinaryConjugationSection (NormalBranch.K D g.val)
      ((NormalBranch.K D g.val).pCoreIn 2) (second D g.val) (σ.comp (restrictedActor d hK a hi)))
    (A : Subgroup G) (hAL : A≤D.L₁) (hA : Nat.card A=3) :
    (NormalBranch.K D g.val).pCoreIn 2⊓centralizer (A:Set G)≤second D g.val := by
  let := (ZMod.algebra F4 2).toModule
  obtain ⟨m,r,q,heq⟩ := natural_coordinates d h e htilde hU g hgn hg hK hL hp a hi σ c
  have hAK := hAL.trans hL
  let f : A→*alternatingGroup (Fin 5) := (restrictedActor d hK a hi).comp (inclusion hAK)
  have hker : IsPGroup 2 f.ker := by
    change IsPGroup 2 ((restrictedActor d hK a hi).comp (inclusion hAK)).ker
    rw [←MonoidHom.comap_ker]
    apply IsPGroup.comap_of_injective _ _ (inclusion_injective hAK)
    rw [restrictedActor_ker_eq_twoCore d hK a hi e]
    exact pCore_isPGroup
  have h3 : IsPGroup 3 A := IsPGroup.of_card (n:=1) hA
  have hb : f.ker=⊥ := by
    simpa only [inf_idem] using (IsPGroup.disjoint_of_coprime hker (h3.to_subgroup f.ker) (by decide)).eq_bot
  have hf : Function.Injective (m.toMonoidHom.comp f) := m.injective.comp ((MonoidHom.ker_eq_bot_iff f).mp hb)
  have hc : Nat.card (m.toMonoidHom.comp f).range=3 :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans hA
  let := Representation.BinaryFixedPoints.action (σ.comp f)
  have hz := Representation.BinaryFixedPoints.sl2_four_fixed_eq_bot (σ.comp f)
    (m.toMonoidHom.comp f) hc r q (fun a v j => heq (f a) v j)
  intro j hj
  let u : (NormalBranch.K D g.val).pCoreIn 2 := ⟨j,hj.1⟩
  have hfix : c.coordinates u∈FixedPoints.subgroup A (Multiplicative E) := by
    intro a
    apply Multiplicative.toAdd.injective
    have he := c.equivariant (inclusion hAK a) u
    have hu : (⟨(inclusion hAK a).val*u.val*(inclusion hAK a).val⁻¹,
      (mem_normalizer_iff.mp (c.normalized (inclusion hAK a).property) u.val).mp u.property⟩ :
        (NormalBranch.K D g.val).pCoreIn 2)=u := by
      apply Subtype.ext
      change a.val*j*a.val⁻¹=j
      rw [mem_centralizer_iff.mp hj.2 a.val a.property,mul_inv_cancel_right]
    rw [hu] at he
    exact he.symm
  rw [hz,mem_bot] at hfix
  exact (c.coordinates_eq_one_iff u).mp hfix

/-- The exact order-four witness needed for the G₂ source case is impossible. -/
theorem order_four_cubic_fixed_false (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
    (htilde : D.tilde D.UH=⁅D.tilde D.UH,D.tilde D.L₁⁆)
    (hU : ¬ IsMulCommutative D.UH)
    (A : Subgroup G) (hAL : A≤D.L₁) (hA : Nat.card A=3)
    (j : G) (hjU : j∈D.UH) (hj : orderOf j=4) (hjA : j∈centralizer (A:Set G)) : False := by
  obtain ⟨a,g,hgn,hg,hK,hL,hp,_,_,hi⟩ := ClosurePair.exists_source_pair_of_tilde d h e htilde hU
  let := second_normal_in_core d h g hK
  let := upper_elementary d h e htilde hU g hg hK hp a hi
  obtain ⟨σ,c,_⟩ := upper_action d h e htilde hU g hgn hg hK hL hp a hi
  have hjcore : j∈(NormalBranch.K D g.val).pCoreIn 2 :=
    fixed_local_core_le_pair_core d h e g hK hL a hi A hAL hA
      ⟨(ClosurePair.closure_reduction_of_tilde d h htilde).2.1 hjU,hjA⟩
  have hjsecond := fixed_pair_core_le_second d h e htilde hU g hgn hg hK hL hp a hi σ c A hAL hA ⟨hjcore,hjA⟩
  exact order_four_not_mem_second d h e g hgn hK hL a hi j hj hjsecond

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.CubicFixed
