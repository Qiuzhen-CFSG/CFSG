module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.CubicCount
public import Theory.SpecificGroups.SL2.CubicCopiesLength
/-!
# The even chief count in the original ordinary A₆ branch

The cubic actor has fixed length one on the sixteen-element source module:
it fixes the original point and survives the two-group action kernel.
The second layer has the same length, while its actual upper quotient is a
sum of natural SL₂(4) planes, each of length two. The literal A₄ residual
quotient adds one. Hence every complete original L₁ chief series has an
even noncentral two-count. No fixed-Sylow G.2 setup is imposed on the pair.
Source: Aschbacher–Smith13.5.22(2), printed p.924.
-/
public section
open Subgroup NoncentralChiefRefinement NoncentralChiefRefinement.CubicComparison
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.CubicParity
open Section08.SourceCompletion NormalBranch
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks SourceFiveModule SourceUpperStructure
open ChapterG.Section02.Setup
open ChapterG.Section02.AlternatingFive.Recognition.ProjectiveGeometry
open ClosureLayers ClosureUpper
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
include d

/-- Cauchy's theorem lifts a cubic actor from the original residual quotient. -/
theorem exists_cubic (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6)) :
    ∃A:Subgroup G,A≤D.L₁ ∧ Nat.card A=3 := by
  have hd : 3∣Nat.card D.L₁ :=
    (SourceStar.original_residual_quotient_card d h e) ▸ card_quotient_dvd_card (pCore 2 D.L₁)
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G:=D.L₁) 3 hd
  refine ⟨(zpowers a).map D.L₁.subtype,map_subtype_le _,?_⟩
  rw [card_map_of_injective D.L₁.subtype_injective,Nat.card_zpowers,ha]

theorem module_length_one (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
    (A : Subgroup G) (hAL : A≤D.L₁) (hA : Nat.card A=3) :
    conjugationCubicLength A D.V=1 := by
  have hLL : D.L₁≤D.L := (map_subtype_le _).trans inf_le_left
  have hAV : A≤normalizer (D.V:Set G) := hAL.trans (hLL.trans (le_sup_left.trans d.normalizes_V))
  let := conjMulDistribMulActionOfLeNormalizer A D.V hAV
  let F := FixedPoints.subgroup A D.V
  have hAP : A≤centralizer (D.V₁:Set G) :=
    hAL.trans ((map_subtype_le _).trans inf_le_right)
  have hPF : D.V₁.subgroupOf D.V≤F := by
    intro v hv a
    apply Subtype.ext
    change a.val*v.val*a.val⁻¹=v.val
    rw [←hAP a.property v.val hv,mul_inv_cancel_right]
  have hcard : 2≤Nat.card F := by
    have hh := Nat.card_le_card_of_injective (inclusion hPF) (inclusion_injective hPF)
    rw [Nat.card_congr (subgroupOfEquivOfLe (h.point_lt.le.trans h.plus_le)).toEquiv,h.point_card] at hh
    exact hh
  have h3 : IsPGroup 3 A := IsPGroup.of_card (n:=1) hA
  have hneq : F≠⊤ := by
    intro he
    have hAC : A≤centralizer (D.V:Set G) := by
      intro a ha v hv
      have hh : (⟨v,hv⟩:D.V)∈F := he ▸ mem_top _
      have hf := congrArg Subtype.val (hh ⟨a,ha⟩)
      change a*v*a⁻¹=v at hf
      exact (mul_inv_eq_iff_eq_mul.mp hf).symm
    have hAcore := (le_inf (hAL.trans hLL) hAC).trans (local_centralizer_le_core d e)
    have hd := IsPGroup.disjoint_of_coprime h3 (isPGroup_pCoreIn 2 D.L) (by decide)
    have hb : A=⊥ := le_bot_iff.mp (fun x hx => hd.eq_bot ▸ ⟨hx,hAcore hx⟩)
    rw [hb,card_bot] at hA
    omega
  have hc := F.index_mul_card
  rw [ReturningPlane.module_card d] at hc
  have hidx := FixedPoints.index_eq_four_pow_cubicLength h3 h.elementary.isPGroup
  have hn := F.one_lt_index_of_ne_top hneq
  have hbound : F.index<16 := by nlinarith
  have hlen : FixedPoints.cubicLength A D.V<2 := by
    by_contra hh
    have hp := Nat.pow_le_pow_right (by decide : 1≤4) (show 2≤FixedPoints.cubicLength A D.V by omega)
    rw [←hidx] at hp
    change 16≤F.index at hp
    omega
  have hpos : FixedPoints.cubicLength A D.V≠0 := by
    intro hz
    rw [hz,pow_zero] at hidx
    change F.index=1 at hidx
    omega
  rw [conjugationCubicLength_eq A D.V hAV]
  omega

theorem second_length_one (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
    (g : D.L) (hK : NormalBranch.K D g.val≤D.L) (hL : D.L₁≤NormalBranch.K D g.val)
    (A : Subgroup G) (hAL : A≤D.L₁) (hA : Nat.card A=3)
    (hp : IsElementaryAbelian 2 (second D g.val)) :
    conjugationCubicLength A (second D g.val)=1 := by
  have hVK := hAL.trans hL
  have hnV : NormalBranch.K D g.val≤normalizer (D.V:Set G) :=
    hK.trans (le_sup_left.trans d.normalizes_V)
  have hnS : NormalBranch.K D g.val≤normalizer (second D g.val:Set G) := second_normalized d h g hK
  let := hp
  have hSV : second D g.val≤normalizer (D.V:Set G) :=
    ((le_centralizer_iff_isMulCommutative.mpr (inferInstance : IsMulCommutative (second D g.val))).trans
      (centralizer_le (show D.V≤second D g.val from le_sup_left))).trans
        (Subgroup.centralizer_le_normalizer _)
  let : (D.V.subgroupOf (second D g.val)).Normal :=
    (normal_subgroupOf_iff_le_normalizer (show D.V≤second D g.val from le_sup_left)).mpr hSV
  have he := length_eq_of_commutator_le A (second D g.val) D.V
    (IsPGroup.of_card (n:=1) hA) hp.isPGroup le_sup_left (hVK.trans hnS) (hVK.trans hnV)
    ((commutator_mono le_rfl hVK).trans (second_commutator d h g hK))
  rw [←he]
  exact module_length_one d h e A hAL hA

theorem upper_length_even (h : D.Hypothesis)
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
    ∃r:ℕ,sectionCubicLength A (second D g.val) ((NormalBranch.K D g.val).pCoreIn 2)=2*r := by
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
  have hlen := Representation.BinaryFixedPoints.sl2_four_cubicLength_of_two_kernel
    σ f hA hker m field_card r q heq
  let := c.kernel_normal
  have hnS := hAK.trans (pair_normalizes_core g)
  have hnN := hAK.trans (second_normalized d h g hK)
  let := quotientConjugationAction A ((NormalBranch.K D g.val).pCoreIn 2)
    (second D g.val) hnS hnN
  let := Representation.BinaryFixedPoints.action (σ.comp f)
  refine ⟨r,?_⟩
  rw [sectionCubicLength_eq_quotient_of_twoGroup A ((NormalBranch.K D g.val).pCoreIn 2)
    (second D g.val) (IsPGroup.of_card (n:=1) hA) (isPGroup_pCoreIn 2 _) c.kernel_le hnS hnN]
  apply Eq.trans (FixedPoints.cubicLength_eq_of_equivariant c.quotientEquiv ?_) hlen
  intro x v
  obtain ⟨s,rfl⟩ := QuotientGroup.mk'_surjective _ v
  apply Multiplicative.toAdd.injective
  exact c.equivariant (inclusion hAK x) s

/-- The original L₁ chief series has an even number of noncentral two-factors.
The same actual cubic actor is retained on V, the second layer and its upper quotient. -/
theorem count_even (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
    (htilde : D.tilde D.UH=⁅D.tilde D.UH,D.tilde D.L₁⁆)
    (hU : ¬ IsMulCommutative D.UH)
    (A : Subgroup G) (hAL : A≤D.L₁) (hA : Nat.card A=3)
    (t : ChiefSeries D.L₁) (h0 : t.head=⊥) (h1 : t.last=⊤) :
    ∃r:ℕ,t.noncentralTwoCount=2*r+2 := by
  obtain ⟨a,g,hgn,hg,hK,hL,hp,_,_,hi⟩ := ClosurePair.exists_source_pair_of_tilde d h e htilde hU
  let := second_normal_in_core d h g hK
  let := upper_elementary d h e htilde hU g hg hK hp a hi
  obtain ⟨σ,c,_⟩ := upper_action d h e htilde hU g hgn hg hK hL hp a hi
  obtain ⟨r,hr⟩ := upper_length_even d h e htilde hU g hgn hg hK hL hp a hi
    (E := Additive ((NormalBranch.K D g.val).pCoreIn 2 ⧸
      (second D g.val).subgroupOf ((NormalBranch.K D g.val).pCoreIn 2))) σ c A hAL hA
  have hsecond := second_length_one d h e g hK hL A hAL hA (second_elementary d h e g hgn hK hL a hi)
  have hcount := CubicCount.count_eq_core_length_add_one d h e g hK hL a hi A hAL hA t h0 h1
  have hmono := conjugationCubicLength_mono A (second_le_core d h g hgn hK hL a hi)
  unfold sectionCubicLength at hr
  refine ⟨r,?_⟩
  omega

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.CubicParity
