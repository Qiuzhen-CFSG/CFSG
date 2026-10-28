module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceUpperStructure

/-!
# The literal A₅ action on the original upper section

Conjugation on S/V descends through the exact restricted actor K→A₅.
The original subgroup images of W=U_H∩S and W^g are complementary. The
U_H displacement lies in the W image and U_H fixes that image. These
statements retain the original quotient map and right conjugator and
supply the binary geometry needed by the source projective recognition.

Source: Aschbacher–Smith,G.2.4(6), printed pp.334–335, used in13.5.15.
-/

@[expose] public section
open Subgroup
open scoped Pointwise commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceUpperAction
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks
open SourceFiveModule SourceUpperStructure
open ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)

/-- The action descends to the exact A₅ quotient, with the original quotient map. -/
theorem upper_action (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬ IsMulCommutative D.UH) (g : D.L)
    (hg : g.val ∈ NormalBranch.K D g.val) (hK : NormalBranch.K D g.val ≤ D.L)
    (hL : D.L₁ ≤ NormalBranch.K D g.val) (hp : IsPPerfect 2 (NormalBranch.K D g.val))
    (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom) :
    let := module_normal_in_core d g hK
    let := upper_elementary d h e hseed hn hU g hg hK hL hp a hi
    ∃ (σ : Representation (ZMod 2) (alternatingGroup (Fin 5))
        (Additive ((NormalBranch.K D g.val).pCoreIn 2 ⧸
          D.V.subgroupOf ((NormalBranch.K D g.val).pCoreIn 2))))
      (c : Representation.BinaryConjugationSection (NormalBranch.K D g.val)
        ((NormalBranch.K D g.val).pCoreIn 2) D.V (σ.comp (restrictedActor d hK a hi))),
      ∀s:(NormalBranch.K D g.val).pCoreIn 2,(c.coordinates s).toAdd =
        Additive.ofMul (QuotientGroup.mk' (D.V.subgroupOf ((NormalBranch.K D g.val).pCoreIn 2)) s) := by
  let := module_normal_in_core d g hK
  let := upper_elementary d h e hseed hn hU g hg hK hL hp a hi
  have hk : (restrictedActor d hK a hi).ker =
      ((NormalBranch.K D g.val).pCoreIn 2).subgroupOf (NormalBranch.K D g.val) := by
    rw [restrictedActor_ker_eq_twoCore d hK a hi e]
    exact (comap_map_eq_self_of_injective (NormalBranch.K D g.val).subtype_injective _).symm
  exact Representation.BinaryConjugationSection.exists_canonical
    (NormalBranch.K D g.val) ((NormalBranch.K D g.val).pCoreIn 2) D.V
    (pCoreIn_le 2 _) (module_le_core d h hseed g hK hL a hi)
    (pair_normalizes_core g) (hK.trans (le_sup_left.trans d.normalizes_V))
    (restrictedActor d hK a hi) (restrictedActor_surjective d hK a hi) hk

theorem upper_root_bounds (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (g : D.L) (hK : NormalBranch.K D g.val ≤ D.L)
    (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (ρ : Representation (ZMod 2) (NormalBranch.K D g.val) E)
    (c : Representation.BinaryConjugationSection (NormalBranch.K D g.val)
      ((NormalBranch.K D g.val).pCoreIn 2) D.V ρ)
    (u : NormalBranch.K D g.val) (hu : u.val ∈ D.UH) :
    LinearMap.range (ρ u-1) ≤ c.imageSpace (D.UH⊓(NormalBranch.K D g.val).pCoreIn 2) ∧
    ∀v∈c.imageSpace (D.UH⊓(NormalBranch.K D g.val).pCoreIn 2),ρ u v=v := by
  have hUS : ⁅D.UH,(NormalBranch.K D g.val).pCoreIn 2⁆ ≤
      D.UH⊓(NormalBranch.K D g.val).pCoreIn 2 :=
    le_inf (le_normalizer_iff_commutator_le_left.mp
      (SourceCoreProduct.core_normalizes_closure d h e g hK a hi))
      (le_normalizer_iff_commutator_le_right.mp
        ((show D.UH≤NormalBranch.K D g.val from le_sup_left).trans (pair_normalizes_core g)))
  have hUW : ⁅D.UH,D.UH⊓(NormalBranch.K D g.val).pCoreIn 2⁆ ≤ D.V :=
    ((commutator_mono le_rfl inf_le_left).trans
      (derived_le_of_frattini_image_le h.g2_hypothesis.U_isPGroup h.frattini_UH_le_point)).trans
        (h.point_lt.le.trans h.plus_le)
  exact ⟨c.displacement_range_le_imageSpace_of_commutator_le D.UH _ hUS u hu,
    c.fixed_on_imageSpace_of_commutator_le D.UH _ hUW u hu⟩

include d in
theorem seed_join (h : D.Hypothesis) (g : D.L) (hg : g.val∉D.Gz) :
    D.Vplus ⊔ conjugate D.Vplus g.val = D.V := by
  let W := conjugate D.Vplus g.val
  have hcW : Nat.card W=8 :=
    (card_map_of_injective (MulAut.conj g.val⁻¹).injective).trans d.seed_card
  have hnV : D.V.map (MulAut.conj g.val⁻¹).toMonoidHom=D.V :=
    mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (D.V:Set G)).inv_mem (d.normalizes_V (mem_sup_left g.property)))
  have hWV : W≤D.V := by
    have hh := map_mono (f := (MulAut.conj g.val⁻¹).toMonoidHom) h.plus_le
    rwa [hnV] at hh
  have hJ : D.Vplus⊔W≤D.V := sup_le h.plus_le hWV
  have hne : D.Vplus≠D.Vplus⊔W := by
    intro he
    have hle : W≤D.Vplus := he ▸ le_sup_right
    have hEq : W=D.Vplus := eq_of_le_of_card_ge hle (by rw [hcW,d.seed_card])
    have hi : g.val⁻¹∈normalizer (D.Vplus:Set G) := mem_normalizer_iff_map_conj_eq.mpr hEq
    apply hg
    apply ReturningPlane.seed_normalizer_le_point d h g
    simpa only [inv_inv] using (normalizer (D.Vplus:Set G)).inv_mem hi
  have hlt : 8<Nat.card (D.Vplus⊔W:Subgroup G) := by
    rw [←d.seed_card]
    exact Set.ncard_lt_ncard (lt_of_le_of_ne
      (show (D.Vplus:Set G)⊆((D.Vplus⊔W:Subgroup G):Set G) from fun _ hx => mem_sup_left hx)
      (fun he => hne (SetLike.coe_injective he)))
  have hle : Nat.card (D.Vplus⊔W:Subgroup G)≤16 :=
    (Nat.card_le_card_of_injective (inclusion hJ) (inclusion_injective hJ)).trans_eq (ReturningPlane.module_card d)
  have hd := card_dvd_of_le (show D.Vplus≤D.Vplus⊔W from le_sup_left)
  rw [d.seed_card] at hd
  have hj : Nat.card (D.Vplus⊔W:Subgroup G)=16 := by
    obtain ⟨n,hn⟩ := hd
    omega
  exact eq_of_le_of_card_ge hJ (by rw [hj,ReturningPlane.module_card d])

theorem upper_marked_complement (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬ IsMulCommutative D.UH) (g : D.L) (hgn : g.val∉D.Gz)
    (hg : g.val ∈ NormalBranch.K D g.val) (hK : NormalBranch.K D g.val ≤ D.L)
    (hL : D.L₁ ≤ NormalBranch.K D g.val) (hp : IsPPerfect 2 (NormalBranch.K D g.val))
    (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (ρ : Representation (ZMod 2) (NormalBranch.K D g.val) E)
    (c : Representation.BinaryConjugationSection (NormalBranch.K D g.val)
      ((NormalBranch.K D g.val).pCoreIn 2) D.V ρ) :
    IsCompl (c.imageSpace (D.UH⊓(NormalBranch.K D g.val).pCoreIn 2))
      (c.imageSpace (conjugate (D.UH⊓(NormalBranch.K D g.val).pCoreIn 2) g.val)) ∧
    c.imageSpace (conjugate (D.UH⊓(NormalBranch.K D g.val).pCoreIn 2) g.val) =
      (c.imageSpace (D.UH⊓(NormalBranch.K D g.val).pCoreIn 2)).map
        (ρ (⟨g.val,hg⟩:NormalBranch.K D g.val)⁻¹) := by
  let S := (NormalBranch.K D g.val).pCoreIn 2
  let W := D.UH⊓S
  let X := conjugate W g.val
  have hVW : D.Vplus≤W := le_inf (le_conjugateSpanBy _ _)
    (h.plus_le.trans (module_le_core d h hseed g hK hL a hi))
  have hVgX : conjugate D.Vplus g.val≤X := map_mono hVW
  have hVV := seed_join d h g hgn
  have hprod : (D.V:Set G)=(D.Vplus:Set G)*(conjugate D.Vplus g.val:Set G) := by
    rw [←hVV]
    apply coe_mul_of_right_le_normalizer_left
    have hnorm : D.V≤normalizer (D.Vplus:Set G) := by
      let := h.elementary
      exact ((le_centralizer_iff_isMulCommutative.mpr (inferInstance : IsMulCommutative D.V)).trans
        (centralizer_le h.plus_le)).trans (Subgroup.centralizer_le_normalizer _)
    exact (le_sup_right.trans hVV.le).trans hnorm
  have hdis : Disjoint (c.imageSpace W) (c.imageSpace X) := by
    apply Submodule.disjoint_def.mpr
    intro v hv hv'
    obtain ⟨b,hb,hbv⟩ := (c.mem_imageSpace_iff _ _).mp hv
    obtain ⟨x,hx,hxv⟩ := (c.mem_imageSpace_iff _ _).mp hv'
    have he : b.val*x.val⁻¹∈D.V := by
      apply (c.coordinates_eq_one_iff (b*x⁻¹)).mp
      rw [map_mul,map_inv,Multiplicative.toAdd.injective (hbv.trans hxv.symm),mul_inv_cancel]
    change b.val*x.val⁻¹∈(D.V:Set G) at he
    rw [hprod] at he
    obtain ⟨v₀,hv₀,v₁,hv₁,heq⟩ := he
    change v₀*v₁=b.val*x.val⁻¹ at heq
    have heq' : v₀⁻¹*b.val=v₁*x.val := by
      calc
        _ = v₀⁻¹*((b.val*x.val⁻¹)*x.val) := by group
        _ = v₀⁻¹*((v₀*v₁)*x.val)  := by rw [←heq]
        _ = _ := by group
    have hw : v₀⁻¹*b.val∈W := W.mul_mem (W.inv_mem (hVW hv₀)) hb
    have hx' : v₀⁻¹*b.val∈X := by
      rw [heq']
      exact X.mul_mem (hVgX hv₁) hx
    have hker : v₀⁻¹*b.val∈D.V :=
      ((SourceSecondLayer.intersection_le_seed d h e hseed hn hU g hK hL).trans h.plus_le)
        ⟨hw.1,(map_mono (show W≤D.UH from inf_le_left)) hx'⟩
    have hbV : b.val∈D.V := by
      have hh := D.V.mul_mem (h.plus_le hv₀) hker
      simpa only [mul_inv_cancel_left] using hh
    exact hbv.symm.trans (show (c.coordinates b).toAdd=0 from
      congrArg Multiplicative.toAdd ((c.coordinates_eq_one_iff b).mpr hbV))
  refine ⟨⟨hdis,?_⟩,c.imageSpace_conjBy W inf_le_right (⟨g.val,hg⟩:NormalBranch.K D g.val)⁻¹⟩
  let f : Subgroup (Multiplicative E)≃oSubmodule (ZMod 2) E :=
    Subgroup.toAddSubgroup'.trans (AddSubgroup.toZModSubmodule 2)
  change Codisjoint (f ((W.subgroupOf S).map c.coordinates))
    (f ((X.subgroupOf S).map c.coordinates))
  rw [codisjoint_iff,←f.map_sup,←f.map_top]
  apply congrArg f
  apply codisjoint_iff.mp
  apply Subgroup.codisjoint_map c.onto
  have hcod (B : Subgroup G) (hb : B=W⊔X) : Codisjoint (W.subgroupOf B) (X.subgroupOf B) := by
    subst B
    exact codisjoint_subgroupOf_sup _ _
  exact hcod S (SourceCoreProduct.core_generated d h e hseed hn hU g hg hK hp a hi)

/-- The selected original pair supplies the quotient action and both markings. -/
theorem exists_original_upper_action (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬ IsMulCommutative D.UH) :
    ∃ (a : alternatingGroup (Fin 6)) (g : D.L)
      (_hgn : g.val∉D.Gz) (hg : g.val∈NormalBranch.K D g.val)
      (hK : NormalBranch.K D g.val≤D.L) (hL : D.L₁≤NormalBranch.K D g.val)
      (hp : IsPPerfect 2 (NormalBranch.K D g.val))
      (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
        FivePair.five.map (MulAut.conj a.val).toMonoidHom),
      let := module_normal_in_core d g hK
      let := upper_elementary d h e hseed hn hU g hg hK hL hp a hi
      ∃ (σ : Representation (ZMod 2) (alternatingGroup (Fin 5))
          (Additive ((NormalBranch.K D g.val).pCoreIn 2 ⧸
            D.V.subgroupOf ((NormalBranch.K D g.val).pCoreIn 2))))
        (c : Representation.BinaryConjugationSection (NormalBranch.K D g.val)
          ((NormalBranch.K D g.val).pCoreIn 2) D.V (σ.comp (restrictedActor d hK a hi))),
        (∀s:(NormalBranch.K D g.val).pCoreIn 2,(c.coordinates s).toAdd =
          Additive.ofMul (QuotientGroup.mk' (D.V.subgroupOf ((NormalBranch.K D g.val).pCoreIn 2)) s)) ∧
        IsCompl (c.imageSpace (D.UH⊓(NormalBranch.K D g.val).pCoreIn 2))
          (c.imageSpace (conjugate (D.UH⊓(NormalBranch.K D g.val).pCoreIn 2) g.val)) ∧
        c.imageSpace (conjugate (D.UH⊓(NormalBranch.K D g.val).pCoreIn 2) g.val) =
          (c.imageSpace (D.UH⊓(NormalBranch.K D g.val).pCoreIn 2)).map
            (σ ((restrictedActor d hK a hi) (⟨g.val,hg⟩:NormalBranch.K D g.val))⁻¹) := by
  obtain ⟨a,g,hgn,hg,hK,hL,hp,_,_,hi,_,_⟩ :=
    SourceCoreProduct.exists_original_core_pair d h e hseed hn hU
  refine ⟨a,g,hgn,hg,hK,hL,hp,hi,?_⟩
  let := module_normal_in_core d g hK
  let := upper_elementary d h e hseed hn hU g hg hK hL hp a hi
  obtain ⟨σ,c,hc⟩ := upper_action d h e hseed hn hU g hg hK hL hp a hi
  refine ⟨σ,c,hc,?_⟩
  have hm := upper_marked_complement d h e hseed hn hU g hgn hg hK hL hp a hi
    (σ.comp (restrictedActor d hK a hi)) c
  simpa only [MonoidHom.comp_apply,map_inv] using hm

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceUpperAction
end
