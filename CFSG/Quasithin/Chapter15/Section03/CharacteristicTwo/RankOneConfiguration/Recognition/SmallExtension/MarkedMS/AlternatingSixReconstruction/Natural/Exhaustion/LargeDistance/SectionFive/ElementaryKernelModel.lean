module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeKernelLine
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeAlignmentModel
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Structure.ExceptionalLattice

/-!
# Elementary actors on the critical fixed hyperplane

For either six-letter cover, an elementary actor containing the critical
transposition has an aligned fixed-kernel commutator of dimension at most one
whenever the full displacement is not controlled by that commutator and the
critical line. Classify the elementary actor into a three-pair subgroup or the
exceptional subgroup. The former uses the existing two-cover calculations;
the latter uses its augmentation-core coordinate identity and an equivariant
surjection to either cover. The constant word is retained in the alignment.

This is the binary natural-cover calculation used in MS93 (3.3)(ii)(2) and
(5.7), printed pp.866--867 and 919. The literal endpoint application must
supply elementary abelianness and failure of full displacement control.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags CoreCrossing
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.ElementaryKernelModel
local notation "ρ" => coreRepresentation (Fin 6)

private def lineWord : C := pairWord 0 1 + pairWord 2 3

private theorem exceptional_certificate :
    ∀ (v : Full (Fin 6)) (j : Fin 8), (∑ i, v i)=0 → v 4=v 5 →
      ∃ a : ZMod 2, representation (Fin 6) (exceptionalWords j) v-v = a • lineWord.val := by
  decide +kernel

private theorem core_line (P : Subgroup S) (hP : P ≤ exceptional 6 (by decide)) :
    subspaceCommutator ρ (fixedSpace ρ (zpowers swap45)) P ≤
      Submodule.span (ZMod 2) {lineWord} := by
  apply Submodule.span_le.mpr
  rintro _ ⟨g,hg,v,hv,rfl⟩
  obtain ⟨j,rfl⟩ := (mem_exceptional_iff g).mp (hP hg)
  have hfix := (mem_fixedSpace_zpowers_iff _ _ _).mp hv
  have h45 : v.val 4=v.val 5 := congrArg (fun w : C => w.val 5) hfix
  obtain ⟨a,ha⟩ := exceptional_certificate v.val j v.property h45
  have he : ρ (exceptionalWords j) v-v=a • lineWord := Subtype.ext ha
  rw [he]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

private theorem cover_surjection
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (σ : Representation (ZMod 2) S Y)
    (hm : SixCover.IsNaturalOrCore σ (MonoidHom.id S)) :
    ∃ f : C →ₗ[ZMod 2] Y, Function.Surjective f ∧
      (∀ g v, f (ρ g v)=σ g (f v)) ∧ f (pairWord 4 5) ≠ 0 := by
  rcases hm with ⟨E,hE⟩ | ⟨E,hE⟩
  · let f := E.symm.toLinearMap.comp (coreToNatural (Fin 6))
    refine ⟨f,E.symm.surjective.comp coreToNatural_surjective,?_,?_⟩
    · intro g v
      apply E.injective
      simp only [f,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,
        hE,MonoidHom.id_apply,coreToNatural_equivariant]
    · intro hz
      have hh := congrArg E hz
      have hp := NaturalGeometry.pairVector_ne_zero (by decide : (4 : Fin 6) ≠ 5)
      apply hp
      have hpair : coreToNatural (Fin 6) (pairWord 4 5)=NaturalGeometry.pairVector 4 5 := rfl
      simpa only [hpair,f,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,
        map_zero] using hh
  · refine ⟨E.symm.toLinearMap,E.symm.surjective,?_,?_⟩
    · intro g v
      apply E.injective
      simp only [LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,hE,MonoidHom.id_apply]
    · intro hz
      have hh := congrArg E hz
      have hp : pairWord 4 5 ≠ 0 := by decide +kernel
      apply hp
      simpa only [LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,map_zero] using hh

private theorem mapped_line
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (σ : Representation (ZMod 2) S Y) (f : C →ₗ[ZMod 2] Y)
    (hf : Function.Surjective f) (he : ∀ g v, f (ρ g v)=σ g (f v))
    (hn : f (pairWord 4 5) ≠ 0) (P : Subgroup S)
    (hP : P ≤ exceptional 6 (by decide)) :
    Module.finrank (ZMod 2) (subspaceCommutator σ (fixedSpace σ (zpowers swap45)) P) ≤ 1 ∧
      subspaceCommutator σ (fixedSpace σ (zpowers swap45)) P ≤
        subspaceCommutator σ ⊤ (zpowers swap45) ⊔ fixedSpace σ ⊤ := by
  have hF : (fixedSpace ρ (zpowers swap45)).map f = fixedSpace σ (zpowers swap45) := by
    apply le_antisymm
    · rintro _ ⟨v,hv,rfl⟩
      apply (mem_fixedSpace_zpowers_iff _ _ _).mpr
      rw [←he,(mem_fixedSpace_zpowers_iff _ _ _).mp hv]
    · intro w hw
      obtain ⟨v,rfl⟩ := hf w
      refine ⟨v,?_,rfl⟩
      have hh : (v.val 4+v.val 5) • f (pairWord 4 5)=0 := by
        rw [←map_smul,←swap45_displacement,map_sub,he,
          (mem_fixedSpace_zpowers_iff _ _ _).mp hw,sub_self]
      have hz : v.val 4+v.val 5=0 := (smul_eq_zero.mp hh).resolve_right hn
      apply (mem_fixedSpace_zpowers_iff _ _ _).mpr
      apply sub_eq_zero.mp
      rw [swap45_displacement,hz,zero_smul]
  have hmap (I : Submodule (ZMod 2) C) (B : Subgroup S) :
      (subspaceCommutator ρ I B).map f = subspaceCommutator σ (I.map f) B := by
    have hh := subspaceCommutator_map_embedding σ ρ (MonoidHom.id S) f
      (fun g v => (he g v).symm) B I
    simpa only [map_id] using hh.symm
  have hK := Submodule.map_mono (f := f) (core_line P hP)
  rw [hmap,hF,Submodule.map_span,Set.image_singleton] at hK
  have hdim : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {f lineWord}) ≤ 1 := by
    simpa using (finrank_span_le_card (R := ZMod 2) ({f lineWord} : Set Y))
  refine ⟨(Submodule.finrank_mono hK).trans hdim,hK.trans ?_⟩
  apply Submodule.span_le.mpr
  rintro _ rfl
  have heq : lineWord=pairWord 4 5+oneWord := by decide +kernel
  rw [heq,map_add]
  apply Submodule.add_mem
  · apply Submodule.mem_sup_left
    have hm := Submodule.map_mono (f := f)
      (show Submodule.span (ZMod 2) {pairWord 4 5} ≤ subspaceCommutator ρ ⊤ (zpowers swap45) by
        rw [swap45_moved])
    rw [hmap,Submodule.map_top,LinearMap.range_eq_top.mpr hf] at hm
    exact hm ⟨_,Submodule.subset_span (Set.mem_singleton _),rfl⟩
  · apply Submodule.mem_sup_right
    intro g
    change σ g.val (f oneWord)=f oneWord
    rw [←he]
    rfl

private theorem exceptional_line
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (σ : Representation (ZMod 2) S Y)
    (hm : SixCover.IsNaturalOrCore σ (MonoidHom.id S))
    (u t : S) (P : Subgroup S)
    (hP : P ≤ (exceptional 6 (by decide)).map (MulAut.conj u).toMonoidHom)
    (ht : t ∈ (exceptional 6 (by decide)).map (MulAut.conj u).toMonoidHom)
    (hs : t.IsSwap) :
    Module.finrank (ZMod 2) (subspaceCommutator σ (fixedSpace σ (zpowers t)) P) ≤ 1 ∧
      subspaceCommutator σ (fixedSpace σ (zpowers t)) P ≤
        subspaceCommutator σ ⊤ (zpowers t) ⊔ fixedSpace σ ⊤ := by
  obtain ⟨a,ha,hat⟩ := ht
  have hsA : a.IsSwap := by
    have hc : IsConj a t := isConj_iff.mpr ⟨u,hat⟩
    exact Equiv.Perm.isSwap_iff_cycleType.mpr
      ((Equiv.Perm.isConj_iff_cycleType_eq.mp hc).trans (Equiv.Perm.isSwap_iff_cycleType.mp hs))
  have ha45 : a=swap45 := exceptional_transposition_unique ha (by
    obtain ⟨i,j,hij,rfl⟩ := hsA
    exact Equiv.Perm.card_support_swap hij)
  have htw : (MulAut.conj u) swap45=t := ha45 ▸ hat
  obtain ⟨f,hf,hfe,hfn⟩ := cover_surjection σ hm
  let c := (MulAut.conj u).toMonoidHom
  let P₀ := P.comap c
  have hmap : P₀.map c=P := map_comap_eq_self_of_surjective (MulAut.conj u).surjective P
  have hP₀ : P₀ ≤ exceptional 6 (by decide) := by
    apply (map_le_map_iff_of_injective (f := c) (MulAut.conj u).injective).mp
    rw [hmap]
    exact hP
  let τ := σ.comp c
  let f₀ := (σ u).comp f
  have hs₀ : Function.Surjective f₀ := by
    intro v
    obtain ⟨a,ha⟩ := hf (σ u⁻¹ v)
    refine ⟨a,?_⟩
    change σ u (f a)=v
    rw [ha,σ.self_inv_apply]
  have he₀ (g : S) (v : C) : f₀ (ρ g v)=τ g (f₀ v) := by
    change σ u (f (ρ g v))=σ (u*g*u⁻¹) (σ u (f v))
    rw [hfe]
    simp only [map_mul,Module.End.mul_apply,σ.inv_self_apply]
  have hn₀ : f₀ (pairWord 4 5) ≠ 0 := by
    intro hz
    have hh := congrArg (σ u⁻¹) hz
    apply hfn
    simpa only [f₀,LinearMap.comp_apply,σ.inv_self_apply,map_zero] using hh
  have hA : (zpowers swap45).map c=zpowers t := by
    rw [MonoidHom.map_zpowers]
    exact congrArg zpowers htw
  have hT : (⊤ : Subgroup S).map c=⊤ := map_top_of_surjective c (MulAut.conj u).surjective
  have hh := mapped_line τ f₀ hs₀ he₀ hn₀ P₀ hP₀
  have hK : subspaceCommutator τ (fixedSpace τ (zpowers swap45)) P₀ =
      subspaceCommutator σ (fixedSpace σ (zpowers t)) P := by
    simp only [τ,subspaceCommutator_comp_map,fixedSpace_comp_map,hA,hmap]
  rw [hK] at hh
  simpa only [τ,subspaceCommutator_comp_map,fixedSpace_comp_map,hA,hmap,hT] using hh

/-- For an elementary actor containing the critical transposition, failure of
full displacement control forces an aligned fixed-kernel line on either cover. -/
theorem small_aligned_of_failure
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (σ : Representation (ZMod 2) S Y)
    (hm : SixCover.IsNaturalOrCore σ (MonoidHom.id S))
    (t : S) (P : Subgroup S) (he : IsElementaryAbelian 2 P)
    (ht : t ∈ P) (hs : t.IsSwap)
    (hfail : ¬ subspaceCommutator σ ⊤ P ≤
      subspaceCommutator σ (fixedSpace σ (zpowers t)) P ⊔ subspaceCommutator σ ⊤ (zpowers t)) :
    Module.finrank (ZMod 2) (subspaceCommutator σ (fixedSpace σ (zpowers t)) P) ≤ 1 ∧
      subspaceCommutator σ (fixedSpace σ (zpowers t)) P ≤
        subspaceCommutator σ ⊤ (zpowers t) ⊔ fixedSpace σ ⊤ := by
  have hn : P ≠ ⊥ := by
    intro hp
    have ht1 : t=1 := by simpa only [hp,mem_bot] using ht
    obtain ⟨i,j,hij,he⟩ := hs
    have heval := congrArg (fun g : S => g i) (he.symm.trans ht1)
    simp only [Equiv.swap_apply_left,Equiv.Perm.one_apply] at heval
    exact hij heval.symm
  obtain ⟨B,hB,hBD | hBE,u,hu⟩ := exists_conjugate_le_D_or_exceptional ⟨hn,he⟩
  · have hP := hu ▸ map_mono (f := (MulAut.conj u).toMonoidHom) hBD
    have ht' := hP ht
    refine ⟨?_,?_⟩
    · by_contra! hlarge
      exact hfail (CubeKernelLine.model_comparison σ hm u t P hP ht' hs hlarge)
    · exact (CubeAlignmentModel.model_dichotomy σ hm u t P hP ht' hs).resolve_right hfail
  · have hP := hu ▸ map_mono (f := (MulAut.conj u).toMonoidHom) hBE
    exact exceptional_line σ hm u t P hP (hP ht) hs
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.ElementaryKernelModel
