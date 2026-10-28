module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.FixedRoot
public import Theory.SpecificGroups.SymplecticFour.SourceFusionOrder.OuterConjugacy

/-!
# Original outer-involution conjugacy and centralizer placement

Over field order four the native flag involutions are conjugate through the
native Borel. Pull that explicit conjugator back through the same whole
pure-middle equivalence. Faithfulness of the original full-middle lift
then proves conjugacy in the original group, in either orientation.

The previously proved root-to-outer fusion now puts every original outer
involution in an original root class. Conjugating the full ambient root
centralizer bound places its entire centralizer in the corresponding
conjugate full normalizer. This supplies the actual ambient placement for
the fixed-endpoint quotient argument, without recognizing a completion.

Source: Aschbacher--Smith F.4.37, the Sp4(4) paragraph on printed p.293
of refs/quasithin.pdf, applied to 5.3.1--3, pp.658--659. The fixed-endpoint
A4/V4 quotient obstruction, S=T at q=4, and the three-class same-extension
order comparison remain required.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem middle_conjugator
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hq : Nat.card F=4)
    {C N : Subgroup G} (hCN : C≤N) (e : C ≃* borel (F := F))
    (σ : N →* SourceNormalizerExtension.flagAutomorphisms F)
    (hσ : Function.Injective σ)
    (hag : ∀ c : C, (σ (inclusion hCN c)).val=MulAut.conj (e c).val)
    (f t : N) (hf : orderOf f=2) (ht : orderOf t=2)
    (hfo : (σ f).val ∉ MulAut.innerSubgroup (Sp F))
    (hto : (σ t).val ∉ MulAut.innerSubgroup (Sp F)) :
    ∃ c : C, c.val*f.val*c.val⁻¹=t.val := by
  have hfo' : orderOf (σ f).val=2 := by
    rw [Subgroup.orderOf_coe,orderOf_injective σ hσ,hf]
  have hto' : orderOf (σ t).val=2 := by
    rw [Subgroup.orderOf_coe,orderOf_injective σ hσ,ht]
  obtain ⟨b,hb⟩ := SourceFusionOrder.outer_flag_involutions_borel_conjugate hq
    (σ f).val (σ t).val hfo' hto' (σ f).property (σ t).property hfo hto
  let c := e.symm b
  have hh : inclusion hCN c*f*(inclusion hCN c)⁻¹=t := by
    apply hσ
    apply Subtype.ext
    simp only [map_mul,map_inv,Subgroup.coe_mul,Subgroup.coe_inv]
    rw [hag]
    simpa only [c,e.apply_symm_apply] using hb
  exact ⟨c,congrArg Subtype.val hh⟩

variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
include d h hH hp hm hF he



/-- Outer involutions of the original Sylow are conjugate by an element
of the original whole pure Borel, in either amalgam orientation. -/
theorem Preparation.symplectic_outer_involutions_borel_conjugate
    (f t : T) (hf : orderOf f=2) (ht : orderOf t=2)
    (hfo : f.val ∉ sourceS L H) (hto : t.val ∉ sourceS L H) :
    ∃ c : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
      ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
      c.val*f.val*c.val⁻¹=t.val := by
  have hst : sourceS L H≠(T : Subgroup G) := fun hh => hfo (hh.symm ▸ f.property)
  have hq := (d.symplectic_proper_inner_sylow_field_four h hH hp F hm hF he hst).2.2.1
  let N := normalizer (L : Set G) ⊓ normalizer (residual H : Set G)
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  let C := P 0 ⊓ P 1
  have hTN : (T : Subgroup G)≤N :=
    le_inf h.sylow_normalizes (hH.1.1.2.trans (le_normalizer_residual H))
  have hout (x : T) (hx : x.val ∉ sourceS L H) : x.val ∉ C := by
    intro hxc
    have hFC := d.hypothesisF11 h hH.1.1.2
    have hs : Chapter1.IsSylowIn 2 (sourceS L H) C := by
      change Chapter1.IsSylowIn 2 (sourceS L H) (P 0 ⊓ P 1)
      rw [show P 0 ⊓ P 1=ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) from
        ChapterF.Source.lemma_F_1_3_6 hFC]
      exact hFC.sylow_commonBorel
    obtain ⟨R,hR⟩ := hs
    have hRT : (R : Subgroup C)≤(T : Subgroup G).subgroupOf C := by
      intro y hy
      exact sourceS_le_sylow h.sylow_normalizes hH.1.1.2 (hR ▸ mem_map_of_mem C.subtype hy)
    have hTR : (T : Subgroup G).subgroupOf C=R :=
      R.is_maximal' (T.isPGroup'.comap_subtype (K := C)) hRT
    apply hx
    apply hR ▸ mem_map_of_mem C.subtype (x := (⟨x.val,hxc⟩ : C))
    rw [←hTR]
    exact x.property
  let fN : N := inclusion hTN f
  let tN : N := inclusion hTN t
  have hfN : orderOf fN=2 := (orderOf_injective (inclusion hTN)
    (inclusion_injective hTN) f).trans hf
  have htN : orderOf tN=2 := (orderOf_injective (inclusion hTN)
    (inclusion_injective hTN) t).trans ht
  obtain ⟨_,hlift⟩ := d.symplectic_native_middle_lift h hH hp F hm hF he
  rcases hlift with ⟨a,σ,hσ,hact,_,hinner⟩ | ⟨a,σ,hσ,hact,_,hinner⟩
  · apply middle_conjugator hq a.middle_le a.comparison.middle σ hσ _ fN tN hfN htN
      (fun hh => hout f hfo ((hinner fN).mp hh))
      (fun hh => hout t hto ((hinner tN).mp hh))
    intro c
    exact congrArg Subtype.val (SourceNormalizerExtension.restriction_injective
      ((DFunLike.congr_fun hact _).trans (a.native_inner_action c)))
  · apply middle_conjugator hq a.middle_le a.comparison.middle σ hσ _ fN tN hfN htN
      (fun hh => hout f hfo ((hinner fN).mp hh))
      (fun hh => hout t hto ((hinner tN).mp hh))
    intro c
    exact congrArg Subtype.val (SourceNormalizerExtension.reverseRestriction_injective
      ((DFunLike.congr_fun hact _).trans (a.native_inner_action_reverse c)))

/-- Every original outer involution is fused to an original root
involution. The source root and actual ambient conjugator are retained. -/
theorem Preparation.symplectic_outer_involution_root_conjugate
    (f : T) (hf : orderOf f=2) (hfo : f.val ∉ sourceS L H) :
    ∃ i : Fin 2, ∃ z : G, orderOf z=2 ∧
      z ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype ∧
      ∃ g : G, g*z*g⁻¹=f.val := by
  have hst : sourceS L H≠(T : Subgroup G) := fun hh => hfo (hh.symm ▸ f.property)
  obtain ⟨i,z,hz,hzR,t,ht,hto,hzt⟩ :=
    d.symplectic_proper_inner_sylow_outer_root_fusion h hH hp F hm hF he hst
  obtain ⟨c,hc⟩ := d.symplectic_outer_involutions_borel_conjugate h hH hp F hm hF he
    t f ht hf hto hfo
  obtain ⟨g,hg⟩ := isConj_iff.mp hzt
  refine ⟨i,z,hz,hzR,c.val*g,?_⟩
  calc
    (c.val*g)*z*(c.val*g)⁻¹ = c.val*(g*z*g⁻¹)*c.val⁻¹ := by group
    _ = f.val := by rw [hg,hc]

/-- The full ambient centralizer of every outer involution lies in a
conjugate of an original full root normalizer. This supplies the ambient
placement used by the fixed-endpoint quotient argument in F.4.37. -/
theorem Preparation.symplectic_outer_centralizer_le_conjugate_normalizer
    (f : T) (hf : orderOf f=2) (hfo : f.val ∉ sourceS L H) :
    ∃ i : Fin 2, ∃ z : G, orderOf z=2 ∧
      z ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype ∧
      ∃ g : G, g*z*g⁻¹=f.val ∧
        centralizer ({f.val} : Set G) ≤
          (normalizer (![L,residual H] i : Set G)).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨i,z,hz,hzR,g,hg⟩ := d.symplectic_outer_involution_root_conjugate h hH hp F hm hF he f hf hfo
  have hb := d.symplectic_central_involution_centralizers h hH hp F hm hF he i z hzR hz
  refine ⟨i,z,hz,hzR,g,hg,?_⟩
  intro x hx
  let a := MulAut.conj g
  have ha : a z=f.val := hg
  have hxc : a.symm x ∈ centralizer ({z} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    apply a.injective
    simpa only [map_mul,a.apply_symm_apply,ha] using mem_centralizer_singleton_iff.mp hx
  exact ⟨a.symm x,hb hxc,a.apply_symm_apply x⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
