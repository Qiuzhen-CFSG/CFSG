module
public import CFSG.Quasithin.Chapter13.Section07.FixedLayerSource.NaturalLift

/-!
# The full quotient actor in the natural fixed-layer branch

The faithful plus module is a proper nonzero quotient of the doubled natural
component module. Its kernel and quotient are each three-dimensional. Thus
H/O₂(H) embeds into GL₃(2), while its selected component already has order168,
so that component is the entire quotient actor. The source application keeps
the original opposite conjugator and both canonical quotient actions.

Source: Aschbacher–Smith13.7.16(2), printed p.944.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section07
open ChapterB.QuasisimpleSource
variable {A X Y : Type*} [Group A] [Finite A]
 [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
 [AddCommGroup Y] [Module (ZMod 2) Y] [FiniteDimensional (ZMod 2) Y]

private theorem full_actor_of_faithful_proper_double_quotient
    (τ : Representation (ZMod 2) A X) (σ : Representation (ZMod 2) A Y)
    (hf : Function.Injective σ) (J : Subgroup A)
    (a : ActionEquiv (τ.comp J.subtype) (repeated (linearNatural BinaryField.two 3) 2))
    (q : τ.IntertwiningMap σ) (hq : Function.Surjective q)
    (hker : q.toLinearMap.ker ≠ ⊥) [Nontrivial Y] : J = ⊤ := by
  let qJ : Representation.IntertwiningMap (τ.comp J.subtype) (σ.comp J.subtype) := { q with isIntertwining' k := q.isIntertwining' k.val }
  let N := qJ.ker
  have hn : N ≠ ⊥ := fun he => hker (congrArg Subrepresentation.toSubmodule he)
  have hp : N ≠ ⊤ := by
    intro ht
    obtain ⟨y,hy⟩ := exists_ne (0 : Y)
    obtain ⟨x,hx⟩ := hq y
    have hm : x ∈ N.toSubmodule := by rw [ht]; trivial
    exact hy (hx.symm.trans hm)
  obtain ⟨e⟩ := repeated_double_proper_submodule_equiv (τ.comp J.subtype)
    BinaryField.two (by decide) a N hn hp
  have hkdim : Module.finrank (ZMod 2) q.toLinearMap.ker = 3 :=
    e.toLinearEquiv.finrank_eq.trans (Module.finrank_fin_fun (ZMod 2))
  have hxdim : Module.finrank (ZMod 2) X = 6 := by
    have hh := a.linearEquiv.finrank_eq
    change Module.finrank (ZMod 2) X = Module.finrank (ZMod 2) (Fin 2 → Fin 3 → ZMod 2) at hh
    simpa [Module.finrank_pi_fintype, Module.finrank_fin_fun] using hh
  have hydim : Module.finrank (ZMod 2) Y = 3 := by
    have hh := q.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hq,finrank_top,hkdim,hxdim] at hh
    omega
  let μ := σ.asGroupHom
  have hμ : Function.Injective μ := by
    intro x y he
    apply hf
    exact congrArg (fun f : LinearMap.GeneralLinearGroup (ZMod 2) Y =>
      (f : Module.End (ZMod 2) Y)) he
  let basis := Module.finBasisOfFinrankEq (ZMod 2) Y hydim
  let b : Matrix.PSL3Two.SL ≃* LinearMap.GeneralLinearGroup (ZMod 2) Y :=
    Matrix.PSL3Two.equivGL.trans (Matrix.GeneralLinearGroup.toLin' basis)
  have hc : Nat.card A ≤ 168 := by
    have hd := Subgroup.card_dvd_of_injective μ hμ
    have hb := Nat.card_congr b.toEquiv.symm
    rw [hb,Matrix.PSL3Two.card_SL] at hd
    exact Nat.le_of_dvd (by decide) hd
  have hj : Nat.card J = 168 := (Nat.card_congr a.groupEquiv.toEquiv).trans Matrix.PSL3Two.card_SL
  apply eq_of_le_of_card_ge le_top
  rwa [card_top,hj]
end CFSG.Quasithin.Chapter13.Section07

namespace CFSG.Quasithin.Chapter13.Section07
open ChapterB.QuasisimpleSource
variable {G X Y : Type*} [Group G] [Finite G]
 [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
 [AddCommGroup Y] [Module (ZMod 2) Y] [FiniteDimensional (ZMod 2) Y]
 {F : ChapterF.Section09.Setup G}

theorem component_eq_top_of_double_and_faithful_plus
    (h : F.Hypothesis)
    (ρ : Representation (ZMod 2) (F.H ⧸ pCore 2 F.H) X)
    (c : BinaryConjugationSection F.H F.UH F.V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 F.H))))
    (σ : Representation (ZMod 2) (F.H ⧸ pCore 2 F.H) Y)
    (s : BinaryConjugationSection F.H F.UH (PlusAction.fixedLayer F)
      (σ.comp (QuotientGroup.mk' (pCore 2 F.H))))
    (hf : Function.Injective σ)
    (K : Subgroup F.H) (hKC : K.IsCComponent)
    (hm : ⁅PlusAction.fixedLayer F,K.map F.H.subtype⁆ ≠ ⊥)
    (hplus : subspaceCommutator σ ⊤ (K.map (QuotientGroup.mk' (pCore 2 F.H))) = ⊤)
    [Nontrivial Y]
    (hsI : (⊤ : Subgroup (F.H ⧸ pCore 2 F.H)) ≤ subspaceStabilizer ρ
      (subspaceCommutator ρ ⊤ (K.map (QuotientGroup.mk' (pCore 2 F.H)))))
    (a : ActionEquiv ((wholeSubspaceAction ρ
      (subspaceCommutator ρ ⊤ (K.map (QuotientGroup.mk' (pCore 2 F.H)))) hsI).comp
      (K.map (QuotientGroup.mk' (pCore 2 F.H))).subtype)
      (repeated (linearNatural BinaryField.two 3) 2)) :
    K.map (QuotientGroup.mk' (pCore 2 F.H)) = ⊤ := by
  let π := QuotientGroup.mk' (pCore 2 F.H)
  let J := K.map π
  let I := subspaceCommutator ρ ⊤ J
  let τ := wholeSubspaceAction ρ I hsI
  obtain ⟨p,hp,_,hpker⟩ := BinaryConjugationSection.exists_projection
    F.H F.H F.UH F.V₁ (PlusAction.fixedLayer F) le_rfl (PlusAction.point_le_fixedLayer h)
    π π (QuotientGroup.mk'_surjective _) (MonoidHom.id _) (by intro k; rfl) ρ σ c s
  let q : τ.IntertwiningMap σ :=
    (p.toLinearMap.comp I.subtype).intertwiningMap_of_isIntertwiningMap _ _
      (by intro k v; exact LinearMap.congr_fun (p.isIntertwining' k) v.val)
  have hq : Function.Surjective q := by
    have hh := map_moved_of_surjective_intertwining ρ σ J p.toLinearMap hp
      (fun k v => LinearMap.congr_fun (p.isIntertwining' k) v)
    rw [hplus] at hh
    intro y
    obtain ⟨x,hx,he⟩ := hh.symm ▸ (Submodule.mem_top (x := y))
    exact ⟨⟨x,hx⟩,he⟩
  let Z := c.imageSpace (PlusAction.fixedLayer F)
  have hz : Z ≤ p.toLinearMap.ker := hpker.symm.le
  have hM : subspaceCommutator ρ Z J ≤ I := subspaceCommutator_mono_left ρ le_top J
  have hMker : subspaceCommutator ρ Z J ≤ p.toLinearMap.ker := by
    apply (subspaceCommutator_mono_left ρ hz J).trans
    apply subspaceCommutator_le_of_invariant ρ
    apply le_subspaceStabilizer
    intro k hk v hv
    change p (ρ k v) = 0
    change p v = 0 at hv
    rw [show p (ρ k v) = σ k (p v) from LinearMap.congr_fun (p.isIntertwining' k) v,hv,map_zero]
  have hkn : q.toLinearMap.ker ≠ ⊥ := by
    intro hb
    have hzM : subspaceCommutator ρ Z J = ⊥ := by
      apply bot_unique
      intro v hv
      have he : (⟨v,hM hv⟩ : I) ∈ q.toLinearMap.ker := hMker hv
      rw [hb] at he
      exact congrArg Subtype.val (show (⟨v,hM hv⟩ : I) = 0 from he)
    exact component_fixed_layer_image_not_fixed h ρ c K hKC hm
      ((subspaceCommutator_eq_bot_iff ρ Z J).mp hzM)
  exact full_actor_of_faithful_proper_double_quotient τ σ hf J a q hq hkn
end CFSG.Quasithin.Chapter13.Section07

namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup ChapterB.QuasisimpleSource
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d
theorem source_fixed_layer_component_eq_top
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1)
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W)
    (s : BinaryConjugationSection H (Section08.Source.UH H V₃)
      ((Section08.Source.UH H V₃) ⊓ centralizer (H.pCoreIn 2 : Set G))
      (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (B : Subgroup (H ⧸ pCore 2 H)) (hB : IsMinimalBestOffender σ B)
    (hBA : B ≤ ((conjugate (Section08.Source.VH H V) (g : G) ⊓
      (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2).subgroupOf H).map
        (QuotientGroup.mk' (pCore 2 H)))
    (K : Subgroup H) (hKC : K.IsCComponent) (hK : IsComponent (H ⧸ pCore 2 H)
      (K.map (QuotientGroup.mk' (pCore 2 H))))
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) = H.pCoreIn 2)
    (hcomm : ⁅K.map (QuotientGroup.mk' (pCore 2 H)),B⁆ = K.map (QuotientGroup.mk' (pCore 2 H)))
    (hm : ⁅PlusAction.fixedLayer (ConjugateIntersections.sourceSetup T L V V₃ V₁ H),
      K.map H.subtype⁆ ≠ ⊥)
    (hl : ClassicalGroup.IsPSL (K.map (QuotientGroup.mk' (pCore 2 H))) 3 2) :
    K.map (QuotientGroup.mk' (pCore 2 H)) = ⊤ := by
  obtain ⟨hE,ρ,c,_,hsI,⟨a⟩⟩ := source_tilde_component_doubleThree_of_fixed_layer_movement
    d h hU hV hne g hs hout σ s B hB hBA K hKC hK hk hcomm hm hl
  let := hE
  have hi := (source_plus_component_irrPlus_and_actor d h hU hV hne g hs hout
    σ s B hB hBA K hK hk hcomm).1
  have hwhole := source_plus_component_whole d h hU hV hne g hs hout
    σ s B hB hBA K hKC hK hk hcomm
  have hnt : (⊤ : Submodule (ZMod 2) W) ≠ ⊥ := hwhole ▸ hi.ne_bot σ
  let : Nontrivial (⊤ : Submodule (ZMod 2) W) := Submodule.nontrivial_iff_ne_bot.mpr hnt
  let : Nontrivial W := Function.Injective.nontrivial (⊤ : Submodule (ZMod 2) W).subtype_injective
  exact component_eq_top_of_double_and_faithful_plus h ρ c σ s
    (source_plus_faithful_of_kernel_eq σ s hk) K hKC hm hwhole hsI a
end CFSG.Quasithin.Chapter13.Section07
