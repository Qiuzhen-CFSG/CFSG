module
public import CFSG.Quasithin.Chapter13.Section07.ComponentWholeSource
public import CFSG.Quasithin.Chapter13.Section07.TildeOffenders
public import Theory.Representation.BinaryConjugationSection.Projection
public import Theory.Representation.BinaryConjugationSection.FixedImage
public import Theory.Representation.BinaryOffender.TwoNoncentralLayers
public import Theory.Representation.BinaryOffender.Restriction
public import Theory.GroupTheory.Commutator.SimpleSubnormal

/-!
# The original two-layer FF extraction in13.7.16

Suppose the selected perfect component moves U₀. Its movement cannot
vanish in U_H/V₁: vanishing would put the commutator in the H-central
point, and perfectness would make it trivial. The natural projection onto
U_H/U₀ therefore has both a noncentral kernel and a noncentral quotient.
The component-moved tilde module is faithful and is not Irr⁺.

The final source theorem retains the chosen conjugator and constructs the
canonical U_H/V₁ action. An actual best offender inside U_H^g restricts
to an FF* offender on the component-moved module. This proves the two-layer
and offender-extraction step of13.7.16(2); the subsequent doubled-natural
classification and original13.5.2(3) marking are separate source inputs.
Source: Aschbacher–Smith13.7.16, printed p.944.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory

namespace CFSG.Quasithin.Chapter13.Section07
open ChapterF.Section09.Setup ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

theorem component_fixed_layer_image_not_fixed
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (D.H ⧸ pCore 2 D.H) W)
    (c : BinaryConjugationSection D.H D.UH D.V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 D.H))))
    (K : Subgroup D.H) (hK : K.IsCComponent)
    (hm : ⁅PlusAction.fixedLayer D,K.map D.H.subtype⁆ ≠ ⊥) :
    ¬ c.imageSpace (PlusAction.fixedLayer D) ≤
      fixedSpace ρ (K.map (QuotientGroup.mk' (pCore 2 D.H))) := by
  intro hfixed
  let π := QuotientGroup.mk' (pCore 2 D.H)
  have hf : c.imageSpace (PlusAction.fixedLayer D) ≤
      fixedSpace (ρ.comp π) ((K.map D.H.subtype).subgroupOf D.H) := by
    intro v hv k
    obtain ⟨k',hk',he⟩ := k.property
    have he' : k' = k.val := Subtype.ext he
    change ρ (π k.val) v = v
    exact hfixed hv ⟨π k.val,by rw [←he']; exact mem_map_of_mem π hk'⟩
  have hc : ⁅PlusAction.fixedLayer D,K.map D.H.subtype⁆ ≤ D.V₁ := by
    rw [commutator_comm]
    exact c.commutator_le_of_imageSpace_fixed (K.map D.H.subtype) (PlusAction.fixedLayer D)
      (by simpa using map_le_range D.H.subtype K) inf_le_left hf
  let := hK.perfect
  let : Group.IsPerfect (K.map D.H.subtype) := Group.IsPerfect.map D.H.subtype
  have hKH : K.map D.H.subtype ≤ D.H := by simpa using map_le_range D.H.subtype K
  apply hm
  apply commutator_eq_bot_of_iterated_eq_bot
  apply le_bot_iff.mp
  exact (commutator_mono hc le_rfl).trans
    (commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp (hKH.trans h.H_centralizes))).le

theorem component_tilde_not_irrPlus_of_fixed_layer_movement
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    {W W₀ : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup W₀] [Module (ZMod 2) W₀]
    (ρ : Representation (ZMod 2) (D.H ⧸ pCore 2 D.H) W)
    (c : BinaryConjugationSection D.H D.UH D.V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 D.H))))
    (σ : Representation (ZMod 2) (D.H ⧸ pCore 2 D.H) W₀)
    (s : BinaryConjugationSection D.H D.UH (PlusAction.fixedLayer D)
      (σ.comp (QuotientGroup.mk' (pCore 2 D.H))))
    (K : Subgroup D.H) (hKC : K.IsCComponent)
    (hm : ⁅PlusAction.fixedLayer D,K.map D.H.subtype⁆ ≠ ⊥)
    (hplus : subspaceCommutator σ ⊤ (K.map (QuotientGroup.mk' (pCore 2 D.H))) ≠ ⊥) :
    ¬ IsIrrPlus ρ (K.map (QuotientGroup.mk' (pCore 2 D.H)))
      (subspaceCommutator ρ ⊤ (K.map (QuotientGroup.mk' (pCore 2 D.H)))) := by
  let π := QuotientGroup.mk' (pCore 2 D.H)
  let := hKC.perfect
  let : Group.IsPerfect (K.map π) := Group.IsPerfect.map π
  obtain ⟨p,hp,_,hpker⟩ := BinaryConjugationSection.exists_projection
    D.H D.H D.UH D.V₁ (PlusAction.fixedLayer D) le_rfl (PlusAction.point_le_fixedLayer h)
    π π (QuotientGroup.mk'_surjective _) (MonoidHom.id _) (by intro k; rfl) ρ σ c s
  apply not_isIrrPlus_moved_of_two_noncentral_layers ρ σ (K.map π) p.toLinearMap hp
    (fun k v => LinearMap.congr_fun (p.isIntertwining' k) v) _ hplus
  rw [hpker]
  exact component_fixed_layer_image_not_fixed h ρ c K hKC hm

theorem component_tilde_moved_pointwise_faithful
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    {W W₀ : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup W₀] [Module (ZMod 2) W₀]
    (ρ : Representation (ZMod 2) (D.H ⧸ pCore 2 D.H) W)
    (c : BinaryConjugationSection D.H D.UH D.V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 D.H))))
    (σ : Representation (ZMod 2) (D.H ⧸ pCore 2 D.H) W₀)
    (s : BinaryConjugationSection D.H D.UH (PlusAction.fixedLayer D)
      (σ.comp (QuotientGroup.mk' (pCore 2 D.H))))
    (K : Subgroup D.H) (hfaithful : Function.Injective σ)
    (hwhole : subspaceCommutator σ ⊤ (K.map (QuotientGroup.mk' (pCore 2 D.H))) = ⊤) :
    ∀ k : D.H ⧸ pCore 2 D.H,
      (∀ v ∈ subspaceCommutator ρ ⊤ (K.map (QuotientGroup.mk' (pCore 2 D.H))),
        ρ k v = v) → k = 1 := by
  let π := QuotientGroup.mk' (pCore 2 D.H)
  obtain ⟨p,hp,_,_⟩ := BinaryConjugationSection.exists_projection
    D.H D.H D.UH D.V₁ (PlusAction.fixedLayer D) le_rfl (PlusAction.point_le_fixedLayer h)
    π π (QuotientGroup.mk'_surjective _) (MonoidHom.id _) (by intro k; rfl) ρ σ c s
  exact eq_one_of_fixes_moved_of_faithful_quotient ρ σ (K.map π) p.toLinearMap hp
    (fun k v => LinearMap.congr_fun (p.isIntertwining' k) v) hfaithful hwhole

open Section08.SourceCompletion
open scoped IsMulCommutative
variable {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

theorem source_tilde_component_FF_of_fixed_layer_movement
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
      K.map H.subtype⁆ ≠ ⊥) :
    let U := Section08.Source.UH H V₃
    let π := QuotientGroup.mk' (pCore 2 H)
    ∃ hE : IsElementaryAbelian 2 U, letI := hE;
      ∃ (ρ : Representation (ZMod 2) (H ⧸ pCore 2 H) (Additive (U ⧸ V₁.subgroupOf U)))
        (c : BinaryConjugationSection H U V₁ (ρ.comp π)),
        let I := subspaceCommutator ρ ⊤ (K.map π)
        Function.Injective ρ ∧
        (∀ u : U, (c.coordinates u).toAdd = Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf U) u)) ∧
        (∀ k : H ⧸ pCore 2 H, (∀ v ∈ I, ρ k v = v) → k = 1) ∧
        ¬ IsIrrPlus ρ (K.map π) I ∧
        ∃ D : Subgroup (H ⧸ pCore 2 H),
          D ≤ ((conjugate U (g : G)).subgroupOf H).map π ∧
          IsBestOffender ρ D ∧ D ≤ subspaceStabilizer ρ I ∧
          IsBestOffender (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I D) ∧
          IsFFModule (subspaceImageRepresentation ρ I) := by
  dsimp only
  obtain ⟨hE,ρ,c,hf,hcoord,_,hUg⟩ := source_tilde_offenders d h hU hV g hs hout
  let := hE
  have hfaith := source_plus_faithful_of_kernel_eq σ s hk
  have hwhole := source_plus_component_whole d h hU hV hne g hs hout σ s B hB hBA
    K hKC hK hk hcomm
  have hi := (source_plus_component_irrPlus_and_actor d h hU hV hne g hs hout
    σ s B hB hBA K hK hk hcomm).1
  have hplus := hi.ne_bot σ
  have hpoint := component_tilde_moved_pointwise_faithful h ρ c σ s K hfaith hwhole
  have hnot := component_tilde_not_irrPlus_of_fixed_layer_movement h ρ c σ s K hKC hm hplus
  have hn := source_plus_component_normal d h hU hV hne g hs hout σ s B hB hBA
    K hKC hK hk hcomm
  let π := QuotientGroup.mk' (pCore 2 H)
  let J := K.map π
  let : J.Normal := Subgroup.Normal.map hn π (QuotientGroup.mk'_surjective _)
  let I := subspaceCommutator ρ ⊤ J
  have hstab : (⊤ : Subgroup (H ⧸ pCore 2 H)) ≤ subspaceStabilizer ρ I :=
    subspaceCommutator_invariant_normalizer ρ (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
      (by rw [J.normalizer_eq_top])
  obtain ⟨D,hDle,hD⟩ := hUg.exists_bestOffender ρ
  have hDI : D ≤ subspaceStabilizer ρ I := le_top.trans hstab
  have hmove : ¬ I ≤ fixedSpace ρ D := by
    intro hfix
    apply hD.1.1
    apply bot_unique
    intro x hx
    exact mem_bot.mpr (hpoint x (fun v hv => hfix hv ⟨x,hx⟩))
  have hrestricted := hD.restricted ρ I hDI hmove
  exact ⟨hE,ρ,c,hf,hcoord,hpoint,hnot,D,hDle,hD,hDI,hrestricted,
    ⟨restrictedSubgroup ρ I D,hrestricted.isOffender _⟩⟩
end CFSG.Quasithin.Chapter13.Section07
