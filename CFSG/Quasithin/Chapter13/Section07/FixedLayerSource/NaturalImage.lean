module
public import CFSG.Quasithin.Chapter13.Section07.FixedLayerSource.DoubleThree
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ProperDouble
public import Theory.Representation.BinaryConjugationSection.CommutatorImage

/-!
# The natural image of the original fixed-layer commutator

The component-moved tilde module consists of two copies of the binary
natural three-dimensional module. The image of [U₀,K] is nonzero by the
original F.9 perfect-component argument. It is proper because it lies in
the kernel of the projection to the plus module, where K has nonzero
movement. A nonzero proper submodule of these two copies is one natural
copy. Its coordinates retain the same component marking as the doubled
module.

The source specialization constructs the canonical U_H/V₁ section and
applies this argument to the literal [U₀,K]. It supplies the quotient
marking needed by the separate central-point removal, without identifying
the original subgroup with its image prematurely.
Source: Aschbacher–Smith13.5.2(3), pp.913–914, and13.7.16(2), p.944.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section07
open ChapterB.QuasisimpleSource
variable {G X : Type*} [Group G] [AddCommGroup X] [Module (ZMod 2) X]

theorem proper_subspace_of_double_natural
    (ρ : Representation (ZMod 2) G X) (J : Subgroup G)
    (I : Submodule (ZMod 2) X) (hsI : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ I)
    (a : ActionEquiv ((wholeSubspaceAction ρ I hsI).comp J.subtype)
      (repeated (linearNatural BinaryField.two 3) 2))
    (M : Submodule (ZMod 2) X) (hsM : J ≤ subspaceStabilizer ρ M)
    (hMI : M ≤ I) (hne : M ≠ ⊥) (hproper : M ≠ I) :
    Nonempty ((invariantSubspace ρ J M hsM).toRepresentation.Equiv
      ((linearNatural BinaryField.two 3).comp a.groupEquiv.toMonoidHom)) := by
  let N : Subrepresentation ((wholeSubspaceAction ρ I hsI).comp J.subtype) :=
    ⟨M.comap I.subtype,by intro g v hv; exact (hsM g.property _).2 hv⟩
  have hNne : N ≠ ⊥ := by
    intro hz
    apply hne
    apply bot_unique
    intro v hv
    have he : (⟨v,hMI hv⟩ : I) ∈ N.toSubmodule := hv
    rw [hz] at he
    exact congrArg Subtype.val (show (⟨v,hMI hv⟩ : I) = 0 from he)
  have hNp : N ≠ ⊤ := by
    intro ht
    apply hproper
    apply le_antisymm hMI
    intro v hv
    have he : (⟨v,hv⟩ : I) ∈ N.toSubmodule := by rw [ht]; trivial
    exact he
  obtain ⟨e⟩ := repeated_double_proper_submodule_equiv _ BinaryField.two (by decide) a N hNne hNp
  let b : N.toRepresentation.Equiv (invariantSubspace ρ J M hsM).toRepresentation :=
    .mk (Submodule.comapSubtypeEquivOfLe hMI) (by intro g; ext v; rfl)
  let e' := b.symm.trans e
  exact ⟨e'⟩

variable {A : Type*} [Group A] [Finite A]

/-- The literal fixed-layer commutator is a nonzero proper submodule of
its doubled component-moved tilde module. -/
theorem component_fixed_layer_image_natural
    {F : ChapterF.Section09.Setup A} (h : F.Hypothesis)
    {X₀ : Type*} [AddCommGroup X₀] [Module (ZMod 2) X₀]
    (ρ : Representation (ZMod 2) (F.H ⧸ pCore 2 F.H) X)
    (c : BinaryConjugationSection F.H F.UH F.V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 F.H))))
    (σ : Representation (ZMod 2) (F.H ⧸ pCore 2 F.H) X₀)
    (s : BinaryConjugationSection F.H F.UH (PlusAction.fixedLayer F)
      (σ.comp (QuotientGroup.mk' (pCore 2 F.H))))
    (K : Subgroup F.H) (hKC : K.IsCComponent)
    (hm : ⁅PlusAction.fixedLayer F,K.map F.H.subtype⁆ ≠ ⊥)
    (hplus : subspaceCommutator σ ⊤ (K.map (QuotientGroup.mk' (pCore 2 F.H))) ≠ ⊥)
    (hsI : (⊤ : Subgroup (F.H ⧸ pCore 2 F.H)) ≤ subspaceStabilizer ρ
      (subspaceCommutator ρ ⊤ (K.map (QuotientGroup.mk' (pCore 2 F.H)))))
    (a : ActionEquiv ((wholeSubspaceAction ρ
      (subspaceCommutator ρ ⊤ (K.map (QuotientGroup.mk' (pCore 2 F.H)))) hsI).comp
      (K.map (QuotientGroup.mk' (pCore 2 F.H))).subtype)
      (repeated (linearNatural BinaryField.two 3) 2)) :
    let J := K.map (QuotientGroup.mk' (pCore 2 F.H))
    let M := c.imageSpace ⁅PlusAction.fixedLayer F,K.map F.H.subtype⁆
    ∃ hsM : J ≤ subspaceStabilizer ρ M,
      Nonempty ((invariantSubspace ρ J M hsM).toRepresentation.Equiv
        ((linearNatural BinaryField.two 3).comp a.groupEquiv.toMonoidHom)) := by
  dsimp only
  let π := QuotientGroup.mk' (pCore 2 F.H)
  let J := K.map π
  let U₀ := PlusAction.fixedLayer F
  let Z := c.imageSpace U₀
  let I := subspaceCommutator ρ ⊤ J
  let M := c.imageSpace ⁅U₀,K.map F.H.subtype⁆
  have hKH : K.map F.H.subtype ≤ F.H := by simpa using map_le_range F.H.subtype K
  have hsub : (K.map F.H.subtype).subgroupOf F.H = K :=
    K.comap_map_eq_self_of_injective F.H.subtype_injective
  have hM : M = subspaceCommutator ρ Z J := by
    dsimp only [M]
    rw [commutator_comm,c.imageSpace_commutator _ U₀ hKH (show U₀ ≤ F.UH from inf_le_left),
      subspaceCommutator_comp_map,hsub]
  have hsZ : (⊤ : Subgroup (F.H ⧸ pCore 2 F.H)) ≤ subspaceStabilizer ρ Z := by
    apply le_subspaceStabilizer
    intro k _ v hv
    obtain ⟨t,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 F.H) k
    obtain ⟨u,hu,rfl⟩ := (c.mem_imageSpace_iff U₀ v).mp hv
    let z : F.UH := ⟨(t : A)*u*(t : A)⁻¹,
      (mem_normalizer_iff.mp (c.normalized t.property) u).mp u.property⟩
    exact (c.mem_imageSpace_iff U₀ _).mpr
      ⟨z,(mem_normalizer_iff.mp (PlusAction.fixedLayer_normalized (D := F) t.property) u).mp hu,
        c.equivariant t u⟩
  have hsM : J ≤ subspaceStabilizer ρ M := by
    rw [hM]
    exact subspaceCommutator_invariant_normalizer ρ
      (le_trans le_top hsZ) J.le_normalizer
  have hMI : M ≤ I := by
    rw [hM]
    exact subspaceCommutator_mono_left ρ le_top J
  have hneM : M ≠ ⊥ := by
    rw [hM]
    intro hz
    exact component_fixed_layer_image_not_fixed h ρ c K hKC hm
      ((subspaceCommutator_eq_bot_iff ρ Z J).mp hz)
  obtain ⟨p,hp,_,hpker⟩ := BinaryConjugationSection.exists_projection
    F.H F.H F.UH F.V₁ U₀ le_rfl (PlusAction.point_le_fixedLayer h)
    π π (QuotientGroup.mk'_surjective _) (MonoidHom.id _) (by intro k; rfl) ρ σ c s
  have hMker : M ≤ p.toLinearMap.ker := by
    rw [hpker,hM]
    exact subspaceCommutator_le_of_invariant ρ (le_trans le_top hsZ)
  have hproper : M ≠ I := by
    intro he
    apply hplus
    have hmap := map_moved_of_surjective_intertwining ρ σ J p.toLinearMap hp
      (fun k v => LinearMap.congr_fun (p.isIntertwining' k) v)
    rw [←hmap]
    apply bot_unique
    rintro _ ⟨v,hv,rfl⟩
    exact hMker (he.symm ▸ hv)
  exact ⟨hsM,proper_subspace_of_double_natural ρ J I hsI a M hsM hMI hneM hproper⟩
end CFSG.Quasithin.Chapter13.Section07

namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup ChapterB.QuasisimpleSource
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d
theorem source_component_fixed_layer_image_natural
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
    let U := Section08.Source.UH H V₃
    let π := QuotientGroup.mk' (pCore 2 H)
    ∃ hE : IsElementaryAbelian 2 U, letI := hE;
      ∃ (ρ : Representation (ZMod 2) (H ⧸ pCore 2 H) (Additive (U ⧸ V₁.subgroupOf U)))
        (c : BinaryConjugationSection H U V₁ (ρ.comp π)),
        let I := subspaceCommutator ρ ⊤ (K.map π)
        let N := c.imageSpace ⁅PlusAction.fixedLayer
          (ConjugateIntersections.sourceSetup T L V V₃ V₁ H),K.map H.subtype⁆
        (∀ u : U, (c.coordinates u).toAdd = Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf U) u)) ∧
        ∃ (hsI : (⊤ : Subgroup (H ⧸ pCore 2 H)) ≤ subspaceStabilizer ρ I)
          (a : ActionEquiv ((wholeSubspaceAction ρ I hsI).comp (K.map π).subtype)
            (repeated (linearNatural BinaryField.two 3) 2))
          (hsN : K.map π ≤ subspaceStabilizer ρ N),
          Nonempty ((invariantSubspace ρ (K.map π) N hsN).toRepresentation.Equiv
            ((linearNatural BinaryField.two 3).comp a.groupEquiv.toMonoidHom)) := by
  dsimp only
  obtain ⟨hE,ρ,c,hcoord,hsI,⟨a⟩⟩ :=
    source_tilde_component_doubleThree_of_fixed_layer_movement d h hU hV hne g hs hout
      σ s B hB hBA K hKC hK hk hcomm hm hl
  let := hE
  have hplus := (source_plus_component_irrPlus_and_actor d h hU hV hne g hs hout
    σ s B hB hBA K hK hk hcomm).1.ne_bot σ
  obtain ⟨hsN,e⟩ := component_fixed_layer_image_natural h ρ c σ s K hKC hm hplus hsI a
  exact ⟨hE,ρ,c,hcoord,hsI,a,hsN,e⟩

end CFSG.Quasithin.Chapter13.Section07
