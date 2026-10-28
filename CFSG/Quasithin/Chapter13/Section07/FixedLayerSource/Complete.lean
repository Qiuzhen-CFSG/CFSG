module
public import CFSG.Quasithin.Chapter13.Section07.FixedLayerSource.FullActor
public import CFSG.Quasithin.Chapter13.Section07.FixedLayerSource.LocalFlagInputs
public import CFSG.Quasithin.Chapter13.Section07.FixedLayerSource.Coordinates
public import Theory.Representation.PSL3Two.DoubledLocalFlag
public import CFSG.Quasithin.Chapter13.Section07.NaturalFixedLine
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedProduct

/-!
# The selected natural component centralizes the fixed layer

If the original PSL₃(2) component moved U₀, the two-layer tilde argument would
give two natural copies. The actual commutator [U₀,K] is one natural copy:
the same opposite-span involution eliminates its central point kernel.
The faithful plus quotient forces K*=H*. The unique doubled-natural Sylow
offender puts the original L₁T image in the line parabolic, with L₁ containing
its residual and the opposite span containing its radical. One inner change
of coordinates marks all three actors at once. The original pair fixed-line
contradiction now rules out [U₀,K]≠1.

All action, marking, and placement premises of that contradiction are
discharged here from the selected source row. No classification of the other
rows is asserted. Source: Aschbacher–Smith13.7.16(2), printed p.944, using
original13.5.2(3), pp.913–914.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup ChapterB.QuasisimpleSource
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)

private theorem lineV_R : lineV = BinaryLinearThree.R := by
  have he : lineParabolicSL.pCoreIn 2 = lineV := by
    rw [←pointParabolic_map_diagram,←map_pCoreIn_of_injective 2 _ _ diagram.injective,
      MarkedProduct.pointParabolic_core,pointV_map_diagram]
  rw [←he,lineParabolicSL_pCoreIn_two_eq_R]

private theorem map_conj_cancel (A : Subgroup SL) (g : SL) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = A := by
  rw [Subgroup.map_map]
  have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id SL := by
    ext a
    simp [MulAut.conj_apply,mul_assoc]
  rw [he,Subgroup.map_id]

include d
theorem source_no_fixed_layer_linear_three
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
    False := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let π := QuotientGroup.mk' (pCore 2 H)
  let J := K.map π
  let N := (⁅PlusAction.fixedLayer F,K.map H.subtype⁆ : Subgroup G)
  have hJ : J = ⊤ := source_fixed_layer_component_eq_top d h hU hV hne g hs hout
    σ s B hB hBA K hKC hK hk hcomm hm hl
  obtain ⟨hEU,ρ,hsI,a,hEN,δ,p,hδ,hp,D,hDle,hD⟩ :=
    source_component_fixed_layer_natural_packet d h hU hV hne g hs hout
      σ s B hB hBA K hKC hK hk hcomm hm hl
  let := hEU
  let := hEN
  let I := subspaceCommutator ρ ⊤ J
  let τ := wholeSubspaceAction ρ I hsI
  let tJ : J ≃* (H ⧸ pCore 2 H) := MulEquiv.ofBijective J.subtype
    ⟨J.subtype_injective,fun x => ⟨⟨x,by rw [hJ]; trivial⟩,rfl⟩⟩
  have ht (x : H ⧸ pCore 2 H) : ((tJ.symm x : J) : H ⧸ pCore 2 H) = x :=
    tJ.apply_symm_apply x
  let eJ : (H ⧸ pCore 2 H) ≃* SL := tJ.symm.trans a.groupEquiv
  have hτ (x : H ⧸ pCore 2 H) (v : I) :
      a.linearEquiv (τ x v) = (repeated (linearNatural BinaryField.two 3) 2) (eJ x) (a.linearEquiv v) := by
    have hh := a.intertwines (tJ.symm x) v
    change a.linearEquiv (τ ((tJ.symm x : J) : H ⧸ pCore 2 H) v) = _ at hh
    rwa [ht] at hh
  let b := a.linearEquiv.trans (LinearEquiv.finTwoArrow (ZMod 2) BinaryLinearThree.Vector)
  have hb (x : H ⧸ pCore 2 H) (v : I) :
      b (τ x v) = (BinaryLinearThree.W.prod BinaryLinearThree.W) (eJ x) (b v) :=
    congrArg (LinearEquiv.finTwoArrow (ZMod 2) BinaryLinearThree.Vector) (hτ x v)
  let S := (T.subtype h.T_le_H).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  let P := ((F.L₁ ⊔ (T : Subgroup G)).subgroupOf H).map π
  let Q := ((L ⊔ (T : Subgroup G)).pCoreIn 2 |>.subgroupOf H).map π
  obtain ⟨hSP,hPQ,hQS,hP,hres⟩ := source_fixed_layer_local_inputs d h hne hk
  obtain ⟨hUgA,_,_,_⟩ := pair_conjugate_seed_quotient_nontrivial d h hU hV g hs hout
  have hDQ : D ≤ Q := hDle.trans (map_mono (comap_mono (hUgA.trans inf_le_right)))
  obtain ⟨z,hS,hPz,hDz⟩ := BinaryLinearThree.DoubledOffenders.doubled_local_line_flag
    τ eJ b hb S P Q D hSP hPQ hDQ hQS hD hP
  let fJ := (MulAut.conj z⁻¹).toMonoidHom.comp eJ.toMonoidHom
  have hSf : (S : Subgroup (H ⧸ pCore 2 H)).map fJ = borelSL := by
    rw [←Subgroup.map_map,hS,map_conj_cancel]
  have hPf : P.map fJ = lineParabolicSL := by
    rw [←Subgroup.map_map,hPz,map_conj_cancel]
  have hDf : D.map fJ = BinaryLinearThree.R := by
    rw [←Subgroup.map_map,hDz,map_conj_cancel]
  have hL : lineA ≤ (F.L₁.subgroupOf H).map (fJ.comp π) := by
    have hh := map_mono (f := fJ) hres
    rw [map_embedded_pResidual,hPf] at hh
    change residual lineParabolicSL ≤ _ at hh
    rw [line_residual] at hh
    rwa [Subgroup.map_map] at hh
  have hR : lineV ≤ ((conjugate F.UH (g : G)).subgroupOf H).map (fJ.comp π) := by
    have hh := map_mono (f := fJ) hDle
    rwa [hDf,←lineV_R,Subgroup.map_map] at hh
  have hnp := source_plus_component_normal d h hU hV hne g hs hout
    σ s B hB hBA K hKC hK hk hcomm
  have hKn : H ≤ normalizer (K.map H.subtype) := by
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le K)).mp
    change ((K.map H.subtype).comap H.subtype).Normal
    rwa [comap_map_eq_self_of_injective H.subtype_injective]
  let hHN := NaturalFixedLine.component_layer_normalized (T := T) (L := L) (V := V)
    (V₃ := V₃) (V₁ := V₁) (K.map H.subtype) hKn
  let e₀ : N ≃* Model := naturalCoverCoordinates N p.toLinearMap hp
  let e := e₀.trans (slAut z⁻¹)
  have hinter (x : H ⧸ pCore 2 H) (w : Additive N) :
      p.toLinearMap (δ x w) = BinaryLinearThree.W (eJ x) (p.toLinearMap w) := by
    have hh := LinearMap.congr_fun (p.isIntertwining' (eJ x)) w
    change p.toLinearMap (δ ((a.groupEquiv.symm (a.groupEquiv (tJ.symm x)) : J) : H ⧸ pCore 2 H) w) = _ at hh
    rw [a.groupEquiv.symm_apply_apply,ht] at hh
    exact hh
  have he₀ : linearAction H N hHN e₀ = eJ.toMonoidHom.comp π :=
    naturalCoordinates_linearAction H N hHN π δ p.toLinearMap hp
      (eJ.toMonoidHom.comp π) (fun t w => hinter (π t) w) hδ
  have he : linearAction H N hHN e = fJ.comp π := by
    rw [linearAction_postcompose,he₀]
    rfl
  have hHG : H ≤ G₁ := by
    rw [d.first_normalizer]
    exact h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  exact NaturalFixedLine.source_no_natural_fixed_layer_flag d h hU hV
    (seed_noncentral_on_local_core h hHG hne) g hout (K.map H.subtype)
    (map_subtype_le K) hKn e (he.symm ▸ hL)
    (by rw [he]; exact (show _ = borelSL from (Subgroup.map_map _ _ _).symm.trans hSf).symm.le)
    (he.symm ▸ hR)
theorem source_linear_three_component_centralizes_fixedLayer
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
    (hl : ClassicalGroup.IsPSL (K.map (QuotientGroup.mk' (pCore 2 H))) 3 2) :
    K.map H.subtype ≤ centralizer (PlusAction.fixedLayer
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) : Set G) := by
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [commutator_comm]
  by_contra hm
  exact source_no_fixed_layer_linear_three d h hU hV hne g hs hout
    σ s B hB hBA K hKC hK hk hcomm hm hl

end CFSG.Quasithin.Chapter13.Section07
