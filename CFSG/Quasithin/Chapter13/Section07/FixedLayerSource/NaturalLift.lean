module
public import CFSG.Quasithin.Chapter13.Section07.FixedLayerSource.NaturalImage
public import CFSG.Quasithin.Chapter13.Section07.FixedLayerSource.NaturalCover
public import Theory.Representation.BinaryConjugationSection.Coinvariants
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.DoubledSylowTransport

/-!
# The original component commutator is a natural module

The literal conjugation action on W=[U₀,K] factors through H/O₂(H), because
W centralizes O₂(H). Its map to the already marked image in U_H/V₁ is a
central natural-module cover: perfectness of K supplies full movement, and
the kernel lies in V₁. The same opposite-span offender belongs to the
component by doubled Sylow geometry. One of its involutions removes the
central kernel using the disjoint opposite span, so the cover is bijective.

The source consumer retains the chosen conjugator, the actual component
marking, and the conjugation equation on the original subgroup. This proves
the natural-module step used in original13.7.16(2); the subsequent placement
of the local parabolic is separate.
Source: Aschbacher–Smith13.5.2(3), pp.913–914, and13.7.16(2), p.944.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section07
variable {G X : Type*} [Group G] [Finite G]
  [AddCommGroup X] [Module (ZMod 2) X]
  {F : ChapterF.Section09.Setup G}

theorem fixed_layer_natural_cover
    (h : F.Hypothesis)
    (ρ : Representation (ZMod 2) (F.H ⧸ pCore 2 F.H) X)
    (c : BinaryConjugationSection F.H F.UH F.V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 F.H))))
    (K : Subgroup F.H) (hpK : IsPPerfect 2 (K.map F.H.subtype))
    (hKn : F.H ≤ normalizer (K.map F.H.subtype))
    [IsElementaryAbelian 2 (⁅PlusAction.fixedLayer F,K.map F.H.subtype⁆ : Subgroup G)]
    (hsM : K.map (QuotientGroup.mk' (pCore 2 F.H)) ≤ subspaceStabilizer ρ
      (c.imageSpace ⁅PlusAction.fixedLayer F,K.map F.H.subtype⁆))
    (j : K.map (QuotientGroup.mk' (pCore 2 F.H)) ≃* BinaryLinearThree.Group)
    (e : (invariantSubspace ρ (K.map (QuotientGroup.mk' (pCore 2 F.H)))
      (c.imageSpace ⁅PlusAction.fixedLayer F,K.map F.H.subtype⁆) hsM).toRepresentation.Equiv
        (BinaryLinearThree.W.comp j.toMonoidHom)) :
    let π := QuotientGroup.mk' (pCore 2 F.H)
    let J := K.map π
    let W := (⁅PlusAction.fixedLayer F,K.map F.H.subtype⁆ : Subgroup G)
    ∃ δ : Representation (ZMod 2) (F.H ⧸ pCore 2 F.H) (Additive W),
      (∀ (t : F.H) (w : Additive W), ((δ (π t) w).toMul : G) = t*w.toMul*(t:G)⁻¹) ∧
      ∃ p : Representation.IntertwiningMap
        (δ.comp (J.subtype.comp j.symm.toMonoidHom)) BinaryLinearThree.W,
        Representation.OneCohomology.IsCover p ∧
        (∀ w : Additive W, p w = 0 → (w.toMul : G) ∈ F.V₁) ∧
        (∀ w : Additive W, p w = e ⟨(c.coordinates ⟨w.toMul,
          (le_normalizer_iff_commutator_le_left.mp
            ((map_subtype_le K).trans (PlusAction.fixedLayer_normalized (D := F))))
                w.toMul.property |>.1⟩).toAdd,
          (c.mem_imageSpace_iff W _).mpr ⟨_,w.toMul.property,rfl⟩⟩) := by
  dsimp only
  let π := QuotientGroup.mk' (pCore 2 F.H)
  let J := K.map π
  let C := K.map F.H.subtype
  let U₀ := PlusAction.fixedLayer F
  let W := (⁅U₀,C⁆ : Subgroup G)
  let M := c.imageSpace W
  have hCH : C ≤ F.H := map_subtype_le K
  have hWU : W ≤ U₀ := le_normalizer_iff_commutator_le_left.mp
    (hCH.trans (PlusAction.fixedLayer_normalized (D := F)))
  have hWUH : W ≤ F.UH := hWU.trans inf_le_left
  have hWH : W ≤ F.H := hWUH.trans c.section_le
  have hNW : F.H ≤ normalizer W := by
    intro t ht
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (PlusAction.fixedLayer_normalized (D := F) ht),
      mem_normalizer_iff_map_conj_eq.mp (hKn ht)]
  have hk : ∀ t ∈ π.ker, (t : G) ∈ centralizer (W : Set G) := by
    intro t ht w hw
    have htQ : (t : G) ∈ F.H.pCoreIn 2 := by
      exact ⟨t,(QuotientGroup.eq_one_iff _).mp ht,rfl⟩
    exact (hWU hw).2 t htQ |>.symm
  obtain ⟨δ,cW,hcW⟩ := BinaryConjugationSection.exists_of_central_kernel
    F.H W hWH hNW π (QuotientGroup.mk'_surjective _) hk
  have hδ (t : F.H) (w : Additive W) :
      ((δ (π t) w).toMul : G) = t*w.toMul*(t:G)⁻¹ := by
    have hh := cW.equivariant t w.toMul
    rw [hcW,hcW] at hh
    exact (congrArg (fun x : Additive W => (x.toMul : G)) hh).symm
  let σ : Representation (ZMod 2) BinaryLinearThree.Group (Additive W) :=
    δ.comp (J.subtype.comp j.symm.toMonoidHom)
  let m : W →* F.UH := W.inclusion hWUH
  let f₀ : Additive W →ₗ[ZMod 2] X :=
    (c.coordinates.comp m).toAdditiveLeft.toZModLinearMap 2
  let f : Additive W →ₗ[ZMod 2] M := f₀.codRestrict M (fun w =>
    (c.mem_imageSpace_iff W _).mpr ⟨m w.toMul,w.toMul.property,rfl⟩)
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨u,hu,he⟩ := (c.mem_imageSpace_iff W _).mp v.property
    refine ⟨Additive.ofMul ⟨u,hu⟩,Subtype.ext he⟩
  have hf_act (k : J) (w : Additive W) :
      f (δ k w) = (invariantSubspace ρ J M hsM).toRepresentation k (f w) := by
    obtain ⟨t,ht⟩ := QuotientGroup.mk'_surjective (pCore 2 F.H) (k : F.H ⧸ pCore 2 F.H)
    apply Subtype.ext
    change f₀ (δ k w) = ρ k (f₀ w)
    rw [←ht]
    have hh := c.equivariant t (m w.toMul)
    have hw := hδ t w
    change (c.coordinates (m ((δ (π t) w).toMul))).toAdd = _
    exact (congrArg (fun u : F.UH => (c.coordinates u).toAdd)
      (Subtype.ext hw)).trans hh
  let p : σ.IntertwiningMap BinaryLinearThree.W := {
    toLinearMap := e.toLinearMap.comp f
    isIntertwining' := by
      intro a
      apply LinearMap.ext
      intro w
      change e (f (δ (J.subtype (j.symm a)) w)) = BinaryLinearThree.W a (e (f w))
      have he := LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' (j.symm a)) (f w)
      change e ((invariantSubspace ρ J M hsM).toRepresentation (j.symm a) (f w)) =
        BinaryLinearThree.W (j (j.symm a)) (e (f w)) at he
      rw [j.apply_symm_apply] at he
      exact (congrArg e (hf_act (j.symm a) w)).trans he }
  have hker (w : Additive W) (hw : p w = 0) : (w.toMul : G) ∈ F.V₁ := by
    have hf0 : f w = 0 := e.injective (hw.trans e.map_zero.symm)
    exact (c.coordinates_eq_one_iff (m w.toMul)).mp
      (Multiplicative.toAdd.injective (congrArg Subtype.val hf0))
  have hfixed : p.toLinearMap.ker ≤ Representation.invariants σ := by
    intro w hw a
    obtain ⟨t,ht⟩ := QuotientGroup.mk'_surjective (pCore 2 F.H) (j.symm a)
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((δ (J.subtype (j.symm a)) w).toMul : G) = w.toMul
    simp only [Subgroup.subtype_apply]
    rw [←ht,hδ]
    rw [← h.H_centralizes t.property w.toMul (hker w hw),mul_inv_cancel_right]
  have hgen : ⁅C,W⁆ ⊔ (⊥ : Subgroup G) = W := by
    rw [sup_bot_eq,commutator_comm]
    exact commutator_isPPerfect_idempotent C U₀ hpK
      (h.g2_hypothesis.U_isPGroup.to_le inf_le_left)
      (hCH.trans (PlusAction.fixedLayer_normalized (D := F)))
  let r : C →* BinaryLinearThree.Group := (j.toMonoidHom.comp
    (π.subgroupMap K)).comp (K.equivMapOfInjective F.H.subtype F.H.subtype_injective).symm.toMonoidHom
  have hact (k : C) (w : Additive W) :
      (δ.comp π) ⟨k,hCH k.property⟩ w = σ (r k) w := by
    change δ (π ⟨k,hCH k.property⟩) w =
      δ (J.subtype (j.symm (r k))) w
    congr 2
    change _ = (j.symm (j ((π.subgroupMap K)
      ((K.equivMapOfInjective F.H.subtype F.H.subtype_injective).symm k))) : F.H ⧸ pCore 2 F.H)
    rw [j.symm_apply_apply]
    change π ⟨k,hCH k.property⟩ = π _
    congr 1
    apply Subtype.ext
    exact (congrArg (fun z : C => (z : G))
      ((K.equivMapOfInjective F.H.subtype F.H.subtype_injective).apply_symm_apply k)).symm
  have hfull := cW.coinvariants_eq_top_of_group_generation C hCH σ r hact hgen
  refine ⟨δ,hδ,p,⟨e.surjective.comp hf,hfixed,hfull⟩,hker,?_⟩
  intro w
  rfl
end CFSG.Quasithin.Chapter13.Section07

namespace CFSG.Quasithin.Chapter13.Section07
open ChapterB.QuasisimpleSource
variable {G X : Type*} [Group G] [Finite G]
  [AddCommGroup X] [Module (ZMod 2) X]

theorem doubled_offender_le_component
    (ρ : Representation (ZMod 2) G X) (hf : Function.Injective ρ)
    (J : Subgroup G) [J.Normal]
    (a : ActionEquiv (ρ.comp J.subtype)
      (repeated (linearNatural BinaryField.two 3) 2))
    (D : Subgroup G) (hD : IsOffender ρ D) : D ≤ J := by
  obtain ⟨P,hDP⟩ := hD.1.2.isPGroup.exists_le_sylow
  obtain ⟨g,_,hRJ,huniq,_⟩ := doubled_sylow_geometry ρ hf J ⊤ le_top a (P.subtype le_top)
  apply (huniq D ?_ hD).symm ▸ hRJ
  rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (P : Subgroup G) ≤ ⊤ from le_top)]
  exact hDP

end CFSG.Quasithin.Chapter13.Section07

namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup ChapterB.QuasisimpleSource
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d
theorem source_component_fixed_layer_natural_packet
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
    let π := QuotientGroup.mk' (pCore 2 H)
    let J := K.map π
    let N := (⁅PlusAction.fixedLayer (ConjugateIntersections.sourceSetup T L V V₃ V₁ H),
      K.map H.subtype⁆ : Subgroup G)
    ∃ hEU : IsElementaryAbelian 2 (Section08.Source.UH H V₃), letI := hEU;
      ∃ (ρ : Representation (ZMod 2) (H ⧸ pCore 2 H)
          (Additive ((Section08.Source.UH H V₃) ⧸ V₁.subgroupOf (Section08.Source.UH H V₃))))
        (hsI : (⊤ : Subgroup (H ⧸ pCore 2 H)) ≤ subspaceStabilizer ρ (subspaceCommutator ρ ⊤ J))
        (a : ActionEquiv ((wholeSubspaceAction ρ (subspaceCommutator ρ ⊤ J) hsI).comp J.subtype)
          (repeated (linearNatural BinaryField.two 3) 2)),
        ∃ hE : IsElementaryAbelian 2 N, letI := hE;
          ∃ (δ : Representation (ZMod 2) (H ⧸ pCore 2 H) (Additive N))
            (p : Representation.IntertwiningMap
              (δ.comp (J.subtype.comp a.groupEquiv.symm.toMonoidHom)) BinaryLinearThree.W),
            (∀ (t : H) (w : Additive N), ((δ (π t) w).toMul : G) = t*w.toMul*(t:G)⁻¹) ∧
            Function.Bijective p.toLinearMap ∧ ∃ D : Subgroup (H ⧸ pCore 2 H),
              D ≤ ((conjugate (Section08.Source.UH H V₃) (g : G)).subgroupOf H).map π ∧
              IsOffender (wholeSubspaceAction ρ (subspaceCommutator ρ ⊤ J) hsI) D := by
  dsimp only
  obtain ⟨hE,ρ,c,_,_,hpoint,hnot,D,hDle,hD,_,hDimage,_⟩ :=
    source_tilde_component_FF_of_fixed_layer_movement d h hU hV hne g hs hout
      σ s B hB hBA K hKC hK hk hcomm hm
  let := hE
  let π := QuotientGroup.mk' (pCore 2 H)
  let J := K.map π
  have hnK := source_plus_component_normal d h hU hV hne g hs hout
    σ s B hB hBA K hKC hK hk hcomm
  let : J.Normal := Subgroup.Normal.map hnK π (QuotientGroup.mk'_surjective _)
  obtain ⟨F,hF,hfin,hcard,⟨a⟩⟩ := hl
  let := hF
  let := hfin
  let := Fintype.ofFinite F
  let f : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hcard)).symm
  let eJ := a.trans ((Atlas.fieldEquivPSL 3 f).trans Matrix.PSL3Two.equiv.symm)
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Atlas.Comparisons.Exceptional.sl3Two_simple
  let : IsSimpleGroup J := eJ.isSimpleGroup
  have hc : Nat.card J = 168 :=
    (Nat.card_congr eJ.toEquiv).trans Atlas.Comparisons.Exceptional.sl3Two_card
  have hi := (source_plus_component_irrPlus_and_actor d h hU hV hne g hs hout
    σ s B hB hBA K hK hk hcomm).1
  have hwhole := source_plus_component_whole d h hU hV hne g hs hout
    σ s B hB hBA K hKC hK hk hcomm
  rw [hwhole] at hi
  obtain ⟨hUgA,_,_,_⟩ := pair_conjugate_seed_quotient_nontrivial d h hU hV g hs hout
  have hUgT : conjugate (Section08.Source.UH H V₃) (g : G) ≤ (T : Subgroup G) :=
    hUgA.trans inf_le_right |>.trans (h.sylow_centralizer.symm.le.trans inf_le_left)
  have hDS : D ≤ ((T : Subgroup G).subgroupOf H).map π :=
    hDle.trans (map_mono (comap_mono hUgT))
  have hcS := source_plus_sylow_centralizer_eq_bot d h hU hV hne g hs hout
    σ s B hB hBA K hKC hK hk hcomm
  have hDC : D ⊓ centralizer (J : Set (H ⧸ pCore 2 H)) = ⊥ := by
    apply bot_unique
    rw [← hcS]
    exact inf_le_inf_right _ hDS
  obtain ⟨hsI,⟨aI⟩⟩ := component_tilde_doubleThree ρ σ
    (source_plus_faithful_of_kernel_eq σ s hk) (source_plus_sqtk_cover d h)
    hi hK hc hpoint hnot hDimage hD.1.2.isPGroup hD.1.1 hDC
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let N := (⁅PlusAction.fixedLayer F,K.map H.subtype⁆ : Subgroup G)
  have hNU : N ≤ F.UH := (le_normalizer_iff_commutator_le_left.mp
    ((map_subtype_le K).trans (PlusAction.fixedLayer_normalized (D := F)))).trans inf_le_left
  let : IsElementaryAbelian 2 F.UH := hE
  let hEN : IsElementaryAbelian 2 N := IsElementaryAbelian.of_le hNU
  let := hEN
  have hKn : H ≤ normalizer (K.map H.subtype) := by
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le K)).mp
    change ((K.map H.subtype).comap H.subtype).Normal
    rwa [comap_map_eq_self_of_injective H.subtype_injective]
  let : Group.IsPerfect K := hKC.perfect
  let : Group.IsPerfect (K.map H.subtype) := Group.IsPerfect.map H.subtype
  have hpK : IsPPerfect 2 (K.map H.subtype) := by
    intro R hR hq
    let : R.Normal := hR
    by_contra hneR
    let : Nontrivial ((K.map H.subtype) ⧸ R) := QuotientGroup.nontrivial_iff.mpr hneR
    let : Group.IsPerfect ((K.map H.subtype) ⧸ R) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective R)
    let : Group.IsNilpotent ((K.map H.subtype) ⧸ R) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable ((K.map H.subtype) ⧸ R) inferInstance
  have hplus := (source_plus_component_irrPlus_and_actor d h hU hV hne g hs hout
    σ s B hB hBA K hK hk hcomm).1.ne_bot σ
  obtain ⟨hsN,⟨eN⟩⟩ := component_fixed_layer_image_natural h ρ c σ s K hKC hm hplus hsI aI
  let : IsElementaryAbelian 2 (⁅PlusAction.fixedLayer F,K.map F.H.subtype⁆ : Subgroup G) := hEN
  obtain ⟨δ,hδ,p,hp,hker,_⟩ := fixed_layer_natural_cover h ρ c K hpK hKn hsN aI.groupEquiv eN
  let I := subspaceCommutator ρ ⊤ J
  let τ := wholeSubspaceAction ρ I hsI
  have hfτ := wholeSubspaceAction_faithful ρ I hsI hpoint
  have hDτ := wholeSubspaceAction_bestOffender ρ I hsI hpoint hDimage
  have hDJ : D ≤ J := doubled_offender_le_component τ hfτ J aI D (hDτ.isOffender τ)
  obtain ⟨x,hx,hxne⟩ := D.bot_or_exists_ne_one.resolve_left hD.1.1
  let : IsElementaryAbelian 2 D := hD.1.2
  have hx2 : orderOf x = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian x hx) hxne
  let xJ : J := ⟨x,hDJ hx⟩
  let a := aI.groupEquiv xJ
  have ha : orderOf a = 2 := (aI.groupEquiv.orderOf_eq xJ).trans
    ((orderOf_injective J.subtype J.subtype_injective xJ).symm.trans hx2)
  obtain ⟨u,hu,he⟩ := hDle hx
  have hact (w : Additive N) :
      (((δ.comp (J.subtype.comp aI.groupEquiv.symm.toMonoidHom)) a w).toMul : G) =
        u*w.toMul*(u:G)⁻¹ := by
    change ((δ ((aI.groupEquiv.symm (aI.groupEquiv xJ) : J) : H ⧸ pCore 2 H) w).toMul : G) = _
    rw [aI.groupEquiv.symm_apply_apply]
    change ((δ x w).toMul : G) = _
    rw [←he]
    exact hδ u w
  have hbij := source_component_natural_cover_bijective d h hU g hs hout
    (K.map H.subtype) (map_subtype_le K) _ p hp hker a ha (u:G) hu hact
  exact ⟨hE,ρ,hsI,aI,hEN,δ,p,hδ,hbij,D,hDle,hDτ.isOffender τ⟩

theorem source_component_fixed_layer_natural
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
    let π := QuotientGroup.mk' (pCore 2 H)
    let J := K.map π
    let N := (⁅PlusAction.fixedLayer (ConjugateIntersections.sourceSetup T L V V₃ V₁ H),
      K.map H.subtype⁆ : Subgroup G)
    ∃ hE : IsElementaryAbelian 2 N, letI := hE;
      ∃ (j : J ≃* BinaryLinearThree.Group)
        (δ : Representation (ZMod 2) (H ⧸ pCore 2 H) (Additive N))
        (p : Representation.IntertwiningMap
          (δ.comp (J.subtype.comp j.symm.toMonoidHom)) BinaryLinearThree.W),
        (∀ (t : H) (w : Additive N), ((δ (π t) w).toMul : G) = t*w.toMul*(t:G)⁻¹) ∧
        Function.Bijective p := by
  obtain ⟨hEU,ρ,hsI,a,hE,δ,p,hδ,hp,_⟩ :=
    source_component_fixed_layer_natural_packet d h hU hV hne g hs hout
      σ s B hB hBA K hKC hK hk hcomm hm hl
  exact ⟨hE,a.groupEquiv,δ,p,hδ,hp⟩

end CFSG.Quasithin.Chapter13.Section07
