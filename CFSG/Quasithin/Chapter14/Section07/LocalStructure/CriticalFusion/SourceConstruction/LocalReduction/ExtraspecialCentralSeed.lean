module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialSpanFaithful
public import Theory.Representation.PSL3Two.CoreCentralSeed
public import Theory.Representation.BinaryConjugationSection.SubspacePreimages

/-!
# A central seed in the original faithful core branch

The marked Fano core contains a nonzero fixed displacement for L₁.
Lift its displacement through the literal R/V coordinates. It belongs to
O₂(K) and the upper chief endpoint. Its image in the faithful chief plane
is fixed by L₁, hence zero, so it belongs to the lower endpoint as well.
The cubic norm on E/V proves that this lift lies outside U.

Taking the fixed-space preimage and intersecting the original endpoints
produces C ≤ O₂(K) with C not contained in U, [C,L₁] ≤ V and [C,K] ≤ U.
The actual original-group application assumes only the faithful branch
of the already proved 14.7.23 alternatives and the named earlier inputs.

Source: Aschbacher–Smith 14.7.25, printed pp.1051–1052, refs/quasithin.pdf.
The faithful central-subgroup application is in ExtraspecialCentralSubgroup;
the central branch of 14.7.24 and maximal-normalizer control remain separate.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source NoncentralChiefRefinement
open Chapter14.Section04.LargerDimension.LocalAction.Components
open BinaryLinearThree.ParabolicCyclic.ChiefCounts
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem centralSeed_point_image
    (q : L →* BinaryLinearThree.Group)
    (hP : (F.H.subgroupOf L).map q = Matrix.PSL3Two.lineParabolicSL) :
    ((F.Li L 1).subgroupOf L).map q = actor := by
  have he : (F.Li L 1).subgroupOf L =
      (pResidual 2 (F.H.subgroupOf L)).map (F.H.subgroupOf L).subtype := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le ((F.Li_le L 1).trans inf_le_left),
      map_embedded_pResidual,subgroupOf_map_subtype]
    simp only [InvariantFlag.Li,show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) by decide,↓reduceIte]
    change (pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype = _
    rw [inf_comm]
  rw [he,map_embedded_pResidual,hP]
  rfl

/-- The faithful core alternative supplies an actual subgroup outside U,
inside both the residual two-core and the lower central flank, whose
point-residual displacement lies in V. -/
theorem extraspecial_faithful_central_seed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (hnc : ¬ ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U) :
    ∃ C : Subgroup G, C ≤ (K F).pCoreIn 2 ∧ ¬ C ≤ F.U ∧
      C ≤ conjugateSpanBy ⁅F.U,Q T L⁆ L ∧
      ⁅C,F.Li L 1⁆ ≤ V ∧ ⁅C,K F⁆ ≤ F.U := by
  obtain ⟨X,ha,hm,τ,s,e,σ,_,hσ,_,hP,_,hc | ⟨⟨ec⟩,_,_,N,B,hNB,hUN,hBC,hmov,_,_,hupper,hlower⟩⟩ :=
    extraspecial_span_two_module_alternatives h hab structural previous faithful he
  · exact (hnc hc.1).elim
  let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
  let q := e.symm.toMonoidHom.comp (SpanMarking.qL h)
  let j : F.Li L 1 →* (L ⊔ (T : Subgroup G) : Subgroup G) :=
    inclusion (((F.Li_le L 1).trans inf_le_left).trans le_sup_left)
  have hmap := centralSeed_point_image q hP
  have hq (a : F.Li L 1) : q ⟨a,(F.Li_le L 1 a.property).1⟩ ∈ actor := by
    rw [←hmap]
    exact ⟨⟨a,(F.Li_le L 1 a.property).1⟩,a.property,rfl⟩
  have hact (a : F.Li L 1) (v : X) :
      ec (τ (j a) v) = BinaryLinearThree.U₂ (q ⟨a,(F.Li_le L 1 a.property).1⟩) (ec v) := by
    have hh := congrArg (fun ψ : Representation (ZMod 2) L X =>
      ψ ⟨a,(F.Li_le L 1 a.property).1⟩ v) hσ
    change σ (q ⟨a,(F.Li_le L 1 a.property).1⟩) v = τ (j a) v at hh
    exact (congrArg ec hh.symm).trans (IntertwiningMap.isIntertwining _ _ ec.toIntertwiningMap _ _)
  obtain ⟨v,w,a,hv,hfix,hdisp⟩ := BinaryLinearThree.core_exists_fixed_displacement
  let v' := ec.symm v
  let w' := ec.symm w
  have hv' : v' ≠ 0 := by
    intro hh
    apply hv
    have := congrArg ec hh
    simpa only [v',ec.apply_symm_apply,map_zero] using this
  have hfixed (b : F.Li L 1) : τ (j b) v' = v' := by
    apply ec.toLinearEquiv.injective
    change ec (τ (j b) v') = ec v'
    rw [hact,ec.apply_symm_apply,hfix ⟨_,hq b⟩]
  have ham : (a : BinaryLinearThree.Group) ∈ ((F.Li L 1).subgroupOf L).map q := by
    rw [hmap]
    exact a.property
  obtain ⟨aL,haL,haq⟩ := ham
  let a₁ : F.Li L 1 := ⟨aL,haL⟩
  have hdisplacement : τ (j a₁) w' - w' = v' := by
    apply ec.toLinearEquiv.injective
    change ec (τ (j a₁) w' - w') = ec v'
    rw [map_sub,hact,ec.apply_symm_apply,ec.apply_symm_apply]
    change BinaryLinearThree.U₂ (q aL) w - w = v
    rw [haq]
    exact hdisp
  have hvcomm : v' ∈ s.imageSpace ⁅F.Li L 1,R⁆ := by
    rw [s.imageSpace_commutator (F.Li L 1) R
      (((F.Li_le L 1).trans inf_le_left).trans le_sup_left) le_rfl,s.imageSpace_self]
    exact Submodule.subset_span ⟨j a₁,a₁.property,w',Submodule.mem_top,hdisplacement.symm⟩
  obtain ⟨x,hxcomm,hxcoord⟩ := (s.mem_imageSpace_iff ⁅F.Li L 1,R⁆ v').mp hvcomm
  obtain ⟨c,hs,_,_,_,_,_,_,_,_,_,_,hRC,_,hinter,_⟩ :=
    extraspecial_span_source_reduction h hab structural previous faithful he
  have hxB : (x:G) ∈ B.val.map F.H.subtype := by
    apply hupper
    rw [commutator_comm] at hxcomm
    exact commutator_mono (hRC.trans inf_le_right) (pointResidual_le F) hxcomm
  have hRP : ⁅R,F.Li L 1⁆ ≤ (K F).pCoreIn 2 := by
    have hRH : R ≤ F.H := hRC.trans inf_le_left
    have hRK : R ≤ normalizer (K F : Set G) := hRH.trans (H_normalizes_K F)
    have hcommK : ⁅R,K F⁆ ≤ K F := le_normalizer_iff_commutator_le_right.mp hRK
    have hRcore : R ≤ F.H.pCoreIn 2 := by
      let := h.chosen.elementary
      let := hab
      let := elementary_U F
      obtain ⟨ρ,⟨sU⟩⟩ := exists_section F
      exact (hRC.trans inf_le_right).trans
        (centralizer_U_le_core_of_escape h structural (h.flag_escape F previous) sU)
    apply le_trans _ (inf_pCoreIn_le_of_le 2 (show K F ≤ F.H from map_subtype_le _))
    apply le_inf
    · exact (commutator_mono le_rfl (pointResidual_le F)).trans hcommK
    · exact (commutator_mono hRcore le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp
          (((F.Li_le L 1).trans inf_le_right).trans
            (F.H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H)))))
  have hxP : (x:G) ∈ (K F).pCoreIn 2 := by
    apply hRP
    rwa [commutator_comm]
  have hxN : (x:G) ∈ N.val.map F.H.subtype := by
    let C := (centralizer (F.U : Set G)).subgroupOf F.H
    let := h.chosen.elementary
    let := hab
    let := elementary_U F
    obtain ⟨ρU,⟨sU⟩⟩ := exists_section F
    have hC : IsPGroup 2 C :=
      ((isPGroup_pCoreIn 2 F.H).to_le
        (centralizer_U_le_core_of_escape h structural (h.flag_escape F previous) sU)).comap_subtype
    have hBC' : B.val ≤ C := fun b hb => hBC (mem_map_of_mem F.H.subtype hb)
    let : IsElementaryAbelian 2 (Section N B) := chief_elementary N B hNB (hC.to_le hBC')
    let ρ := binarySectionRepresentation N B
    let : ρ.IsIrreducible := binarySection_irreducible N B hNB
    let t := ambientBinarySection F.H N B hNB.le
    have hVN : V ≤ N.val.map F.H.subtype := (le_conjugateSpanBy V F.H).trans hUN
    obtain ⟨_,_,hfree⟩ := extraspecial_faithful_chief_span_plane
      h hab structural previous faithful he hBC hUN t hmov c hs
    apply (t.coordinates_eq_one_iff ⟨x,hxB⟩).mp
    apply hfree
    · exact (t.mem_imageSpace_iff R _).mpr ⟨⟨x,hxB⟩,x.property,rfl⟩
    · intro b
      apply (t.fixed_coordinate_iff_commutator_mem (inclusion ((F.Li_le L 1).trans inf_le_right) b) ⟨x,hxB⟩).mpr
      apply hVN
      apply (s.fixed_coordinate_iff_commutator_mem (j b) x).mp
      rw [hxcoord]
      exact hfixed b
  have hxU : (x:G) ∉ F.U := by
    intro hx
    obtain ⟨b,hb,hnorm⟩ := extraspecial_span_plane_cubic_norm h hab structural previous he s
    have him : v' ∈ s.imageSpace ⁅F.U,Q T L⁆ := by
      apply (s.mem_imageSpace_iff _ _).mpr
      exact ⟨x,hinter.le ⟨hx,x.property⟩,hxcoord⟩
    have hbfix : τ b v' = v' := hfixed ⟨b,hb⟩
    have hh := hnorm v' him
    rw [hbfix,hbfix] at hh
    have htwo : v'+v'=0 := by
      calc v'+v' = (2 : ZMod 2) • v' := (two_smul (ZMod 2) v').symm
           _ = 0 := by simp
    exact hv' (by simpa only [htwo,zero_add] using hh)
  let I := fixedSpace τ ((F.Li L 1).subgroupOf (L ⊔ (T : Subgroup G)))
  let C := s.subspacePreimage I ⊓ N.val.map F.H.subtype ⊓ (K F).pCoreIn 2
  have hxC : (x:G) ∈ C := by
    refine ⟨⟨(s.mem_subspacePreimage I x).mpr ⟨x.property,?_⟩,hxN⟩,hxP⟩
    intro b
    rw [hxcoord]
    exact hfixed ⟨b.val,b.property⟩
  refine ⟨C,inf_le_right,(fun hc => hxU (hc hxC)),
    (inf_le_left.trans inf_le_left).trans (s.subspacePreimage_le I),?_,?_⟩
  · rw [commutator_comm]
    apply s.commutator_le_of_imageSpace_fixed (F.Li L 1) C
      (((F.Li_le L 1).trans inf_le_left).trans le_sup_left)
      ((inf_le_left.trans inf_le_left).trans (s.subspacePreimage_le I))
    exact (s.imageSpace_mono (inf_le_left.trans inf_le_left)).trans
      (s.imageSpace_subspacePreimage I).le
  · exact (commutator_mono (inf_le_left.trans inf_le_right) le_rfl).trans hlower

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
