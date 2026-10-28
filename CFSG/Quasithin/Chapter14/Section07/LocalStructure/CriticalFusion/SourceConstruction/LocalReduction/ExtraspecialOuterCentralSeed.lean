module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialOuterCore
public import Theory.Representation.PSL3Two.CoreCentralSeed
public import Theory.Representation.BinaryConjugationSection.SubspacePreimages

/-!
# The original central seed from the outer Core module

A nonzero fixed displacement in the marked Core lifts to [S,L₁] ≤ P.
Its coordinates in P/C_P(U) are L₁-fixed, so dual fixed-point vanishing
puts the lift in C_P(U). The cubic norm on U/E shows that it lies outside U.

The fixed-space preimage in S/R, intersected with C_P(U), therefore gives
an actual C ≤ P outside U with [C,L₁] ≤ R and [C,K] ≤ U. All quotient
maps are those of the original flag. ExtraspecialCentralCompletion applies
this seed to obtain the central subgroup without a recognition callback.

Source: Aschbacher–Smith 14.7.24(2), printed p.1051, refs/quasithin.pdf.
The genuine earlier implications retain their producers; their final
source discharge stays with qt-d-14775-source.
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

private theorem outerSeed_point_image
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

/-- The central branch supplies an actual subgroup outside U in C_P(U),
with the two commutator bounds used in the source central-subgroup argument. -/
theorem extraspecial_outer_central_seed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (hc : ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U) :
    ∃ C : Subgroup G, C ≤ (K F).pCoreIn 2 ∧ ¬ C ≤ F.U ∧
      C ≤ conjugateSpanBy F.U L ∧
      ⁅C,F.Li L 1⁆ ≤ conjugateSpanBy ⁅F.U,Q T L⁆ L ∧ ⁅C,K F⁆ ≤ F.U := by
  obtain ⟨X,ha,hm,τ,s,e,σ,_,hσ,_,hP,_,⟨ec⟩,_,_⟩ :=
    extraspecial_outer_core_of_central h hab structural previous faithful he hc
  let R := conjugateSpanBy F.U L
  let q := e.symm.toMonoidHom.comp (SpanMarking.qL h)
  let j : F.Li L 1 →* (L ⊔ (T : Subgroup G) : Subgroup G) :=
    inclusion (((F.Li_le L 1).trans inf_le_left).trans le_sup_left)
  have hmap := outerSeed_point_image q hP
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
  have hxP : (x : G) ∈ (K F).pCoreIn 2 := by
    apply extraspecial_outer_commutator_core h hab structural previous faithful he
    rwa [commutator_comm]
  obtain ⟨ee⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv ee.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr ee.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv ee).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  let P := (K F).pCoreIn 2
  let PC := P ⊓ centralizer (F.U : Set G)
  obtain ⟨Y,haY,hmY,ρU,sU,t,_,_,_⟩ := extraspecial_core_duality
    h hab structural previous hex hcard hexp P (Or.inr rfl)
  obtain ⟨_,_,hfree⟩ := extraspecial_core_outer_fixed_plane h hab structural previous faithful ⟨ee⟩ sU t
  have hxPC : (x : G) ∈ PC := by
    apply (t.coordinates_eq_one_iff ⟨x,hxP⟩).mp
    apply hfree
    intro b
    apply (t.fixed_coordinate_iff_commutator_mem
      (inclusion ((F.Li_le L 1).trans inf_le_right) b) ⟨x,hxP⟩).mpr
    have hxR : ⁅(x : G),(b : G)⁆ ∈ conjugateSpanBy ⁅F.U,Q T L⁆ L := by
      apply (s.fixed_coordinate_iff_commutator_mem (j b) x).mp
      rw [hxcoord]
      exact hfixed b
    refine ⟨?_,(hRC hxR).2⟩
    exact (le_normalizer_iff_commutator_le_left.mp
      (((F.Li_le L 1).trans inf_le_right).trans t.normalized))
      (commutator_mem_commutator hxP b.property)
  have hxU : (x : G) ∉ F.U := by
    intro hx
    obtain ⟨b,hb,hnorm⟩ := extraspecial_outer_plane_cubic_norm h hab structural previous faithful ⟨ee⟩ s
    have him : v' ∈ s.imageSpace F.U :=
      (s.mem_imageSpace_iff _ _).mpr ⟨x,hx,hxcoord⟩
    have hbfix : τ b v' = v' := hfixed ⟨b,hb⟩
    have hh := hnorm v' him
    rw [hbfix,hbfix] at hh
    have htwo : v'+v'=0 := by
      calc v'+v' = (2 : ZMod 2) • v' := (two_smul (ZMod 2) v').symm
           _ = 0 := by simp
    exact hv' (by simpa only [htwo,zero_add] using hh)
  let I := fixedSpace τ ((F.Li L 1).subgroupOf (L ⊔ (T : Subgroup G)))
  let C := s.subspacePreimage I ⊓ PC
  have hxC : (x : G) ∈ C := by
    refine ⟨(s.mem_subspacePreimage I x).mpr ⟨x.property,?_⟩,hxPC⟩
    intro b
    rw [hxcoord]
    exact hfixed ⟨b.val,b.property⟩
  refine ⟨C,inf_le_right.trans inf_le_left,(fun hh => hxU (hh hxC)),
    inf_le_left.trans (s.subspacePreimage_le I),?_,?_⟩
  · rw [commutator_comm]
    apply s.commutator_le_of_imageSpace_fixed (F.Li L 1) C
      (((F.Li_le L 1).trans inf_le_left).trans le_sup_left)
      (inf_le_left.trans (s.subspacePreimage_le I))
    exact (s.imageSpace_mono inf_le_left).trans (s.imageSpace_subspacePreimage I).le
  · exact (commutator_mono (inf_le_right.trans inf_le_right) le_rfl).trans hc

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
