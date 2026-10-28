module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourFixedKernels
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceThreeGenerators
public import Theory.Representation.SymplecticFourOrthogonalCover.RootOverlap

/-!
# The centralizer of the common critical-overlap section

For an actual order-q critical image, source (3)'s equal overlap indices
identify Z intersect Z' with the full centralizer of either layer in the
other. The fixed midpoint supplement contributes no displacement, so the
movement of that common overlap is computed on the original moving cover.

An actor centralizing the overlap modulo the common critical displacement
acts on the root-fixed hyperplane through a point radical. In the universal
orthogonal cover its displacement has zero central coordinate. Descent to
the original cover proves that this displacement is disjoint from the
entire fixed attachment, including in the maximal-cover case. Applying the
same calculation in the reverse orientation retains both full attachments.

The final theorem constructs the literal centralizer inside the common
radical by its quotient action, and gives its exact membership criterion.
This is the shared centralizer in MS93 (3.7)(4), printed p.875. The lower
bound identifying its movement with the whole root-overlap complement,
the order-q-squared critical case, and source (5)/(6) remain necessary for
the field restriction. No degree-two or block recognition is asserted.

The local point-radical and root-coordinate proofs adapt the existing
SymplecticFourOrthogonalCover.HyperplaneMovement calculations; all uses of
RootOverlap keep the literal projection and the full covering kernel.
-/

public noncomputable section
open Matrix Subgroup Representation Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
open Representation.SymplecticFourOrthogonalCover
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
section Model
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {σ : Representation (ZMod 2) (L (K := F)) W}
omit [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
private theorem point_radical_of_hyperplane_movement (g : Sp F)
    (hfix : g • e (F := F) 0=e 0)
    (hmove : ∀ v : Vector F, v (.inr 0)=0 → g • v-v ∈ point F) :
    g ∈ pointRadicalAmbient := by
  let g' : pointLocal (F := F) := ⟨g,(mem_pointLocal_iff_fixed g).mpr hfix⟩
  refine ⟨g',?_,rfl⟩
  change pointQuotient g'=1
  apply Subtype.ext
  ext i j
  have hj : (Pi.single (middleIndex j) (1:F) : Vector F) (.inr 0)=0 := by
    fin_cases j <;> simp [middleIndex]
  have hm := (mem_point_iff _).mp (hmove (Pi.single (middleIndex j) 1) hj)
  have he : ((g • (Pi.single (middleIndex j) (1:F) : Vector F)-Pi.single (middleIndex j) 1 : Vector F))
      (middleIndex i)=0 := by
    fin_cases i
    · exact hm.1
    · exact hm.2 1
  change pointQuotientMatrix g' i j=(1 : Matrix (Fin 2) (Fin 2) F) i j
  fin_cases i <;> fin_cases j <;>
    simpa [pointQuotientMatrix,middleIndex,Theory.SpecificGroups.SymplecticFour.smul_eq_mulVec,Matrix.mulVec_single,
      g',sub_eq_zero] using he

private theorem standard_root_fixed_iff
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (Y T : Subgroup G) (hTY : T ≤ Y) (β : Y →* L (K := F))
    (hact : ∀ (y : Y) (w : W), j (Multiplicative.ofAdd (σ (β y) w)) =
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹)
    (hT : ((β.comp (inclusion hTY)).range.map (commutator (Sp F)).subtype)=RootSubgroup.group 0)
    (w : W) : j (Multiplicative.ofAdd w) ∈ centralizer (T : Set G) ↔
      p w ∈ (form F).orthogonal (point F) := by
  rw [←PointRadicalAction.root_displacement,orthogonal_displacementSpace]
  constructor
  · intro hw a ha
    obtain ⟨_,⟨t,rfl⟩,ht⟩ := hT.symm ▸ ha
    have he : σ (β (inclusion hTY t)) w=w := by
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hact]
      change t.val*j (Multiplicative.ofAdd w)*t.val⁻¹=_
      rw [hw t.val t.property,mul_inv_cancel_right]
    have he' := congrArg p he
    rw [p.isIntertwining] at he'
    exact ht ▸ he'
  · intro hw t ht
    have hmem : (β (inclusion hTY ⟨t,ht⟩)).val ∈ RootSubgroup.group 0 :=
      hT ▸ mem_map_of_mem _ (show β (inclusion hTY ⟨t,ht⟩) ∈
        (β.comp (inclusion hTY)).range from ⟨_,rfl⟩)
    have he := congrArg (fun w => j (Multiplicative.ofAdd w))
      (cover_fixed_of_projection_fixed p hp (β (inclusion hTY ⟨t,ht⟩)) w (hw _ hmem))
    rw [hact,mul_inv_eq_iff_eq_mul] at he
    exact he

private theorem embedded_standard_overlap_disjoint
    (hF : 2 < Nat.card F)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (Y T B : Subgroup G) (hTY : T ≤ Y) (hBY : B ≤ Y)
    (β : Y →* L (K := F))
    (hact : ∀ (y : Y) (w : W), j (Multiplicative.ofAdd (σ (β y) w)) =
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹)
    (hT : ((β.comp (inclusion hTY)).range.map (commutator (Sp F)).subtype)=RootSubgroup.group 0)
    (hfix : ∀ b : B, (β (inclusion hBY b)).val • e (F := F) 0=e 0)
    (hmove : ⁅j.range ⊓ centralizer (T : Set G),B⁆ ≤ ⁅T,j.range⁆) :
    Disjoint (⁅j.range ⊓ centralizer (T : Set G),B⁆)
      (p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j) := by
  let P := (((point F).restrictScalars (ZMod 2)).comap p.toLinearMap).toAddSubgroup.toSubgroup.map j
  have hRP : ⁅T,j.range⁆ ≤ P := by
    apply commutator_le.mpr
    intro b hb u hu
    obtain ⟨w,rfl⟩ := hu
    refine ⟨Multiplicative.ofAdd (σ (β (inclusion hTY ⟨b,hb⟩)) w.toAdd-w.toAdd),?_,?_⟩
    · change p (σ (β (inclusion hTY ⟨b,hb⟩)) w.toAdd-w.toAdd) ∈ point F
      rw [map_sub,p.isIntertwining]
      have hb' : (β (inclusion hTY ⟨b,hb⟩)).val ∈ RootSubgroup.group 0 :=
        hT ▸ mem_map_of_mem _ (show β (inclusion hTY ⟨b,hb⟩) ∈
          (β.comp (inclusion hTY)).range from ⟨_,rfl⟩)
      obtain ⟨t,ht⟩ := (RootSubgroup.mem_group_iff 0 _).mp hb'
      change rootElement 0 t=(β (inclusion hTY ⟨b,hb⟩)).val at ht
      change (β (inclusion hTY ⟨b,hb⟩)).val.val *ᵥ p w.toAdd-p w.toAdd ∈ point F
      rw [←ht,Roots.natural_root,add_sub_cancel_left]
      exact Submodule.mem_span_singleton.mpr ⟨_,rfl⟩
    · rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
      rfl
  have hpoint (b : B) : (β (inclusion hBY b)).val ∈ pointRadicalAmbient := by
    apply point_radical_of_hyperplane_movement _ (hfix b)
    intro v hv
    obtain ⟨w,rfl⟩ := hp.1 v
    have hw : j (Multiplicative.ofAdd w) ∈ j.range ⊓ centralizer (T : Set G) := by
      refine ⟨⟨_,rfl⟩,(standard_root_fixed_iff p hp j hj Y T hTY β hact hT w).mpr ?_⟩
      intro v hv'
      obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hv'
      simp [form_apply,Theory.SpecificGroups.SymplecticFour.e,hv]
    have hm : ⁅b.val,j (Multiplicative.ofAdd w)⁆ ∈ P := by
      apply hRP
      apply hmove
      rw [commutator_comm]
      exact commutator_mem_commutator b.property hw
    obtain ⟨u,hu,he⟩ := hm
    have hu' : u=Multiplicative.ofAdd (σ (β (inclusion hBY b)) w-w) := by
      apply hj
      rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
      exact he
    rw [hu'] at hu
    change p (σ (β (inclusion hBY b)) w-w) ∈ point F at hu
    rwa [map_sub,p.isIntertwining] at hu
  obtain ⟨s,hs,hsmove,_⟩ := cover_point_overlap hF p hp
  let f : Multiplicative F →* G := j.comp s.toAddMonoidHom.toMultiplicative
  have hbound : ⁅j.range ⊓ centralizer (T : Set G),B⁆ ≤ f.range := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro b hb u hu
    obtain ⟨w,rfl⟩ := hu.1
    have hw := (standard_root_fixed_iff p hp j hj Y T hTY β hact hT w.toAdd).mp hu.2
    have hw0 : (p w.toAdd) (.inr 0)=0 := by
      have hh := hw (e 0) (Submodule.subset_span (Set.mem_singleton _))
      simpa [form_apply,Theory.SpecificGroups.SymplecticFour.e] using hh
    obtain ⟨t,ht⟩ := hsmove (β (inclusion hBY ⟨b,hb⟩)) (hpoint ⟨b,hb⟩) w.toAdd hw0
    refine ⟨Multiplicative.ofAdd t,?_⟩
    change j (Multiplicative.ofAdd (s t))=_
    rw [ht,ofAdd_sub,map_div,div_eq_mul_inv,hact]
    rfl
  apply Disjoint.mono_left hbound
  apply disjoint_iff_inf_le.mpr
  rintro x ⟨⟨t,ht⟩,⟨w,hw,he⟩⟩
  have htw : s t.toAdd=w.toAdd := congrArg Multiplicative.toAdd (hj (ht.trans he.symm))
  have ht0 : t.toAdd=0 := by
    have hh := congrArg (fun v => (p v) (.inl 0)) htw
    rw [hs,show p w.toAdd=0 from hw] at hh
    simpa [ClassicalOrthogonal.e] using hh
  change x=1
  rw [←ht]
  change j (Multiplicative.ofAdd (s t.toAdd))=1
  simp only [ht0,map_zero,ofAdd_zero,map_one]
private theorem standard_root_preimage_displacement
    (hF : 2 < Nat.card F)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (Y T : Subgroup G) (hTY : T ≤ Y)
    (β : Y →* L (K := F))
    (hact : ∀ (y : Y) (w : W), j (Multiplicative.ofAdd (σ (β y) w)) =
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹)
    (hT : ((β.comp (inclusion hTY)).range.map (commutator (Sp F)).subtype)=RootSubgroup.group 0)
    (w : W) (hw : p w ∈ point F) : j (Multiplicative.ofAdd w) ∈ ⁅T,j.range⁆ := by
  have hw' : w ∈ Coinvariants.ker (σ.comp Roots.group.subtype) :=
    (Roots.cover_root_geometry hF p hp).2.1 ▸ hw
  clear hw
  induction hw' using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨⟨a,v⟩,rfl⟩ := hw
    obtain ⟨_,⟨t,rfl⟩,ht⟩ := (show a.val.val ∈
        (β.comp (inclusion hTY)).range.map (commutator (Sp F)).subtype from hT.symm ▸ a.property)
    have he : β (inclusion hTY t)=a.val := Subtype.ext ht
    change j (Multiplicative.ofAdd (σ a.val v-v)) ∈ ⁅T,j.range⁆
    rw [ofAdd_sub,map_div,div_eq_mul_inv,←he,hact]
    exact commutator_mem_commutator t.property (show j (Multiplicative.ofAdd v) ∈ j.range from ⟨_,rfl⟩)
  | zero => simp only [ofAdd_zero,map_one,one_mem]
  | add x y _ _ hx hy =>
    rw [ofAdd_add,map_mul]
    exact (⁅T,j.range⁆).mul_mem hx hy
  | smul c v _ hv =>
    fin_cases c
    · change j (Multiplicative.ofAdd ((0 : ZMod 2) • v)) ∈ ⁅T,j.range⁆
      simp only [zero_smul,ofAdd_zero,map_one,one_mem]
    · change j (Multiplicative.ofAdd ((1 : ZMod 2) • v)) ∈ ⁅T,j.range⁆
      simpa only [one_smul] using hv

private theorem embedded_root_overlap_disjoint
    (hF : 2 < Nat.card F)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (Y T B : Subgroup G) (hTY : T ≤ Y) (hBY : B ≤ Y)
    (β : Y →* L (K := F))
    (hact : ∀ (y : Y) (w : W), j (Multiplicative.ofAdd (σ (β y) w)) =
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹)
    (hcard : Nat.card (β.comp (inclusion hTY)).range = Nat.card F)
    (hd : Module.finrank F (displacementSpace
      ((β.comp (inclusion hTY)).range.map (commutator (Sp F)).subtype)) = 1)
    (hrootquad : ∀ x ∈ (β.comp (inclusion hTY)).range.map (commutator (Sp F)).subtype,
      ∀ y ∈ (β.comp (inclusion hTY)).range.map (commutator (Sp F)).subtype,
        ∀ v : Vector F, x • (y • v-v)=y • v-v)
    (hcent : B ≤ centralizer ((⁅T,j.range⁆ : Subgroup G) : Set G))
    (hmove : ⁅j.range ⊓ centralizer (T : Set G),B⁆ ≤ ⁅T,j.range⁆) :
    Disjoint (⁅j.range ⊓ centralizer (T : Set G),B⁆)
      (p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j) := by
  have hcard' : Nat.card ((β.comp (inclusion hTY)).range.map (commutator (Sp F)).subtype)=Nat.card F := by
    rw [card_map_of_injective (commutator (Sp F)).subtype_injective,hcard]
  obtain ⟨g,hg⟩ := FourLongRoots.exists_conjugate_root_of_displacement_one _ hcard' hd hrootquad
  let gl : L (K := F) := ⟨g,by rw [Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top hF]; trivial⟩
  let β' := (MulAut.conj gl).toMonoidHom.comp β
  let j' := j.comp (σ gl⁻¹).toAddMonoidHom.toMultiplicative
  have hj' : Function.Injective j' := hj.comp
    (fun x y he => Multiplicative.toAdd.injective ((σ.apply_bijective gl⁻¹).1 (congrArg Multiplicative.toAdd he)))
  have hjr : j'.range=j.range := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top_of_surjective _
      (show Function.Surjective (σ gl⁻¹).toAddMonoidHom.toMultiplicative from fun w => by
        obtain ⟨v,hv⟩ := (σ.apply_bijective gl⁻¹).2 w.toAdd
        exact ⟨Multiplicative.ofAdd v,congrArg Multiplicative.ofAdd hv⟩),←MonoidHom.range_eq_map]
  have hact' (y : Y) (w : W) : j' (Multiplicative.ofAdd (σ (β' y) w)) =
      y.val*j' (Multiplicative.ofAdd w)*y.val⁻¹ := by
    change j (Multiplicative.ofAdd (σ gl⁻¹ (σ (gl*β y*gl⁻¹) w)))=_
    simp only [map_mul,Module.End.mul_apply,inv_self_apply]
    exact hact y (σ gl⁻¹ w)
  have hT' : ((β'.comp (inclusion hTY)).range.map (commutator (Sp F)).subtype)=RootSubgroup.group 0 := by
    rw [←hg]
    ext x
    constructor
    · rintro ⟨_,⟨t,rfl⟩,rfl⟩
      exact ⟨(β (inclusion hTY t)).val,mem_map_of_mem _ ⟨t,rfl⟩,rfl⟩
    · rintro ⟨_,⟨_,⟨t,rfl⟩,rfl⟩,rfl⟩
      exact ⟨β' (inclusion hTY t),⟨t,rfl⟩,rfl⟩
  have hfix (b : B) : (β' (inclusion hBY b)).val • e (F := F) 0=e 0 := by
    obtain ⟨w,hw⟩ := hp.1 (e (F := F) 0)
    have hm := standard_root_preimage_displacement hF p hp j' Y T hTY β' hact' hT'
      w (hw ▸ Submodule.subset_span (Set.mem_singleton _))
    rw [hjr] at hm
    have he : σ (β' (inclusion hBY b)) w=w := by
      apply Multiplicative.ofAdd.injective
      apply hj'
      rw [hact']
      change b.val*j' (Multiplicative.ofAdd w)*b.val⁻¹=_
      rw [←hcent b.property _ hm,mul_inv_cancel_right]
    have he' := congrArg p he
    rw [p.isIntertwining,hw] at he'
    exact he'
  have hk : p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j' =
      p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j := by
    apply le_antisymm
    · rintro x ⟨w,hw,rfl⟩
      refine ⟨Multiplicative.ofAdd (σ gl⁻¹ w.toAdd),?_,rfl⟩
      change p (σ gl⁻¹ w.toAdd)=0
      rw [p.isIntertwining,show p w.toAdd=0 from hw,map_zero]
    · rintro x ⟨w,hw,rfl⟩
      refine ⟨Multiplicative.ofAdd (σ gl w.toAdd),?_,?_⟩
      · change p (σ gl w.toAdd)=0
        rw [p.isIntertwining,show p w.toAdd=0 from hw,map_zero]
      · change j (Multiplicative.ofAdd (σ gl⁻¹ (σ gl w.toAdd)))=j w
        rw [inv_self_apply]
        rfl
  have hh := embedded_standard_overlap_disjoint hF p hp j' hj' Y T B hTY hBY
    β' hact' hT' hfix (by rwa [hjr])
  rwa [hjr,hk] at hh
end Model
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

set_option maxHeartbeats 400000 in
/-- Movement of the root-fixed part of U, when confined to the common
critical displacement, misses the complete component-fixed attachment. -/
theorem critical_overlap_movement_disjoint
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a) = 2^n)
    (B : Subgroup (FreeAmalgam d.radical)) (hB : B ≤ Q d.radical t)
    (hmove : ⁅U d.radical a ⊓ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)),B⁆ ≤
      ⁅Z d.radical a,Z d.radical z⁆) :
    Disjoint (⁅U d.radical a ⊓ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)),B⁆)
      (U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))) := by
  let := replacementComponent_normal h d
  let s := replacementMovedSection h d
  obtain ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d path.start_color
  have hFc : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  have hCtop : replacementComponent d = ⊤ := by
    let q := QuotientGroup.mk' (pCore 2 d.overgroup)
    have hh := congrArg (fun A : Subgroup d.overgroup => A.map q)
      (replacement_inner_of_positive h d g (by omega))
    rw [Subgroup.map_sup,show (pCore 2 d.overgroup).map q = ⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  let κC := κ.codRestrict (replacementComponent d) (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  have hγact (x : stabilizer d.radical a) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (γ x) w)) =
        x.val*j (Multiplicative.ofAdd w)*x.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC x))) w)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj x w
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  obtain ⟨haq,hzq⟩ := replacement_critical_indices_eq_field_of_small h d path (by omega) (by
    rw [hcritical]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith)
  have hZS : Z d.radical z ≤ stabilizer d.radical a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  let δ := κ.comp (inclusion hZS)
  have hδcard : Nat.card δ.range = Nat.card E.Carrier :=
    (Sp4Four.SourceComparison.quotient_image_card _ _ _ hZS κ hκQ).trans (hzq.trans hFc.symm)
  obtain ⟨β,hβcard,hβmark,hβ,hβdim,hβquad⟩ := inner_root_actor_of_field_index rev (by omega)
    (MSCentralOrbit.C_eq_Q d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d) z path.end_color)
    h.nonbinary hFc s e he (replacement_component_image_structure h d).2.2.2.2
    j hj hjr δ (fun x v => hconj (inclusion hZS x) v) hδcard (haq.trans hFc.symm)
  have hγβ : γ.comp (inclusion hZS)=β := by
    apply MonoidHom.ext
    intro x
    exact (congrArg e.groupEquiv
      (show κC (inclusion hZS x)=e.groupEquiv.symm (β x) from
        Subtype.ext (hβmark x).symm)).trans (e.groupEquiv.apply_symm_apply _)
  have hEF : 2 < Nat.card E.Carrier := by
    rw [hFc]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hcent : B ≤ centralizer
      ((⁅Z d.radical z,j.range⁆ : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
    rw [hjr,commutator_comm]
    exact hB.trans (full_radical_centralizes_critical_root h d path hb c c' hcritical).2.2.1
  have hm : ⁅j.range ⊓ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)),B⁆ ≤
      ⁅Z d.radical z,j.range⁆ := by
    rw [hjr,commutator_comm (Z d.radical z),←critical_displacement_eq_moving h d path hb hat hzt]
    exact hmove
  have hh := embedded_root_overlap_disjoint hEF (MovedSection.coverProjection s e) he j hj
    (stabilizer d.radical a) (Z d.radical z) B hZS (hB.trans c.edge_le) γ hγact
    (by rw [hγβ]; exact hβcard) (by rw [hγβ]; exact hβdim)
    (by rw [hγβ]; exact hβquad) hcent hm
  have hk : (MovedSection.coverProjection s e).toLinearMap.ker.toAddSubgroup.toSubgroup.map j =
      U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · rintro x ⟨v,hv,rfl⟩
      exact ⟨hjr ▸ ⟨v,rfl⟩,(hker v.toAdd).mp hv⟩
    · rintro x ⟨hx,hc⟩
      obtain ⟨v,rfl⟩ := hjr.symm ▸ hx
      exact ⟨v,(hker v.toAdd).mpr hc,rfl⟩
  rwa [hjr,hk] at hh
/-- The actual common overlap is the full centralizer of either critical
layer inside the other; no fixed supplement is removed. -/
theorem critical_common_overlap_eq_centralizer
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a)=2^n) :
    Z d.radical a ⊓ Z d.radical z =
      Z d.radical a ⊓ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) := by
  have hzQ := (g.omega_bound z path.end_color (by
    rw [g.distance_constant z path.end_color]; change 0 < g.b d.radical; omega)).trans
    (omegaCenter_le _)
  have hov := (source_three_of_field_critical h d g hb hsat path hat hzt c c' hcritical).2.2.2.1
  have hle : Z d.radical a ⊓ Z d.radical z ≤ Z d.radical a ⊓ Q d.radical z :=
    inf_le_inf_left _ hzQ
  have hm := relIndex_mul_relIndex (Z d.radical a ⊓ Z d.radical z)
    (Z d.radical a ⊓ Q d.radical z) (Z d.radical a) hle inf_le_left
  rw [inf_relIndex_left,inf_relIndex_left,hcritical,hov] at hm
  have hi : (Z d.radical a ⊓ Z d.radical z).relIndex (Z d.radical a ⊓ Q d.radical z)=1 := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < 2^n by positivity)
    simpa only [one_mul] using hm
  have he := le_antisymm hle (relIndex_eq_one.mp hi)
  rw [he]
  have hAZ : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (g.exists_critical a path.start_color) path.critical.1.le
  rw [←MSCentralOrbit.C_eq_Q d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d) z path.end_color]
  ext x
  exact ⟨fun hx => ⟨hx.1,hx.2.2⟩,fun hx => ⟨hx.1,hAZ hx.1,hx.2⟩⟩

/-- The common overlap includes the full fixed midpoint supplement. Its
movement under any subgroup of the actual edge radical is computed on U. -/
theorem critical_common_overlap_movement
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a)=2^n)
    (B : Subgroup (FreeAmalgam d.radical)) (hB : B ≤ Q d.radical t) :
    ⁅Z d.radical a ⊓ Z d.radical z,B⁆ =
      ⁅U d.radical a ⊓ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)),B⁆ := by
  rw [critical_common_overlap_eq_centralizer h d g hb hsat path hat hzt c c' hcritical]
  have hsub : U d.radical a ⊓ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) ≤
      Z d.radical a ⊓ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) :=
    fun x hx => ⟨U_le_Z a hx.1,hx.2⟩
  apply le_antisymm ?_ (commutator_mono hsub le_rfl)
  rw [commutator_comm _ B,commutator_comm _ B]
  apply commutator_le.mpr
  intro b hb' x hx
  have hxta : Z d.radical t ≤ Z d.radical a := Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat
  let := g.Z_elementary (by omega : 0 < g.b d.radical) a path.start_color
  have hnorm : Z d.radical t ≤ normalizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    (hxta.trans ((Z d.radical a).le_centralizer.trans (centralizer_le (U_le_Z a)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hxjoin : x ∈ U d.radical a ⊔ Z d.radical t := by
    rw [←Z_eq_moving_sup_edge_of_distance_two h d g hb path.start_color hat]
    exact hx.1
  rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hnorm] at hxjoin
  obtain ⟨u,hu,v,hv,rfl⟩ := hxjoin
  let := g.Z_elementary (by omega : 0 < g.b d.radical) z path.end_color
  have hvC : v ∈ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) :=
    (Z d.radical z).le_centralizer (Sp4Four.edge_Z_le_endpoint d.radical path.end_color hzt hv)
  have huC : u ∈ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) := by
    have hh := (centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).mul_mem
      hx.2 ((centralizer _).inv_mem hvC)
    simpa only [mul_inv_cancel_right] using hh
  have ht : color d.radical t=true := by
    have hn := adjacent_color_ne d.radical hat
    cases he : color d.radical t <;> simp_all [path.start_color]
  have hZt : Z d.radical t=omegaCenter (Q d.radical t) := by simp [Z,ht,edgeOmega]
  have hbv : Commute b v := by
    exact (mem_omegaCenter_iff.mp (hZt ▸ hv)).2.2 b (hB hb')
  rw [commutatorElement_mul_right_eq_mul_conj,
    commutatorElement_eq_one_iff_commute.mpr hbv]
  simpa only [mul_one,mul_inv_cancel,one_mul,mul_inv_cancel_right] using
    (commutator_mem_commutator hb' (show u ∈ U d.radical a ⊓ centralizer
      (Z d.radical z : Set (FreeAmalgam d.radical)) from ⟨hu,huC⟩))
omit [Group H] [Finite H] [Field F] [Finite F] [CharP F 2] h in
private theorem exists_section_centralizer
    {G : Type*} [Group G] (T V W : Subgroup G)
    (hVT : V ≤ T) (hcent : T ≤ centralizer (W : Set G)) :
    ∃ B : Subgroup G, B ≤ T ∧
      (∀ b : G, b ∈ B ↔ b ∈ T ∧ ∀ v ∈ V, ⁅b,v⁆ ∈ W) ∧ ⁅V,B⁆ ≤ W := by
  let N := W.subgroupOf T
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (hcent.trans (Subgroup.centralizer_le_normalizer _))
  let q := QuotientGroup.mk' N
  let B₀ := (centralizer ((V.subgroupOf T).map q : Set (T ⧸ N))).comap q
  let B := B₀.map T.subtype
  have hmem (b : G) : b ∈ B ↔ b ∈ T ∧ ∀ v ∈ V, ⁅b,v⁆ ∈ W := by
    constructor
    · rintro ⟨b,hb,rfl⟩
      refine ⟨b.property,?_⟩
      intro v hv
      let v' : T := ⟨v,hVT hv⟩
      have hc : Commute (q b) (q v') := (hb _ (mem_map_of_mem q hv)).symm
      have he : q ⁅b,v'⁆=1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_commute.mpr hc
      exact (show ⁅b,v'⁆ ∈ N from (QuotientGroup.eq_one_iff _).mp he)
    · rintro ⟨hb,hbv⟩
      refine ⟨⟨b,hb⟩,?_,rfl⟩
      rintro _ ⟨v,hv,rfl⟩
      have he : q ⁅(⟨b,hb⟩ : T),v⁆=1 := (QuotientGroup.eq_one_iff _).mpr (hbv v.val hv)
      rw [map_commutatorElement] at he
      exact (commutatorElement_eq_one_iff_commute.mp he).eq.symm
  refine ⟨B,map_subtype_le _,hmem,?_⟩
  rw [commutator_comm]
  apply commutator_le.mpr
  exact fun b hb v hv => ((hmem b).mp hb).2 v hv

/-- The literal centralizer of the common overlap modulo the common
critical displacement moves that overlap disjointly from both complete
fixed attachments. This is the symmetric centralizer in MS93 (3.7)(4). -/
theorem source_four_common_overlap_centralizer
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a)=2^n) :
    let V := Z d.radical a ⊓ Z d.radical z
    let W := ⁅Z d.radical a,Z d.radical z⁆
    let A := U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
    let A' := U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))
    ∃ B : Subgroup (FreeAmalgam d.radical), B ≤ Q d.radical t ∧
      (∀ b : FreeAmalgam d.radical,
        b ∈ B ↔ b ∈ Q d.radical t ∧ ∀ v ∈ V, ⁅b,v⁆ ∈ W) ∧
      ⁅V,B⁆ ≤ W ∧ Disjoint ⁅V,B⁆ A ∧ Disjoint ⁅V,B⁆ A' := by
  dsimp only
  have hZaT : Z d.radical a ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt d.radical a (g.exists_critical a path.start_color)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hat),
      g.distance_constant a path.start_color]
    change 1 < g.b d.radical
    omega
  have hcent := (full_radical_centralizes_critical_root h d path hb c c' hcritical).2.2.1
  rw [←critical_displacement_eq_moving h d path hb hat hzt] at hcent
  obtain ⟨B,hB,hmem,hm⟩ := exists_section_centralizer (Q d.radical t)
    (Z d.radical a ⊓ Z d.radical z) ⁅Z d.radical a,Z d.radical z⁆
    (inf_le_left.trans hZaT) hcent
  refine ⟨B,hB,hmem,hm,?_,?_⟩
  · have he := critical_common_overlap_movement h d g hb hsat path hat hzt c c' hcritical B hB
    rw [he] at hm ⊢
    exact critical_overlap_movement_disjoint h d path hb hat hzt c c' hcritical B hB hm
  · have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
    let rev : CriticalPath d.radical g z a :=
      { start_color := path.end_color
        walk := path.walk.reverse
        shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
        critical := critical_reverse d.radical g hedge a path.start_color
          (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
          z path.end_color path.critical }
    have hother := (replacement_critical_indices_eq_field_of_small h d path (by omega) (by
      rw [hcritical]
      have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
      nlinarith)).2
    rw [inf_comm] at hm ⊢
    rw [commutator_comm (Z d.radical a)] at hm
    have he := critical_common_overlap_movement h d g hb hsat rev hzt hat c' c hother B hB
    rw [he] at hm ⊢
    exact critical_overlap_movement_disjoint h d rev hb hzt hat c' c hother B hB hm

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
