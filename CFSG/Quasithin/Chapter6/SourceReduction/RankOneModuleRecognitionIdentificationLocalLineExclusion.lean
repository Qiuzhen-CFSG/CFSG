module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalCubicSylow
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFieldTransvections
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Theory.SpecificGroups.PSL3.FourScalar

/-!
# Excluding the moved-line branch on the original field-plane quotient

The G.3 block containing the conjugate four-group is subnormal through the
root-generated subgroup, and its full binary linear action is faithful.
Replacement selects a minimal offender inside that four-group. B.5 and the
actual field-centralizer component lift restrict the block to A5, PSL3(2),
or SL3(4). Its order and trivial center leave only PSL3(2).

The original residual cubic centralizes this component. On its full linear
moved space, the invertible commutant is trivial. The full component preimage
contains the original conjugate layer, so fixation contradicts the previously
proved three-subgroups claim, with the original quotient maps unchanged.
Thus the field plane and commutator plane are disjoint.

This proves the moved-line exclusion of 6.2.7. The remaining moved-plane
model exclusions and 6.2.8 graph escape are separate obligations. The
companion Chapter 12 module removes the disjointness premise from the actual
layer's plane-offender geometry and component classification.

Source: Aschbacher--Smith, 6.2.7, printed pp.682--683, using 6.2.4(4,6),
B.5 and the two-core specialization of G.3.1; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open BinaryLinear BinaryTransvectionGroups
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalFieldQuotientAction
open CFSG.Quasithin.ChapterB.QuasisimpleSource CFSG.Quasithin.ChapterB.SourceInduction
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalFieldQuotientAction

private theorem binary_full_quasisimple
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (hd : 3 ≤ Module.finrank (ZMod 2) W) :
    IsQuasisimple (BinaryLinear.GL W) ∧ center (BinaryLinear.GL W) = ⊥ := by
  let d := Module.finrank (ZMod 2) W
  let E := BinaryLinear.SmallParabolicLevi.linearGroupCongr
    (Module.finBasis (ZMod 2) W).equivFun
  let e := (BinaryLinear.OuterCyclic.slEquivLinear d).trans E.symm
  let : Group.IsPerfect (BinaryLinear.OuterCyclic.LinearGroup d) :=
    BinaryLinear.linearGroup_isPerfect d hd
  let : Group.IsPerfect (BinaryLinear.GL W) :=
    Group.IsPerfect.ofSurjective (f := E.symm.toMonoidHom) E.symm.surjective
  have hz : center (BinaryLinear.GL W) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hx1 := (BinaryLinear.OuterCyclic.binary_center_eq_bot (n := d) (by omega)).le
      ((centerCongr e).symm ⟨x,hx⟩).property
    exact e.symm.map_eq_one_iff.mp hx1
  let : IsSimpleGroup PSL(d,ZMod 2) := Atlas.psl_simple_high_rank d hd
  let : IsSimpleGroup (BinaryLinear.GL W) :=
    (E.trans (BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega : 0 < d)).symm).isSimpleGroup
  exact ⟨{ toIsPerfect := inferInstance
           simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup },hz⟩

private theorem line_component
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (I : Subgroup D) (hr : LineRecognition ρ I (moved ρ I)) :
    ∃ (K : Subgroup D) (C : Submodule (ZMod 2) W),
      IsComponent D K ∧ I ≤ K ∧ center K = ⊥ ∧
      3 ≤ Module.finrank (ZMod 2) C ∧
      ∃ e : K ≃* BinaryLinear.GL C,
        (∀ k : K, ∀ w : C, ((e k) w : W) = ρ k w) ∧
        moved ρ K = C := by
  let f : D →* BinaryLinear.GL W :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).toMonoidHom.comp ρ.asGroupHom
  have hfi : Function.Injective f := by
    intro a b he
    apply hf
    ext w
    exact congrArg (fun g : BinaryLinear.GL W => g w) he
  obtain ⟨x,hx,hline,hI,hcore,hG3,hfull,_,hlocal⟩ := hr
  let Δ := MulAction.orbit f.range x
  let i : ChapterG.Section03.OrbitBlock f.range Δ :=
    ⟨MulAction.orbit (generated f.range Δ) x,x,MulAction.mem_orbit_self x,rfl⟩
  let K0 := ChapterG.Section03.blockGroup f.range Δ i
  let N0 := generated f.range Δ
  let C := ChapterG.Section03.blockSpace f.range Δ i
  have hK0N : K0 ≤ N0 := ChapterG.Section03.blockGroup_le_generated hG3 i
  have hK0f : K0 ≤ f.range := generated_le f.range i.val
  let K := K0.comap f
  let fK : K →* K0 := {
    toFun k := ⟨f k,k.property⟩
    map_one' := Subtype.ext (map_one f)
    map_mul' a b := Subtype.ext (map_mul f (a : D) (b : D)) }
  have hfK : Function.Bijective fK := by
    constructor
    · intro a b hab
      exact Subtype.ext (hfi (congrArg Subtype.val hab))
    · intro k
      obtain ⟨a,ha⟩ := hK0f k.property
      exact ⟨⟨a,by change f a ∈ K0; rw [ha]; exact k.property⟩,Subtype.ext ha⟩
  let e0 := MulEquiv.ofBijective fK hfK
  let e1 : K0 ≃* BinaryLinear.GL C := MulEquiv.ofBijective (spanAction f.range i.val)
    ⟨ChapterG.Section03.Reduced.blockAction_injective hG3 hcore i,hfull.surjective i⟩
  let e := e0.trans e1
  have hdim : 3 ≤ Module.finrank (ZMod 2) C := hlocal.dimension_ge_three i
  obtain ⟨hq,hz⟩ := binary_full_quasisimple hdim
  let := hq
  have hKq : IsQuasisimple K := IsQuasisimple.of_mulEquiv e.symm
  have hKs : K.IsSubnormal := by
    let N := N0.subgroupOf f.range
    let K1 := K0.subgroupOf f.range
    have hn0 : N0 ≤ normalizer (K0 : Set (BinaryLinear.GL W)) :=
      (normal_subgroupOf_iff_le_normalizer hK0N).mp (ChapterG.Section03.Reduced.block_normal hG3 i)
    have hn1 : N ≤ normalizer (K1 : Set f.range) := by
      intro a ha
      rw [←subgroupOf_normalizer_eq hK0f]
      exact hn0 ha
    have hs : K1.IsSubnormal := IsSubnormal.step K1 N (subgroupOf_mono _ hK0N)
      (generated_normal f.range Δ hG3.stable).isSubnormal
      (normal_subgroupOf_of_le_normalizer hn1)
    exact hs.comap f.rangeRestrict
  have hIK : I ≤ K := by
    intro a ha
    exact rootGroup_le_generated f.range (MulAction.mem_orbit_self x)
      (hI (mem_map_of_mem f ha))
  have hKz : center K = ⊥ := by
    apply le_bot_iff.mp
    intro k hk
    exact e.map_eq_one_iff.mp (hz.le ((centerCongr e) ⟨k,hk⟩).property)
  refine ⟨K,C,⟨hKs,hKq⟩,hIK,hKz,hdim,e,?_,?_⟩
  · intro k w
    rfl
  · apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨k,hk,w,_,rfl⟩
      exact generated_le_quotientFixer f.range i.val hk w
    · apply Submodule.span_le.mpr
      intro y hy
      have hr : rootGroup f.range y ≠ ⊥ := by
        intro he
        have hh := ChapterG.Section03.Reduced.source_large_roots hG3
          (ChapterG.Section03.block_subset hG3 i hy)
        rw [he,card_bot] at hh
        omega
      obtain ⟨t,ht⟩ := ne_bot_iff_exists_ne_one.mp hr
      have htne : (t : BinaryLinear.GL W) ≠ 1 := fun he => ht (Subtype.ext he)
      obtain ⟨w,hw⟩ : ∃ w : W, t.val w ≠ w := by
        by_contra hn
        push Not at hn
        exact htne (LinearEquiv.ext hn)
      have hdisp : t.val w - w = y :=
        ((mem_centerLine_iff y _).mp (t.property.2.2 w)).resolve_left
          (sub_ne_zero.mpr hw)
      obtain ⟨k,hk⟩ := hfK.surjective ⟨t,rootGroup_le_generated f.range hy t.property⟩
      have hfkt : f k = t.val := congrArg Subtype.val hk
      rw [←hdisp,←hfkt]
      exact Submodule.subset_span ⟨k,k.property,w,Submodule.mem_top,rfl⟩


private theorem binary_full_card_ge
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (hd : 3 ≤ Module.finrank (ZMod 2) W) : 168 ≤ Nat.card (BinaryLinear.GL W) := by
  let d := Module.finrank (ZMod 2) W
  let X := Fin 3 → ZMod 2
  let Y := Fin (d-3) → ZMod 2
  let j : BinaryLinear.GL X →* BinaryLinear.GL (X × Y) := {
    toFun a := a.prodCongr (LinearEquiv.refl (ZMod 2) Y)
    map_one' := by ext v <;> rfl
    map_mul' a b := by ext v <;> rfl }
  have hj : Function.Injective j := by
    intro a b hab
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun f : BinaryLinear.GL (X × Y) => (f (v,0)).1) hab
  let E : W ≃ₗ[ZMod 2] (X × Y) := LinearEquiv.ofFinrankEq _ _ (by
    simp only [X,Y,Module.finrank_prod,Module.finrank_pi,Fintype.card_fin]
    change d = 3 + (d - 3)
    omega)
  have hc : Nat.card (BinaryLinear.GL X) = 168 :=
    (Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.toEquiv).trans Matrix.PSL3Two.card_SL
  rw [←hc,Nat.card_congr (BinaryLinear.SmallParabolicLevi.linearGroupCongr E).toEquiv]
  exact Nat.card_le_card_of_injective j hj

private theorem binary_full_model
    {X W : Type*} [Group X] [Finite X] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (e : X ≃* BinaryLinear.GL W) (hd : 3 ≤ Module.finrank (ZMod 2) W)
    (hm : Nonempty (X ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (X ≃* PSL(3,ZMod 2)) ∨ Nonempty (X ≃* SL(3,BinaryField.four.Carrier))) :
    Nonempty (X ≃* PSL(3,ZMod 2)) := by
  rcases hm with hA | he | hS
  · obtain ⟨eA⟩ := hA
    have hc : Nat.card (BinaryLinear.GL W) = 60 := by
      rw [Nat.card_congr (e.symm.trans eA).toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    have hh := binary_full_card_ge hd
    omega
  · exact he
  · obtain ⟨eS⟩ := hS
    obtain ⟨z,ho,hz,_⟩ := Theory.SpecificGroups.PSL3.FourScalar.exists_central_cubic_moving
      (F := BinaryField.four.Carrier) BinaryField.four.card_eq
    let f := eS.symm.trans e
    have hf : f z = 1 := (binary_full_quasisimple hd).2.le ((centerCongr f) ⟨z,hz⟩).property
    have hz1 := f.map_eq_one_iff.mp hf
    rw [hz1,orderOf_one] at ho
    contradiction

private theorem full_moved_centralizer
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) D W)
    (K : Subgroup D) (C : Submodule (ZMod 2) W)
    (hd : 3 ≤ Module.finrank (ZMod 2) C)
    (e : K ≃* BinaryLinear.GL C)
    (he : ∀ k : K, ∀ w : C, ((e k) w : W) = ρ k w)
    (hm : moved ρ K = C) (δ : BinaryLinear.GL W)
    (hc : ∀ k : K, ∀ w : W, δ (ρ k w) = ρ k (δ w)) :
    ∀ w ∈ moved ρ K, δ w = w := by
  have hmaple : C.map δ.toLinearMap ≤ C := by
    rw [←hm]
    apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨k,hk,w,_,rfl⟩
    change δ (ρ k w - w) ∈ moved ρ K
    rw [map_sub,hc ⟨k,hk⟩]
    exact Submodule.subset_span ⟨k,hk,δ w,Submodule.mem_top,rfl⟩
  have hmap : C.map δ.toLinearMap = C := Submodule.eq_of_le_of_finrank_eq hmaple
    (LinearEquiv.finrank_map_eq δ C)
  let δC : BinaryLinear.GL C := δ.ofSubmodules C C hmap
  have hz : δC ∈ center (BinaryLinear.GL C) := by
    rw [mem_center_iff]
    intro a
    obtain ⟨k,rfl⟩ := e.surjective a
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    change ((e k) (δC w) : W) = δ ((e k) w)
    rw [he,he]
    exact (hc k w).symm
  have hδ : δC = 1 := (binary_full_quasisimple hd).2.le hz
  intro w hw
  have hwC : w ∈ C := hm ▸ hw
  exact congrArg (fun f : BinaryLinear.GL C => (f ⟨w,hwC⟩ : W)) hδ


private theorem section_component_contradiction
    {G D W : Type*} [Group G] [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    {H J U P A : Subgroup G} (hHP : H ≤ P) (hAH : A ≤ H)
    (π : H →* D) (hπ : Function.Surjective π)
    (ρ : Representation (ZMod 2) D W)
    (c : BinaryConjugationSection H J U (ρ.comp π))
    (η : Representation (ZMod 2) P W) (c' : BinaryConjugationSection P J U η)
    (hcoords : c'.coordinates = c.coordinates)
    (hr : ∀ a : H, η (inclusion hHP a) = ρ (π a))
    (d : P) (K : Subgroup D) (hAK : (A.subgroupOf H).map π ≤ K)
    (hc : ∀ k : K, Commute (η.asGroupHom d) (ρ.asGroupHom k))
    (hf : ∀ w ∈ moved ρ K, η d w = w)
    (hclaim : ∀ Q : Subgroup G, A ≤ Q → Q ≤ H →
      (⁅Q,zpowers (d : G)⁆.subgroupOf P).map η.asGroupHom = ⊥ →
      c'.imageSpace ⁅⁅J,Q⁆,zpowers (d : G)⁆ ≠ ⊥) : False := by
  let K0 := K.comap π
  let Q := K0.map H.subtype
  have hQH : Q ≤ H := map_subtype_le _
  have hQP : Q ≤ P := hQH.trans hHP
  have hAQ : A ≤ Q := by
    intro a ha
    exact ⟨⟨a,hAH ha⟩,hAK (mem_map_of_mem π ha),rfl⟩
  have hQsub : Q.subgroupOf H = K0 := by
    change (K0.map H.subtype).comap H.subtype = K0
    rw [comap_map_eq_self_of_injective H.subtype_injective]
  have hKmap : K0.map π = K := by
    exact map_comap_eq_self_of_surjective hπ K
  have hQsubP : Q.subgroupOf P = K0.map (inclusion hHP) := by
    apply map_injective P.subtype_injective
    rw [map_subgroupOf_eq_of_le hQP,map_map]
    rfl
  have hQimage : (Q.subgroupOf P).map η.asGroupHom = K.map ρ.asGroupHom := by
    rw [hQsubP,map_map]
    have he : η.asGroupHom.comp (inclusion hHP) = ρ.asGroupHom.comp π := by
      apply MonoidHom.ext
      intro a
      exact Units.ext (hr a)
    rw [he,←map_map,hKmap]
  have hDsub : (zpowers (d : G)).subgroupOf P = zpowers d := by
    apply map_injective P.subtype_injective
    rw [map_subgroupOf_eq_of_le (zpowers_le.mpr d.property),MonoidHom.map_zpowers]
    rfl
  have hcommSub : ⁅Q,zpowers (d : G)⁆.subgroupOf P =
      ⁅Q.subgroupOf P,zpowers d⁆ := by
    apply map_injective P.subtype_injective
    rw [map_subgroupOf_eq_of_le (Subgroup.commutator_le_sup Q _ |>.trans
      (sup_le hQP (zpowers_le.mpr d.property))),map_commutator,
      map_subgroupOf_eq_of_le hQP,MonoidHom.map_zpowers]
    rfl
  have hcomm : (⁅Q,zpowers (d : G)⁆.subgroupOf P).map η.asGroupHom = ⊥ := by
    rw [hcommSub,map_commutator,hQimage,MonoidHom.map_zpowers,commutator_comm]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply zpowers_le.mpr
    rintro _ ⟨k,hk,rfl⟩
    exact (hc ⟨k,hk⟩).eq.symm
  have hself : c.imageSpace J = ⊤ := by
    apply top_unique
    intro w _
    obtain ⟨j,hj⟩ := c.onto (Multiplicative.ofAdd w)
    exact (c.mem_imageSpace_iff _ _).mpr ⟨j,j.property,congrArg Multiplicative.toAdd hj⟩
  have hm : c'.imageSpace ⁅J,Q⁆ = moved ρ K := by
    have he : c'.imageSpace ⁅J,Q⁆ = c.imageSpace ⁅J,Q⁆ := by
      simp only [BinaryConjugationSection.imageSpace,hcoords]
    rw [he,commutator_comm J Q,c.imageSpace_commutator Q J hQH le_rfl,
      hself,subspaceCommutator_comp_map,hQsub,hKmap]
  apply hclaim Q hAQ hQH hcomm
  rw [commutator_comm ⁅J,Q⁆ _,c'.imageSpace_commutator _ _
    (zpowers_le.mpr d.property)
    (le_normalizer_iff_commutator_le_left.mp (hQP.trans c'.normalized)),hm,hDsub]
  apply (subspaceCommutator_eq_bot_iff η _ _).mpr
  intro w hw
  exact (mem_fixedSpace_zpowers_iff η d w).mpr (hf w hw)

/-- The actual field plane and commutator plane are disjoint in the contrary
one-sided configuration. This excludes the moved-line branch of source 6.2.7
using the original cubic and the literal quotient marking. -/
theorem one_sided_planes_disjoint
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N → N = M)
    (g : G)
    (hBA : layer L R ≤ normalizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (layer L R).map (MulAut.conj g).toMonoidHom ≤ centralizer (layer L R : Set G)) :
    (layer L R ⊓ centralizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G)) ⊓
      ⁅(layer L R).map (MulAut.conj g).toMonoidHom,layer L R⁆ = ⊥ := by
  by_contra hmeet
  let B := layer L R
  let A := B.map (MulAut.conj g).toMonoidHom
  let U := B ⊓ centralizer (A : Set G)
  let H := Centralizer U
  let J := conjugateSpanBy B H
  let P := H ⊔ fieldLocalResidual L U
  have hnat : IsNaturalModule L B n := hnatural.1 ▸ hnatural.2.1
  obtain ⟨hUc,hfield,hout⟩ := local_one_sided_field_plane h hnatural hE hfactor g hBA hnon
  let := (reduced_space h hnatural hE hfactor hfield hUc.ge).elementary
  let π := (action B U).rangeRestrict
  let I := (A.subgroupOf H).map π
  obtain ⟨ρ,c,hfaith,hI,hIc,hrec,_⟩ :=
    exists_line_recognition h hnatural hE hfactor g hBA hnon hmeet
  obtain ⟨_,hmoved,hdim,_,_,_⟩ := section_plane_geometry h hnatural hE hfactor g hBA hnon (W := Additive (space B U)) ρ c
  rw [←hmoved] at hrec
  obtain ⟨K,C,hK,hIK,hKz,hCd,eC,heC,hCm⟩ := line_component ρ hfaith I hrec
  obtain ⟨Q,hQI,hQ,_,_⟩ := hI.exists_quadratic_minimalBestOffender ρ
  have hQK : Q ≤ K := hQI.trans hIK
  have hKQ : ⁅K,Q⁆ = K := hK.commutator_eq_self_of_normalizes
    (hQK.trans K.le_normalizer) (by
      intro hzero
      apply hQ.1.1.1
      apply le_bot_iff.mp
      intro q hq
      have hc : q ∈ centralizer (K : Set (action B U).range) :=
        le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero) hq
      have hz : (⟨q,hQK hq⟩ : K) ∈ center K := by
        rw [mem_center_iff]
        intro k
        exact Subtype.ext (hc k k.property)
      exact congrArg Subtype.val (hKz.le hz))
  have hQdim : Module.finrank (ZMod 2) (moved ρ Q) ≤ 2 := by
    apply (Submodule.finrank_mono ?_).trans hdim
    apply Submodule.span_mono
    rintro _ ⟨q,hq,w,hw,rfl⟩
    exact ⟨q,hQI hq,w,hw,rfl⟩
  have hUne : U ≠ ⊥ := by intro he; change Nat.card U = 4 at hUc; rw [he,card_bot] at hUc; contradiction
  let cover : SQTKQuotient KnownSimple.IsKnownSimple (action B U).range := {
    Cover := H
    kernel := (action B U).ker
    sqtk := by
      have hs := local_field_normalizer_sqtk h hfield hUne
      let j := inclusion (Subgroup.centralizer_le_normalizer (U : Set G))
      exact ⟨hs.stronglyQuasithin.of_injective j (inclusion_injective _),
        hs.isKGroup.of_injective j (inclusion_injective _)⟩
    equiv := QuotientGroup.quotientKerEquivRange (action B U) }
  have hm := ChapterB.SourceInduction.component_actor_of_minimal_plane ρ hfaith
    (action_range_core h hnatural hE hfactor hfield hUc.ge) cover hK hQ hKQ hQdim
  obtain ⟨K0,hK0,_,eK0,_⟩ := action_component_lift h hnatural hE hfactor hu hfield hUc hout K hK
  have hm0 := local_field_component_small_actor h hnat hfield hUc K0 hK0
    (hm.of_mulEquiv eK0)
  have hmodels : Nonempty (K ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (K ≃* PSL(3,ZMod 2)) ∨ Nonempty (K ≃* SL(3,BinaryField.four.Carrier)) := by
    rcases hm0 with h0 | h0 | h0
    · exact Or.inl (h0.map (fun e => eK0.symm.trans e))
    · exact Or.inr (Or.inl (h0.map (fun e => eK0.symm.trans e)))
    · exact Or.inr (Or.inr (h0.map (fun e => eK0.symm.trans e)))
  obtain ⟨eK⟩ := binary_full_model eC hCd hmodels
  let : IsElementaryAbelian 2 J :=
    local_plane_closure_elementary h hnatural hE hfactor inf_le_left hUc.ge
  obtain ⟨d,hd,ho,hBD,η,c',hcoords,hrestrict,_⟩ := field_plane_cubic_section_action hnat hfield hUc c
  let dP : P := ⟨d,mem_sup_right hd⟩
  have hcomm := binary_component_cubic_commutes h hnatural hE hfactor hu hfield hUc hout
    K hK eK ρ η hrestrict d hd (ho ▸ pow_orderOf_eq_one d)
  let δ : BinaryLinear.GL (Additive (space B U)) :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) _ (η.asGroupHom dP)
  have hfix : ∀ w ∈ moved ρ K, η dP w = w :=
    full_moved_centralizer ρ K C hCd eC heC hCm δ (by
      intro k w
      exact congrArg (fun a : (Module.End (ZMod 2) (Additive (space B U)))ˣ => a.val w)
        (hcomm k).eq)
  have hAH : A ≤ H := le_centralizer_iff.mpr inf_le_right
  exact section_component_contradiction (show H ≤ P from le_sup_left) hAH π
    (action B U).rangeRestrict_surjective ρ c η c' hcoords hrestrict dP K hIK hcomm hfix
    (local_one_sided_cubic_section_noncentral h hnatural hE hfactor g hBA hnon η c' d hd hBD)

/-- The marked plane-offender action on the literal centralizer quotient,
with its fixed-space family and the three remaining component models. -/
@[expose] def PlaneSection {G : Type*} [Group G] [Finite G]
    (B A U : Subgroup G) [IsElementaryAbelian 2 (space B U)] : Prop :=
    let H := LocalFieldQuotientAction.Centralizer U
    let J := conjugateSpanBy B H
    let π := (LocalFieldQuotientAction.action B U).rangeRestrict
    let I := (A.subgroupOf H).map π
    ∃ (ρ : Representation (ZMod 2) (LocalFieldQuotientAction.action B U).range
        (Additive (LocalFieldQuotientAction.space B U)))
      (c : BinaryConjugationSection H J U (ρ.comp π)),
      Function.Injective ρ ∧ IsOffender ρ I ∧ IsQuadratic ρ I ∧ Nat.card I = 4 ∧
      moved ρ I = c.imageSpace ⁅A,B⁆ ∧ Module.finrank (ZMod 2) (moved ρ I) = 2 ∧
      fixedCodim ρ I = 2 ∧ I ∈ ChapterE.fixedSpaceFamily ρ 2 ∧
      IsMinimalBestOffender ρ I ∧
      (∀ K, IsComponent (LocalFieldQuotientAction.action B U).range K → ⁅K,I⁆ = K →
        IsIrrPlus ρ K (moved ρ K) ∧
          (Nonempty (K ≃* alternatingGroup (Fin 5)) ∨
            Nonempty (K ≃* PSL(3,ZMod 2)) ∨ Nonempty (K ≃* SL(3,BinaryField.four.Carrier)))) ∧
      ∀ j : J, ∃ hj : (j : G) ∈ H, LocalFieldQuotientAction.projection U ⟨j,hj⟩ =
        ((c.coordinates j).toAdd.toMul : LocalFieldQuotientAction.Ambient U)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalFieldQuotientAction
