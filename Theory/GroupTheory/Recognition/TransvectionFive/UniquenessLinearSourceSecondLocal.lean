module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceSecondCentralizer
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceSecondCentralizer
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceNativeFusion
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Intersections.Model
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceRectangleOrbits
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceRow
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceLocalIsomorphisms
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourcePlaneImage
public import Theory.GroupTheory.CentralizerSmallKernelTransport
/-!
# Completing the linear second-centralizer argument

The native rank-two involution is I + E₀₃ + E₁₄. Its centralizer preserves
its image, so it normalizes the original two-by-three rectangle. The existing
21- and 42-element rectangle orbits show that the full point centralizer is
strictly larger than this second centralizer. Thus any recognized carrier
isomorphism preserves the two marked involution classes.

The actual plane-normalizer comparison preserves every original rectangle
coordinate, in particular code 34. Comparing its restricted centralizer with
the full native centralizer now proves that C_L(t) normalizes the source plane,
where L is the normalizer-generated subgroup. The carrier isomorphism is used
only for this cardinal comparison; the local marking retains the original
plane and t. No simplicity of L or ambient generation is assumed.

Consequently the plane image is relatively normal in (L ∩ C_G(B))/B.
In the six-bit coordinates, an additive rank-one symmetry fixing t preserves
the common four-space. Its images of the prescribed points have the original
fusion types. A four-space calculation shows that their point-free four-group
is already the marked B, so the required transport has conjugator 1 in L.
These two fields discharge the existing fixed-coset arguments, ambient
generation, and the literal source geometry comparison.

Source: Aschbacher, *Sporadic Groups* (1994), 40.3 and 41.1, pp.217–220.
This argument uses the proved rectangle orbits rather than the later 3/12
quotient orbits. It requires no residual identification and makes no replacement
of the source's O²(I) by O₂(I).
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear
open PlaneTensor PlaneCensus

private theorem native_second_matrix : (planeSecondPoint nativeMarking).val =
    1 + Matrix.single 0 3 1 + Matrix.single 1 4 1 := by
  rw [planeSecondPoint, native_element_matrix]
  decide

private theorem native_second_lower (g : SL)
    (hg : g ∈ secondCentralizer nativeMarking) (i j : Fin 5)
    (hi : 2 ≤ i.val) (hj : j.val < 2) : g i j = 0 := by
  have he := congrArg (fun a : SL => a.val)
    (mem_centralizer_singleton_iff.mp hg)
  change g.val * (planeSecondPoint nativeMarking).val =
    (planeSecondPoint nativeMarking).val * g.val at he
  rw [native_second_matrix, Matrix.mul_add, Matrix.mul_add,
    Matrix.add_mul, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at he
  have he3 := congrFun (congrFun he i) 3
  have he4 := congrFun (congrFun he i) 4
  have hi0 : i ≠ 0 := by omega
  have hi1 : i ≠ 1 := by omega
  simp only [Matrix.add_apply, Matrix.mul_single_apply_same, mul_one] at he3 he4
  fin_cases j <;> simp_all

/-- The actual matrix second centralizer preserves the marked image plane. -/
theorem native_second_centralizer_le_plane_normalizer :
    secondCentralizer nativeMarking ≤ sourcePlaneNormalizer nativeMarking := by
  change secondCentralizer nativeMarking ≤ normalizer (nativeMarking.pullback Model.plane : Set SL)
  rw [nativeMarking_pullback Model.plane Model.plane_le_centralizer]
  apply normalizes_closure_of_generators
  rintro g hg _ ⟨i,j,hij,hi,hj,rfl⟩
  apply (RectangleCoordinates.mem2_iff _).mpr
  intro a b hab
  rw [UniquenessMathieu.SourceNormalizer.conjugate_root_entry]
  by_cases ha : a.val < 2
  · have hb : b.val < 2 := by omega
    rw [native_second_lower g⁻¹ ((secondCentralizer nativeMarking).inv_mem hg)
      j b hj hb, mul_zero, add_zero]
  · rw [native_second_lower g hg a i (by omega) hi, zero_mul, add_zero]


private theorem centralizer_card_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (a : A) :
    Nat.card (Subgroup.centralizer ({a} : Set A)) =
      Nat.card (Subgroup.centralizer ({e a} : Set B)) :=
  Nat.card_congr (CentralizerSmallKernelTransport.centralizerEquiv e a).toEquiv

private theorem centralizer_card_conj {A : Type*} [Group A] {a b : A}
    (h : IsConj a b) : Nat.card (Subgroup.centralizer ({a} : Set A)) =
      Nat.card (Subgroup.centralizer ({b} : Set A)) := by
  obtain ⟨g,rfl⟩ := isConj_iff.mp h
  exact centralizer_card_equiv (MulAut.conj g) a

private def centralizerInEquiv {A : Type*} [Group A] (H : Subgroup A) (a : H) :
    (Subgroup.centralizer ({(a : A)} : Set A)).subgroupOf H ≃*
      Subgroup.centralizer ({a} : Set H) where
  toFun x := ⟨x, mem_centralizer_singleton_iff.mpr
    (Subtype.ext (mem_centralizer_singleton_iff.mp x.property))⟩
  invFun x := ⟨x, mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

/-- The rank-two orbit gives the literal relative centralizer index. -/
theorem source_plane_second_index (hlinear : F.LinearFusion) :
    (secondCentralizer F).relIndex (sourcePlaneNormalizer F) = 42 := by
  let N := sourcePlaneNormalizer F
  let ρ : N →* MulAut G := MulAut.conj.comp N.subtype
  let : MulAction N G := MulAction.compHom G ρ
  have ho : MulAction.orbit N (planeSecondPoint F) =
      {a : G | a ∈ F.plane ∧ a ≠ 1 ∧ ¬ IsConj z a} := by
    ext a
    simp only [Set.mem_ofPred_eq]
    rw [linear_plane_second_class F hlinear]
    constructor
    · rintro ⟨n,rfl⟩
      refine ⟨(mem_normalizer_iff.mp n.property _).mp (planeSecondPoint_mem F), ?_⟩
      exact isConj_iff.mpr ⟨n,rfl⟩
    · rintro ⟨ha,hc⟩
      obtain ⟨n,hn,he⟩ := source_plane_fusion F (planeSecondPoint_mem F) ha hc
      exact ⟨⟨n,hn⟩,he⟩
  have hs : MulAction.stabilizer N (planeSecondPoint F) =
      (secondCentralizer F).subgroupOf N := by
    ext n
    change (n : G) * planeSecondPoint F * (n : G)⁻¹ = planeSecondPoint F ↔
      (n : G) ∈ secondCentralizer F
    rw [mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul
  change ((secondCentralizer F).subgroupOf N).index = _
  rw [← hs, MulAction.index_stabilizer, ho, source_plane_nonpoint_card F hlinear]

/-- The marked point centralizer is strictly larger than the second matrix
centralizer; only the already proved 21/42 rectangle orbits are used. -/
theorem native_point_centralizer_larger :
    Nat.card (secondCentralizer nativeMarking) < Nat.card centralizer := by
  let N := sourcePlaneNormalizer nativeMarking
  let Z := centralizer.subgroupOf N
  let T := (secondCentralizer nativeMarking).subgroupOf N
  have hz : Z.index = 21 := source_plane_point_index nativeMarking nativeMarking_linearFusion
  have ht : T.index = 42 := source_plane_second_index nativeMarking nativeMarking_linearFusion
  have hzc := Z.card_mul_index
  have htc := T.card_mul_index
  rw [hz] at hzc
  rw [ht] at htc
  have hpos : 0 < Nat.card T := Nat.card_pos
  have hlt : Nat.card T < Nat.card Z := by omega
  have hT : Nat.card T = Nat.card (secondCentralizer nativeMarking) :=
    Nat.card_congr (subgroupOfEquivOfLe native_second_centralizer_le_plane_normalizer).toEquiv
  have hZ : Nat.card Z ≤ Nat.card centralizer :=
    Nat.card_le_card_of_injective
      (fun x : Z => (⟨x.val.val,x.property⟩ : centralizer))
      (fun a b hab => Subtype.ext (Subtype.ext
        (congrArg (fun x : centralizer => (x : SL)) hab)))
  omega

omit [Finite G] in
/-- Recognition cannot interchange the original point and rank-two classes. -/
theorem recognized_point_class (F : MarkedCentralizer z) (e : G ≃* SL) :
    IsConj transvection (e z) := by
  have ho : orderOf (e z) = 2 := (e.orderOf_eq z).trans F.point_orderOf
  rcases linear_two_involution_classes nativeMarking nativeMarking_linearFusion (e z) ho with h | h
  · exact h
  · have he := centralizer_card_equiv e z
    have hf := Nat.card_congr F.equiv.toEquiv
    have ht := centralizer_card_conj h
    have hlt := native_point_centralizer_larger
    change Nat.card (Subgroup.centralizer ({z} : Set G)) = Nat.card centralizer at hf
    change Nat.card (secondCentralizer nativeMarking) =
      Nat.card (Subgroup.centralizer ({e z} : Set SL)) at ht
    omega

/-- Recognition carries the second marked class to the native second class. -/
theorem recognized_second_class (hlinear : F.LinearFusion) (e : G ≃* SL) :
    IsConj (planeSecondPoint nativeMarking) (e (planeSecondPoint F)) := by
  have ho : orderOf (e (planeSecondPoint F)) = 2 :=
    (e.orderOf_eq _).trans (planeSecondPoint_order F)
  rcases linear_two_involution_classes nativeMarking nativeMarking_linearFusion
      (e (planeSecondPoint F)) ho with h | h
  · have hz := recognized_point_class F e
    have hh := e.symm.toMonoidHom.map_isConj (hz.symm.trans h)
    simp only [MulEquiv.coe_toMonoidHom, e.symm_apply_apply] at hh
    exact (planeSecondPoint_not_conjugate F hlinear hh).elim
  · exact h


private theorem local_second_centralizer_card (hlinear : F.LinearFusion) :
    Nat.card ((secondCentralizer F).subgroupOf (sourcePlaneNormalizer F)) =
      Nat.card (secondCentralizer nativeMarking) := by
  obtain ⟨r,hr,_⟩ := exists_plane_normalizer_equiv F nativeMarking hlinear nativeMarking_linearFusion
  let a : sourcePlaneNormalizer F :=
    ⟨planeSecondPoint F,F.plane.le_normalizer (planeSecondPoint_mem F)⟩
  let b : sourcePlaneNormalizer nativeMarking :=
    ⟨planeSecondPoint nativeMarking,nativeMarking.plane.le_normalizer (planeSecondPoint_mem _)⟩
  have he : r a = b := by
    have hh := hr (sourceEquiv F 34)
    rw [planeMarkingEquiv_element] at hh
    exact hh
  calc
    _ = Nat.card (Subgroup.centralizer ({a} : Set (sourcePlaneNormalizer F))) :=
      Nat.card_congr (centralizerInEquiv (sourcePlaneNormalizer F) a).toEquiv
    _ = Nat.card (Subgroup.centralizer ({b} : Set (sourcePlaneNormalizer nativeMarking))) := by
      rw [centralizer_card_equiv r a,he]
    _ = Nat.card ((secondCentralizer nativeMarking).subgroupOf (sourcePlaneNormalizer nativeMarking)) :=
      (Nat.card_congr (centralizerInEquiv (sourcePlaneNormalizer nativeMarking) b).toEquiv).symm
    _ = _ := Nat.card_congr
      (subgroupOfEquivOfLe native_second_centralizer_le_plane_normalizer).toEquiv

/-- The marked local comparison identifies the full second centralizer with
its intersection with the literal plane normalizer in a recognized carrier. -/
theorem recognized_second_centralizer_le_plane_normalizer
    (hlinear : F.LinearFusion) (e : G ≃* SL) :
    secondCentralizer F ≤ sourcePlaneNormalizer F := by
  have hc : Nat.card (secondCentralizer F) = Nat.card (secondCentralizer nativeMarking) :=
    (centralizer_card_equiv e (planeSecondPoint F)).trans
      (centralizer_card_conj (recognized_second_class F hlinear e)).symm
  let j : (secondCentralizer F).subgroupOf (sourcePlaneNormalizer F) → secondCentralizer F :=
    fun x => ⟨x.val.val,x.property⟩
  have hj : Function.Injective j := fun a b hab => Subtype.ext (Subtype.ext
    (congrArg (fun x : secondCentralizer F => (x : G)) hab))
  have hs := (hj.bijective_of_nat_card_le (by
    rw [local_second_centralizer_card F hlinear,hc])).2
  intro g hg
  obtain ⟨x,hx⟩ := hs ⟨g,hg⟩
  have he : ((x.val : sourcePlaneNormalizer F) : G) = g := congrArg Subtype.val hx
  exact he ▸ x.val.property

/-- In the original generated subgroup, centralizing t forces normalization
of the original marked plane. No simplicity of that subgroup is used. -/
theorem secondStabilizer_le_plane_normalizer (hlinear : F.LinearFusion)
    (g : secondStabilizer F) : (((g : secondCentralizer F) : G)) ∈ sourcePlaneNormalizer F := by
  obtain ⟨e⟩ := normalizerSpan_nonempty_equiv F hlinear
  let E := normalizerSpanMarking F
  let x : normalizerSpan F := ⟨(g : secondCentralizer F),g.property⟩
  have hx : x ∈ secondCentralizer E := by
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    change (x : G) * ((planeSecondPoint E : normalizerSpan F) : G) =
      ((planeSecondPoint E : normalizerSpan F) : G) * (x : G)
    rw [normalizerSpan_secondPoint_val]
    exact mem_centralizer_singleton_iff.mp g.val.property
  have hn := recognized_second_centralizer_le_plane_normalizer E
    (normalizerSpan_linearFusion F hlinear) e hx
  have hm : (x : G) ∈ (sourcePlaneNormalizer E).map (normalizerSpan F).subtype := ⟨x,hn,rfl⟩
  rw [(normalizerSpan_normalizers_map F).2.1] at hm
  exact hm


/-- The plane image is normal in the literal quotient stabilizer. -/
theorem secondFourPlaneImage_normal (hlinear : F.LinearFusion) :
    (secondFourPlaneImage F).Normal where
  conj_mem x hx g := by
    obtain ⟨a,ha,he⟩ := hx
    obtain ⟨k,hk,hg⟩ := g.property
    have hkt : (k : G) ∈ secondCentralizer F :=
      mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp k.property _ (sourceSecondFour_second_mem F)).symm
    have hn := secondStabilizer_le_plane_normalizer F hlinear
      (⟨⟨k,hkt⟩,hk⟩ : secondStabilizer F)
    refine ⟨k * a * k⁻¹, (mem_normalizer_iff.mp hn _).mp ha, ?_⟩
    change QuotientGroup.mk' (secondFourKernel F) (k * a * k⁻¹) =
      ((g * x * g⁻¹ : secondFourStabilizerImage F) : secondFourQuotient F)
    simp only [map_mul,map_inv,Subgroup.coe_mul,Subgroup.coe_inv,he,hg]
    rfl

private def commonCode (c : Code) : Prop := c &&& 9 = 0
private instance (c : Code) : Decidable (commonCode c) := inferInstanceAs (Decidable (c &&& 9 = 0))

private theorem pair_common : ∀ c : Code, pure c = true → pure (34 ^^^ c) = true →
    commonCode c := by decide
private theorem common_xor : ∀ c d : Code, commonCode c → commonCode d →
    commonCode (c ^^^ d) := by decide
private theorem pointfree_product_table : ∀ c d : Code,
    commonCode c → commonCode d → pure c = true → pure (34 ^^^ c) = false →
    pure d = true → c ≠ d → pure (c ^^^ d) = false →
    pure (34 ^^^ (c ^^^ d)) = false → c ^^^ d = 22 ∨ c ^^^ d = 52 := by decide

private theorem normalizer_second_codes (hlinear : F.LinearFusion)
    (g : secondStabilizer F) :
    ∃ f : Equiv.Perm Code,
      (∀ c, (((g : secondCentralizer F) : G) * element F c *
        (((g : secondCentralizer F) : G))⁻¹) = element F (f c)) ∧
      commonCode (f 4) ∧ commonCode (f 2) ∧ pure (f 4) = true ∧
      pure (34 ^^^ f 4) = false ∧ pure (f 2) = true := by
  let n : sourcePlaneNormalizer F := ⟨g,secondStabilizer_le_plane_normalizer F hlinear g⟩
  let f := normalizerAction F n
  have hf := (mem_rankOneGroup f).mp (normalizer_rankOne F hlinear n)
  have ht : f 34 = 34 := by
    apply element_injective F
    rw [normalizerAction_element]
    change (g.val : G) * planeSecondPoint F * (g.val : G)⁻¹ = planeSecondPoint F
    rw [mem_centralizer_singleton_iff.mp g.val.property,mul_inv_cancel_right]
  have hpc (c : Code) : pure (f c) = pure c := hf.2 c
  have htc (c : Code) : pure (34 ^^^ f c) = pure (34 ^^^ c) := by
    rw [← ht,← hf.1,hpc,ht]
  have h2 : commonCode (f 2) := pair_common _ (hpc 2) (htc 2)
  have h6 : commonCode (f 6) := pair_common _ (hpc 6) (htc 6)
  have h4 : f 4 = f 2 ^^^ f 6 := hf.1 2 6
  refine ⟨f,fun c => (normalizerAction_element F n c).symm,?_,h2,hpc 4,htc 4,hpc 2⟩
  rw [h4]
  exact common_xor _ _ h2 h6

private theorem first_point_codes (hlinear : F.LinearFusion) (a : secondStabilizer F)
    (ha : IsConj (secondCentralizerPoint F) a) :
    ∃ c : Code, (((a : secondCentralizer F) : G)) = element F c ∧
      commonCode c ∧ pure c = true ∧ pure (34 ^^^ c) = false := by
  obtain ⟨g,hg⟩ := isConj_iff.mp ha
  obtain ⟨f,hf,h4,_,hp,ht,_⟩ := normalizer_second_codes F hlinear g
  refine ⟨f 4,?_,h4,hp,ht⟩
  have he := congrArg (fun a : secondStabilizer F => ((a : secondCentralizer F) : G)) hg
  exact he.symm.trans (hf 4)

private theorem other_point_codes (hlinear : F.LinearFusion) (b : secondStabilizer F)
    (hb : IsConj (secondCentralizerPoint F) b ∨ IsConj (secondCentralizerOtherPoint F) b) :
    ∃ c : Code, (((b : secondCentralizer F) : G)) = element F c ∧
      commonCode c ∧ pure c = true := by
  rcases hb with hb | hb
  · obtain ⟨c,hc,hm,hp,_⟩ := first_point_codes F hlinear b hb
    exact ⟨c,hc,hm,hp⟩
  · obtain ⟨g,hg⟩ := isConj_iff.mp hb
    obtain ⟨f,hf,_,h2,_,_,hp⟩ := normalizer_second_codes F hlinear g
    refine ⟨f 2,?_,h2,hp⟩
    have he := congrArg (fun a : secondStabilizer F => ((a : secondCentralizer F) : G)) hg
    exact he.symm.trans (hf 2)


omit [Finite G] in
private theorem sourceSecondFour_eq_22 : sourceSecondFour F =
    zpowers (planeSecondPoint F) ⊔ zpowers (element F 22) := by
  rw [sourceSecondFour_eq]
  apply le_antisymm <;> apply sup_le
  · exact le_sup_left
  · apply zpowers_le.mpr
    rw [show element F 52 = planeSecondPoint F * element F 22 from element_xor F 34 22]
    exact mul_mem_sup (mem_zpowers _) (mem_zpowers _)
  · exact le_sup_left
  · apply zpowers_le.mpr
    rw [show element F 22 = planeSecondPoint F * element F 52 from element_xor F 34 52]
    exact mul_mem_sup (mem_zpowers _) (mem_zpowers _)

/-- For the prescribed pair of point classes, the point-free four-group is
already the marked field four-group; no further conjugation is necessary. -/
theorem second_pointfree_four_eq (hlinear : F.LinearFusion)
    (a b : secondStabilizer F)
    (ha : IsConj (secondCentralizerPoint F) a)
    (hb : IsConj (secondCentralizerPoint F) b ∨ IsConj (secondCentralizerOtherPoint F) b)
    (hab : a ≠ b)
    (hfree : ∀ x ∈ zpowers (planeSecondPoint F) ⊔
      zpowers (((a * b : secondStabilizer F) : secondCentralizer F) : G), ¬ IsConj z x) :
    zpowers (planeSecondPoint F) ⊔
      zpowers (((a * b : secondStabilizer F) : secondCentralizer F) : G) = sourceSecondFour F := by
  obtain ⟨c,hc,hcm,hcp,hct⟩ := first_point_codes F hlinear a ha
  obtain ⟨d,hd,hdm,hdp⟩ := other_point_codes F hlinear b hb
  have hcd : c ≠ d := by
    intro he
    apply hab
    apply Subtype.ext
    apply Subtype.ext
    exact hc.trans ((congrArg (element F) he).trans hd.symm)
  have hprod : (((a * b : secondStabilizer F) : secondCentralizer F) : G) =
      element F (c ^^^ d) := by
    change ((a : secondCentralizer F) : G) * ((b : secondCentralizer F) : G) = _
    rw [hc,hd,element_xor]
  rw [hprod] at hfree ⊢
  have hs : pure (c ^^^ d) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    exact hfree _ ((show zpowers (element F (c ^^^ d)) ≤ _ from le_sup_right) (mem_zpowers _))
      ((fusion_iff_pure F hlinear _).mpr hh)
  have hts : pure (34 ^^^ (c ^^^ d)) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    have hm : element F (34 ^^^ (c ^^^ d)) ∈
        zpowers (planeSecondPoint F) ⊔ zpowers (element F (c ^^^ d)) := by
      rw [element_xor F 34 (c ^^^ d)]
      exact mul_mem_sup (mem_zpowers (planeSecondPoint F)) (mem_zpowers (element F (c ^^^ d)))
    exact hfree _ hm ((fusion_iff_pure F hlinear _).mpr hh)
  rcases pointfree_product_table c d hcm hdm hcp hct hdp hcd hs hts with he | he
  · rw [he]
    exact (sourceSecondFour_eq_22 F).symm
  · rw [he]
    exact (sourceSecondFour_eq F).symm

/-- Both remaining local calculations of source 41.1 hold in the original
marked coordinates and in the literal centralizer quotient. -/
theorem secondCentralizerLocalData (hlinear : F.LinearFusion) : SecondCentralizerLocalData F := {
  plane_normal := secondFourPlaneImage_normal F hlinear
  four_transport := by
    intro a b ha hb hab _
    dsimp only
    intro hfree
    have he := second_pointfree_four_eq F hlinear a b ha hb hab hfree
    refine ⟨1,(normalizerSpan F).one_mem,?_⟩
    have h1 : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    rw [h1,Subgroup.map_id]
    exact he }

/-- The full centralizer of the second involution lies in the generated
subgroup, by the two literal fixed-coset arguments of source 41.1. -/
theorem second_centralizer_le_normalizerSpan (hlinear : F.LinearFusion) :
    secondCentralizer F ≤ normalizerSpan F :=
  second_centralizer_le_of_local_data F hlinear (secondCentralizerLocalData F hlinear)

/-- Source 41.1: the original row and three-space normalizers generate G. -/
theorem linear_normalizer_generation (hlinear : F.LinearFusion) :
    rowNormalizer F ⊔ sourceThreeSpaceNormalizer F = ⊤ :=
  normalizer_generation_of_second_local_data F hlinear (secondCentralizerLocalData F hlinear)

/-- The original source geometry and native comparison, with all linear
local premises discharged. -/
theorem nonempty_sourceComparison (hlinear : F.LinearFusion) : Nonempty (SourceComparison F) :=
  nonempty_sourceComparison_of_second_local_data F hlinear (secondCentralizerLocalData F hlinear)

end Theory.GroupTheory.TransvectionFive.UniquenessLinear
