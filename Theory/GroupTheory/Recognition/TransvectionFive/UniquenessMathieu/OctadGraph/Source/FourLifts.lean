module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.SecondCentralizer
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceSecondCentralizer
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourcePlaneCoordinates
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceRectangleOrbits
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.PairCentralizer

public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Point-class lifts in the literal second-four quotient

Inside the marked Sylow, centralizing B(t) forces the two outer adjacent
matrix entries to vanish. If the square lies in B(t), the four remaining
quadratic entries force membership in A₁ or A₂. Every nonzero coset of
either rectangle modulo B(t) has a point-class representative.

The join A₁A₂ has order 256. Adjoining the explicit involution
(I+E₀₁)(I+E₃₄) gives a subgroup of order 512 in I=C_{N_G(A₂)}(t).
The original quotient I/A₂≃S₅ makes it Sylow. Since I normalizes its
actual residual-fixed B(t), Sylow intersection supplies a Sylow subgroup
of C_I(B) inside the original marked Sylow. Conjugating order-four lifts
into that subgroup completes the quotient calculation.

Thus the two fixed-coset arguments and actual ambient M₂₄ recognition
now require only C_L(t)≤N_G(A₂). That placement remains an explicit
obligation. All groups, kernels and quotient maps retain the original
marking and the 21/45 orientation; no generation premise is hidden here.

Source: Aschbacher, *Sporadic Groups* (1994), 41.2, printed pp.220–221.
Internal imports reuse the existing rectangle and four-group coordinates.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer PlaneTensor PlaneCensus
open Theory.SpecificGroups.LinearSylowNormalizers
private abbrev Mat := Matrix (Fin 5) (Fin 5) (ZMod 2)
private def upperEntries (v : Fin 10 → ZMod 2) : Mat := !![
  1,v 0,v 1,v 2,v 3;
  0,1,v 4,v 5,v 6;
  0,0,1,v 7,v 8;
  0,0,0,1,v 9;
  0,0,0,0,1]
private def upperCoordinates (g : SL) : Fin 10 → ZMod 2 :=
  ![g 0 1,g 0 2,g 0 3,g 0 4,g 1 2,g 1 3,g 1 4,g 2 3,g 2 4,g 3 4]
private theorem upper_shape (g : SL) (hg : g ∈ unipotent 5 (ZMod 2)) :
    g.val = upperEntries (upperCoordinates g) := by
  obtain ⟨hu,hd⟩ := (mem_unipotent 5 (ZMod 2) g).mp hg
  have hu := (mem_borel 5 (ZMod 2) g).mp hu
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperEntries,upperCoordinates,hd]
  all_goals exact hu (by decide)

private def codeMatrix (c : Code) : Mat :=
  1 + Matrix.single 0 2 (decode c 0 0) + Matrix.single 0 3 (decode c 0 1) +
    Matrix.single 0 4 (decode c 0 2) + Matrix.single 1 2 (decode c 1 0) +
    Matrix.single 1 3 (decode c 1 1) + Matrix.single 1 4 (decode c 1 2)

private theorem model_code_matrix (c : Code) :
    (modelPlaneCoordinates.symm (Multiplicative.ofAdd (decode c)) : SL).val = codeMatrix c := by
  rw [modelPlaneCoordinates_matrix,modelPlaneCoordinates.apply_symm_apply]
  rfl

private theorem four_commuting_entries (v : Fin 10 → ZMod 2)
    (_ht : upperEntries v * codeMatrix 34 = codeMatrix 34 * upperEntries v)
    (hb : upperEntries v * codeMatrix 52 = codeMatrix 52 * upperEntries v) :
    v 0 = 0 ∧ v 9 = 0 := by
  have h0 := congrFun (congrFun hb 0) 3
  have h9 := congrFun (congrFun hb 1) 4
  have he : codeMatrix 52 = !![1,0,0,0,1;0,1,0,1,1;0,0,1,0,0;0,0,0,1,0;0,0,0,0,1] := by decide
  rw [he] at h0 h9
  simpa [upperEntries,Matrix.mul_apply,Fin.sum_univ_succ,add_comm,add_left_comm,add_assoc]
    using And.intro h0 h9.symm

private theorem square_four_rectangle (v : Fin 10 → ZMod 2) (hv0 : v 0 = 0) (hv9 : v 9 = 0)
    (c : Code) (hc : c ∈ fourCodes)
    (hs : upperEntries v * upperEntries v = codeMatrix c) :
    (v 7 = 0 ∧ v 8 = 0) ∨ (v 1 = 0 ∧ v 4 = 0) := by
  have h03 := congrFun (congrFun hs 0) 3
  have h04 := congrFun (congrFun hs 0) 4
  have h13 := congrFun (congrFun hs 1) 3
  have h14 := congrFun (congrFun hs 1) 4
  simp only [upperEntries,Matrix.mul_apply,Fin.sum_univ_succ] at h03 h04 h13 h14
  simp [hv0,hv9,codeMatrix,Matrix.single] at h03 h04 h13 h14
  have cancel (x y : ZMod 2) : x + (y + x) = y := by
    ring_nf
    simp [show (2 : ZMod 2) = 0 from rfl]
  simp only [cancel] at h03 h04 h13 h14
  have calc4 : ∀ (a b d e : ZMod 2) (c : Code), c ∈ fourCodes →
      a*d = decode c 0 1 → a*e = decode c 0 2 →
      b*d = decode c 1 1 → b*e = decode c 1 2 →
      (d = 0 ∧ e = 0) ∨ (a = 0 ∧ b = 0) := by decide
  exact calc4 (v 1) (v 4) (v 7) (v 8) c hc h03 h04 h13 h14

variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

/-- An element of the source Sylow centralizing B(t), with square in B(t),
belongs to one of the original two elementary rectangles. -/
theorem sylow_secondFour_square_rectangles {a : G}
    (haT : a ∈ (sourceSylow F : Subgroup G)) (haC : a ∈ secondFourCentralizer F)
    (hs : a * a ∈ sourceSecondFour F) : a ∈ F.plane ∨ a ∈ F.threeSpace := by
  let aH : Subgroup.centralizer ({z} : Set G) := ⟨a,sourceSylow_le_point_centralizer F haT⟩
  let g : SL := F.equiv aH
  have hg : g ∈ unipotent 5 (ZMod 2) := by
    apply (F.mem_pullback_iff _ aH).mp
    rwa [← coe_sourceSylow]
  have hshape := upper_shape g hg
  have comm (c : Code) (hc : c ∈ fourCodes) :
      upperEntries (upperCoordinates g) * codeMatrix c =
        codeMatrix c * upperEntries (upperCoordinates g) := by
    let bH : Subgroup.centralizer ({z} : Set G) :=
      ⟨element F c,F.pullback_le _ (element_mem F c)⟩
    have hh : aH * bH = bH * aH := Subtype.ext
      (mem_centralizer_iff.mp haC _ ((element_mem_sourceSecondFour F c).mpr hc)).symm
    have he := congrArg (fun x => (F.equiv x : SL).val) hh
    simp only [map_mul,Subgroup.coe_mul,Matrix.SpecialLinearGroup.coe_mul] at he
    change g.val * (F.equiv bH : SL).val = (F.equiv bH : SL).val * g.val at he
    simpa only [bH,element_model,model_code_matrix,hshape] using he
  obtain ⟨hv0,hv9⟩ := four_commuting_entries _ (comm 34 (by decide)) (comm 52 (by decide))
  obtain ⟨c,hc,he⟩ := hs
  have hsq : upperEntries (upperCoordinates g) * upperEntries (upperCoordinates g) = codeMatrix c := by
    have hh : aH * aH = ⟨element F c,F.pullback_le _ (element_mem F c)⟩ := Subtype.ext he.symm
    have hh' := congrArg (fun x => (F.equiv x : SL).val) hh
    simp only [map_mul,Subgroup.coe_mul,Matrix.SpecialLinearGroup.coe_mul] at hh'
    change g.val * g.val = (F.equiv ⟨element F c,_⟩ : SL).val at hh'
    simpa only [element_model,model_code_matrix,hshape] using hh'
  rcases square_four_rectangle _ hv0 hv9 c hc hsq with h | h
  · left
    apply (F.mem_pullback_iff Model.plane aH).mpr
    apply (RectangleCoordinates.mem2_iff g).mpr
    intro i j hij
    rw [hshape]
    fin_cases i <;> fin_cases j <;> simp [upperEntries,hv0,hv9,h.1,h.2] at hij ⊢
  · right
    apply (F.mem_pullback_iff Model.threeSpace aH).mpr
    apply (RectangleCoordinates.mem3_iff g).mpr
    intro i j hij
    rw [hshape]
    fin_cases i <;> fin_cases j <;> simp [upperEntries,hv0,hv9,h.1,h.2] at hij ⊢

/-- Every nonzero A₁/B(t) coset has a point-class representative, in the
original 21-point orientation. -/
theorem secondFour_plane_point_lift (D : LocalData F) {a : G}
    (ha : a ∈ F.plane) (haB : a ∉ sourceSecondFour F) :
    ∃ b : sourceSecondFour F, IsConj z (a * (b : G)) := by
  obtain ⟨c,hc⟩ := (sourceEquiv F).surjective ⟨a,ha⟩
  have he : element F c = a := congrArg Subtype.val hc
  have hn : c ∉ fourCodes := fun h => haB (he ▸ (element_mem_sourceSecondFour F c).mpr h)
  obtain ⟨b,hb,hp⟩ := fourCodes_cover c hn
  refine ⟨⟨element F b,(element_mem_sourceSecondFour F b).mpr hb⟩,?_⟩
  rw [← he,← element_xor]
  exact (plane_fusion_iff_pure F D.orientation.1 _).mpr hp

/-- The source Sylow calculation supplies point-class lifts for every
involution coset in its literal B(t)-centralizer. -/
theorem sylow_secondFour_point_lift (D : LocalData F) {a : G}
    (haT : a ∈ (sourceSylow F : Subgroup G)) (haC : a ∈ secondFourCentralizer F)
    (hs : a * a ∈ sourceSecondFour F) (haB : a ∉ sourceSecondFour F) :
    ∃ b : sourceSecondFour F, IsConj z (a * (b : G)) := by
  rcases sylow_secondFour_square_rectangles F haT haC hs with h | h
  · exact secondFour_plane_point_lift F D h haB
  · exact secondFour_threeSpace_point_lift F D h haB


private def secondMoverModel : SL := root (by decide : (0 : Fin 5) < 1) *
  root (by decide : (3 : Fin 5) < 4)
private theorem secondMoverModel_upper : secondMoverModel ∈ upper := by
  exact upper.mul_mem (subset_closure ⟨0,1,by decide,rfl⟩)
    (subset_closure ⟨3,4,by decide,rfl⟩)

private def secondMover : G :=
  F.equiv.symm ⟨secondMoverModel,upper_le_centralizer secondMoverModel_upper⟩
private theorem secondMover_mem_sylow : secondMover F ∈ (sourceSylow F : Subgroup G) := by
  rw [coe_sourceSylow]
  apply (F.mem_pullback_iff _ (F.equiv.symm ⟨secondMoverModel,
    upper_le_centralizer secondMoverModel_upper⟩)).mpr
  rw [F.equiv.apply_symm_apply,← model_upper_eq_unipotent]
  exact secondMoverModel_upper

omit [Finite G] in
private theorem secondMover_square : secondMover F ^ 2 = 1 := by
  have hm : secondMoverModel ^ 2 = 1 := by decide
  have hh : (⟨secondMoverModel,upper_le_centralizer secondMoverModel_upper⟩ : centralizer)^2 = 1 :=
    Subtype.ext hm
  exact congrArg Subtype.val (by simpa only [map_pow,map_one] using congrArg F.equiv.symm hh)

omit [Finite G] in
private theorem secondMover_commute_code (c : Code) :
    secondMover F * element F c = element F c * secondMover F ↔
      secondMoverModel.val * codeMatrix c = codeMatrix c * secondMoverModel.val := by
  let s : Subgroup.centralizer ({z} : Set G) :=
    F.equiv.symm ⟨secondMoverModel,upper_le_centralizer secondMoverModel_upper⟩
  let b : Subgroup.centralizer ({z} : Set G) := ⟨element F c,F.pullback_le _ (element_mem F c)⟩
  have he : (F.equiv b : SL).val = codeMatrix c := by
    exact (congrArg (fun x : SL => x.val) (element_model F c)).trans (model_code_matrix c)
  have hs : (F.equiv s : SL) = secondMoverModel := congrArg Subtype.val (F.equiv.apply_symm_apply _)
  constructor
  · intro h
    have hh : s*b = b*s := Subtype.ext h
    have hm := congrArg (fun x => (F.equiv x : SL).val) hh
    simpa only [map_mul,Subgroup.coe_mul,Matrix.SpecialLinearGroup.coe_mul,hs,he] using hm
  · intro h
    have hh : s*b = b*s := by
      apply F.equiv.injective
      apply Subtype.ext
      apply Subtype.ext
      simpa only [map_mul,Subgroup.coe_mul,Matrix.SpecialLinearGroup.coe_mul,hs,he] using h
    exact congrArg Subtype.val hh

omit [Finite G] in
private theorem secondMover_centralizes : secondMover F ∈ secondCentralizer F := by
  apply mem_centralizer_singleton_iff.mpr
  exact (secondMover_commute_code F 34).mpr (by decide)

omit [Finite G] in
private theorem secondMover_not_fourCentralizer : secondMover F ∉ secondFourCentralizer F := by
  intro h
  have hh := (secondMover_commute_code F 52).mp
    (mem_centralizer_iff.mp h _ ((element_mem_sourceSecondFour F 52).mpr (by decide))).symm
  exact (by decide : secondMoverModel.val * codeMatrix 52 ≠ codeMatrix 52 * secondMoverModel.val) hh

private theorem rectangleJoin_card : Nat.card (F.plane ⊔ F.threeSpace : Subgroup G) = 256 := by
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes F.plane F.threeSpace
    ((flag_le_sourceSylow F).2.2.2.trans (plane_normalizers_contain_sourceSylow F).1)
  rw [source_plane_card,source_threeSpace_card,SourceNormalizer.planes_intersection_card] at hc
  omega

/-- The literal source I=C_{N_G(A₂)}(t) has its original order 2⁹·15. -/
theorem local_second_centralizer_card (D : LocalData F) :
    Nat.card (involutionCentralizer F (planeSecondPoint F)) = 7680 := by
  obtain ⟨e⟩ := involutionCentralizer_quotient_of_not_fused F D.orientation _
    (secondPoint_mem_threeSpace F)
    ((element_ne_one_iff F 34).mpr (by decide)) (secondPoint_not_fused F D)
  have hc : Nat.card (involutionCentralizerQuotient F (planeSecondPoint F)) = 120 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have hA : Nat.card (F.threeSpace.subgroupOf (involutionCentralizer F (planeSecondPoint F))) = 64 :=
    (Nat.card_congr (subgroupOfEquivOfLe
      (threeSpace_le_involutionCentralizer F _ (secondPoint_mem_threeSpace F))).toEquiv).trans
        (source_threeSpace_card F)
  rw [card_eq_card_quotient_mul_card_subgroup (F.threeSpace.subgroupOf
    (involutionCentralizer F (planeSecondPoint F))),hc,hA]

/-- A Sylow subgroup of the literal local second centralizer lies in the
original marked Sylow, as required for the rectangle calculation. -/
theorem local_second_sylow (D : LocalData F) :
    ∃ P : Sylow 2 (involutionCentralizer F (planeSecondPoint F)),
      (P : Subgroup (involutionCentralizer F (planeSecondPoint F))) ≤
        (sourceSylow F : Subgroup G).subgroupOf (involutionCentralizer F (planeSecondPoint F)) := by
  let J : Subgroup G := F.plane ⊔ F.threeSpace
  have hJT : J ≤ (sourceSylow F : Subgroup G) :=
    sup_le (flag_le_sourceSylow F).2.2.1 (flag_le_sourceSylow F).2.2.2
  have hJC : J ≤ secondFourCentralizer F :=
    sup_le (plane_le_secondFourCentralizer F) (threeSpace_le_secondFourCentralizer F)
  have hJN : (sourceSylow F : Subgroup G) ≤ normalizer (J : Set G) :=
    (le_inf (plane_normalizers_contain_sourceSylow F).1
      (plane_normalizers_contain_sourceSylow F).2).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  let P : Subgroup G := J ⊔ zpowers (secondMover F)
  have hPT : P ≤ (sourceSylow F : Subgroup G) :=
    sup_le hJT (zpowers_le.mpr (secondMover_mem_sylow F))
  have hPC : P ≤ secondCentralizer F := sup_le
    (hJC.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (sourceSecondFour_second_mem F))))
    (zpowers_le.mpr (secondMover_centralizes F))
  have hPI : P ≤ involutionCentralizer F (planeSecondPoint F) :=
    le_inf (hPT.trans (plane_normalizers_contain_sourceSylow F).2) hPC
  have hcP : Nat.card P = 512 := by
    rw [card_sup_zpowers_of_normalizing_involution J (secondMover F) (secondMover_square F)
      (fun h => secondMover_not_fourCentralizer F (hJC h)) (hJN (secondMover_mem_sylow F))]
    rw [rectangleJoin_card]
  let PI := P.subgroupOf (involutionCentralizer F (planeSecondPoint F))
  have hcPI : Nat.card PI = 512 := (Nat.card_congr (subgroupOfEquivOfLe hPI).toEquiv).trans hcP
  have hindex : PI.index = 15 := by
    have hh := PI.card_mul_index
    rw [hcPI,local_second_centralizer_card F D] at hh
    omega
  have hp : IsPGroup 2 PI := IsPGroup.of_card (n := 9) hcPI
  exact ⟨hp.toSylow (by rw [hindex]; decide),fun x hx => hPT hx⟩

/-- I normalizes its actual residual-fixed four-subgroup. -/
theorem local_second_normalizes_four (D : LocalData F) :
    involutionCentralizer F (planeSecondPoint F) ≤ normalizer (sourceSecondFour F : Set G) := by
  obtain ⟨E⟩ := involutionCentralizerData_of_not_fused F D.orientation _
    (secondPoint_mem_threeSpace F) ((element_ne_one_iff F 34).mpr (by decide))
    (secondPoint_not_fused F D)
  rw [secondFour_eq_involutionFour F D]
  intro g hg
  have hm : (⟨g,hg.1⟩ : threeSpaceNormalizer F) ∈
      E.cubic ⊔ (involutionCentralizer F (planeSecondPoint F)).subgroupOf (threeSpaceNormalizer F) :=
    (show (involutionCentralizer F (planeSecondPoint F)).subgroupOf (threeSpaceNormalizer F) ≤
      E.cubic ⊔ (involutionCentralizer F (planeSecondPoint F)).subgroupOf (threeSpaceNormalizer F) from le_sup_right) (show (⟨g,hg.1⟩ : threeSpaceNormalizer F) ∈
      (involutionCentralizer F (planeSecondPoint F)).subgroupOf (threeSpaceNormalizer F) from hg)
  rw [← E.four_normalizer] at hm
  exact hm


private theorem local_four_sylow (D : LocalData F) :
    ∃ P : Sylow 2 ((secondFourCentralizer F).subgroupOf (involutionCentralizer F (planeSecondPoint F))),
      ∀ x : P, (((x.val : (secondFourCentralizer F).subgroupOf
        (involutionCentralizer F (planeSecondPoint F))) : involutionCentralizer F (planeSecondPoint F)) : G)
          ∈ (sourceSylow F : Subgroup G) := by
  let I := involutionCentralizer F (planeSecondPoint F)
  let K := (secondFourCentralizer F).subgroupOf I
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    ((local_second_normalizes_four F D).trans (normalizer_le_normalizer_centralizer _))
  obtain ⟨P,hP⟩ := local_second_sylow F D
  obtain ⟨Q,hQ⟩ := P.exists_subgroupOf_eq_of_normal K
  refine ⟨Q,fun x => ?_⟩
  have hx : x.val.val ∈ (P : Subgroup I) := by
    have hm : x.val ∈ (Q : Subgroup K) := x.property
    rw [hQ] at hm
    exact hm
  exact hP hx

/-- Every involution of the actual (L∩C_G(B))/B has a point-class lift,
once C_L(t) is placed in G₃. The quotient-lift calculation introduces no
additional premise. -/
theorem secondFour_involution_lifts_of_local_placement (D : LocalData F)
    (hlocal : normalizerSpan F ⊓ Subgroup.centralizer ({planeSecondPoint F} : Set G) ≤
      threeSpaceNormalizer F)
    (x : secondFourStabilizerImage F) (hx : orderOf x = 2) :
    ∃ y : secondFourStabilizer F,
      QuotientGroup.mk' (secondFourKernel F) y = (x : secondFourQuotient F) ∧
      IsConj z ((y : secondFourCentralizer F) : G) := by
  let q := QuotientGroup.mk' (secondFourKernel F)
  obtain ⟨a,haL,he⟩ := x.property
  have hx2 : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
  have ha2 : a * a ∈ secondFourKernel F := by
    apply (QuotientGroup.eq_one_iff (N := secondFourKernel F) (a*a)).mp
    change q (a*a) = 1
    rw [map_mul,he,← pow_two]
    exact congrArg Subtype.val hx2
  have haB : (a : G) ∉ sourceSecondFour F := by
    intro h
    have hq : q a = 1 := (QuotientGroup.eq_one_iff a).mpr h
    have he1 : x = 1 := Subtype.ext (he.symm.trans hq)
    have := (orderOf_eq_prime_iff.mp hx).2
    exact this he1
  have hat : (a : G) ∈ secondCentralizer F :=
    mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp a.property _ (sourceSecondFour_second_mem F)).symm
  have haI : (a : G) ∈ involutionCentralizer F (planeSecondPoint F) :=
    ⟨hlocal ⟨haL,hat⟩,hat⟩
  let I := involutionCentralizer F (planeSecondPoint F)
  let K := (secondFourCentralizer F).subgroupOf I
  let aK : K := ⟨⟨a,haI⟩,a.property⟩
  have ha4 : aK ^ 4 = 1 := by
    obtain ⟨c,_,hc⟩ := ha2
    change element F c = (a : G) * (a : G) at hc
    apply Subtype.ext
    apply Subtype.ext
    change (a : G)^4 = 1
    rw [show (4 : ℕ) = 2*2 from rfl,pow_mul,pow_two (a : G),← hc]
    simpa only [pow_two] using element_square F c
  obtain ⟨k,_,hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show orderOf aK ∣ 2^2 from orderOf_dvd_of_pow_eq_one ha4)
  obtain ⟨P,hP⟩ := local_four_sylow F D
  obtain ⟨v,hv⟩ := P.exists_isConj_of_orderOf_eq_prime_pow hk
  obtain ⟨n,hn⟩ := isConj_iff.mp hv
  let nG : G := n.val.val
  let vG : G := v.val.val.val
  have hconj : nG * (a : G) * nG⁻¹ = vG :=
    congrArg (fun b : K => (b.val : G)) hn
  have hnB : nG ∈ normalizer (sourceSecondFour F : Set G) :=
    Subgroup.centralizer_le_normalizer _ n.property
  have hvC : vG ∈ secondFourCentralizer F := v.val.property
  have hv2 : vG * vG ∈ sourceSecondFour F := by
    have hh : vG*vG = nG*((a : G)*(a : G))*nG⁻¹ := by rw [← hconj]; group
    rw [hh]
    exact (mem_normalizer_iff.mp hnB _).mp ha2
  have hvB : vG ∉ sourceSecondFour F := by
    intro h
    apply haB
    exact (mem_normalizer_iff.mp hnB _).mpr (hconj.symm ▸ h)
  obtain ⟨b,hpoint⟩ := sylow_secondFour_point_lift F D (hP v) hvC hv2 hvB
  have hp : IsConj z ((a : G) * (b : G)) := by
    apply hpoint.trans
    symm
    apply isConj_iff.mpr
    refine ⟨nG,?_⟩
    have hb : nG * (b : G) * nG⁻¹ = b := by
      have hh : (b : G) * nG = nG * (b : G) := mem_centralizer_iff.mp n.property _ b.property
      rw [← hh,mul_inv_cancel_right]
    calc
      nG * ((a : G) * (b : G)) * nG⁻¹ =
        (nG * (a : G) * nG⁻¹) * (nG * (b : G) * nG⁻¹) := by group
      _ = _ := by rw [hconj,hb]
  let bC : secondFourCentralizer F :=
    ⟨b,plane_le_secondFourCentralizer F (sourceSecondFour_le_plane F b.property)⟩
  let y : secondFourStabilizer F := ⟨a*bC,(normalizerSpan F).mul_mem haL
    (plane_le_span F (sourceSecondFour_le_plane F b.property))⟩
  refine ⟨y,?_,hp⟩
  change q (a*bC) = _
  rw [map_mul,show q bC = 1 from (QuotientGroup.eq_one_iff bC).mpr b.property,mul_one]
  exact he

/-- With quotient lifts proved, the sole remaining local premise is the
placement of C_L(t) in the original N_G(A₂). -/
theorem second_centralizer_le_of_local_placement (D : LocalData F)
    (hlocal : normalizerSpan F ⊓ Subgroup.centralizer ({planeSecondPoint F} : Set G) ≤
      threeSpaceNormalizer F) :
    Subgroup.centralizer ({planeSecondPoint F} : Set G) ≤ normalizerSpan F :=
  second_centralizer_le_of_local_placement_and_lifts F D hlocal
    (secondFour_involution_lifts_of_local_placement F D hlocal)

/-- The original full normalizers generate the ambient group once local
second-centralizer placement is established. -/
theorem normalizer_generation_of_local_placement (D : LocalData F)
    (hlocal : normalizerSpan F ⊓ Subgroup.centralizer ({planeSecondPoint F} : Set G) ≤
      threeSpaceNormalizer F) : threeSpaceNormalizer F ⊔ rowNormalizer F = ⊤ :=
  normalizer_generation_of_second_centralizer F D (second_centralizer_le_of_local_placement F D hlocal)

/-- Actual ambient recognition with the quotient-lift premise discharged. -/
theorem equiv_of_local_placement (D : LocalData F)
    (hlocal : normalizerSpan F ⊓ Subgroup.centralizer ({planeSecondPoint F} : Set G) ≤
      threeSpaceNormalizer F) : Nonempty (G ≃* Sporadic.Mathieu.M24) :=
  equiv_of_second_centralizer F D (second_centralizer_le_of_local_placement F D hlocal)

/-- The remaining placement premise refers to exactly the original producer's
oriented marking, retaining the 21/45 convention. -/
theorem oriented_equiv_of_local_placement (hfusion : F.MathieuFusion)
    (hlocal : let E := SourceData.ofFusion F hfusion
      normalizerSpan E.oriented.marking ⊓
        Subgroup.centralizer ({planeSecondPoint E.oriented.marking} : Set G) ≤
          threeSpaceNormalizer E.oriented.marking) : Nonempty (G ≃* Sporadic.Mathieu.M24) :=
  let E := SourceData.ofFusion F hfusion
  equiv_of_local_placement E.oriented.marking E.localData hlocal

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
