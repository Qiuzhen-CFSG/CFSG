module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ExtraspecialReduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.NativeFBranch
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Application

/-!
# Ordinary endpoints of the pure first-class normalizer argument

The original ATLAS max2 subgroup is identified with the first involution
centralizer by the literal certified conjugator. This closes the rank-one
case of KW Section 2.1 and retains the actual native local in its radical
application. The exceptional order-256 branch is transported against the
single independent native-eight normalizer placement; no pure-normalizer
classification is used to discharge that input.

Source: Kleidman--Wilson (1988), Section 2.1, pp.488--489, and Corollary
2.3.6, p.493. The first-centralizer bridge is the native ATLAS word certificate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open ElementaryEightGeometry
attribute [local irreducible] modelGroup matrixA matrixB

/-- The actual first centralizer is the original ATLAS max2 conjugate. -/
theorem firstCentralizer_eq_source_conjugate :
    InvolutionCentralizers.First.centralizer =
      sourceSubgroup.map (MulAut.conj h⁻¹).toMonoidHom := by
  rw [sourceSubgroup_map_conj, localSubgroup_eq_top, ← MonoidHom.range_eq_map,
    centralizerToModel_range]

private theorem map_conj_mul (A : Subgroup Model) (g k : Model) :
    (A.map (MulAut.conj k).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g*k)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

private theorem map_conj_one (A : Subgroup Model) :
    A.map (MulAut.conj (1 : Model)).toMonoidHom = A :=
  mem_normalizer_iff_map_conj_eq.mp (normalizer (A : Set Model)).one_mem

/-- Max2 is a genuine two-local, witnessed by the conjugated first core. -/
theorem sourceSubgroup_isTwoLocal : IsTwoLocal sourceSubgroup := by
  have hl := firstCentralizer_isTwoLocal.map_equiv (MulAut.conj h)
  rwa [firstCentralizer_eq_source_conjugate, map_conj_mul, mul_inv_cancel,
    map_conj_one] at hl

/-- A pure involution line has exactly the corresponding native max2 normalizer. -/
theorem first_line_normalizer (x : Model) (hx : IsConj a x) :
    ∃ g : Model, normalizer (zpowers x : Set Model) =
      sourceSubgroup.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g,hg⟩ := isConj_iff.mp hx
  have hx2 : orderOf x = 2 := by
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq a).trans orderOf_a
  rw [normalizer_zpowers_eq_centralizer_of_order_two x hx2]
  refine ⟨g*h⁻¹,?_⟩
  rw [← map_conj_mul, ← firstCentralizer_eq_source_conjugate]
  change centralizer ({x} : Set Model) =
    (centralizer ({a} : Set Model)).map (MulAut.conj g).toMonoidHom
  rw [map_centralizer_equiv, Set.image_singleton]
  change centralizer ({x} : Set Model) = centralizer ({g*a*g⁻¹} : Set Model)
  rw [hg]

/-- The rank-one branch uses no maximality or ambient Sylow hypothesis. -/
theorem order_two_normalizer (X : Subgroup Model) (hcard : Nat.card X = 2)
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x) :
    ∃ g : Model, normalizer (X : Set Model) =
      sourceSubgroup.map (MulAut.conj g).toMonoidHom := by
  have hX : X ≠ ⊥ := by intro he; rw [he,card_bot] at hcard; contradiction
  obtain ⟨x,hx⟩ := ne_bot_iff_exists_ne_one.mp hX
  have hx1 : (x : Model) ≠ 1 := fun he => hx (Subtype.ext he)
  have hxa := hpure x x.property hx1
  have hx2 : orderOf (x : Model) = 2 := by
    obtain ⟨g,hg⟩ := isConj_iff.mp hxa
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq a).trans orderOf_a
  have he : zpowers (x : Model) = X := eq_of_le_of_card_ge
    (zpowers_le.mpr x.property) (by rw [hcard,Nat.card_zpowers,hx2])
  rw [← he]
  exact first_line_normalizer x hxa

/-- The one fixed native input required from the independent eight-normalizer
calculation. Its proof must not invoke the pure first-class cover. -/
abbrev EightNormalizerPlacement : Prop :=
  ∃ g : Model, normalizer (nativeEight 1 : Set Model) ≤
    LinearFive.fullNormalizer.map (MulAut.conj g).toMonoidHom

/-- The whole normalizer of a group whose full centralizer has the source
fusion lies in an actual F local, with the original conjugator retained. -/
theorem fused_eight_normalizer (h8 : EightNormalizerPlacement)
    (X : Subgroup Model) (g : Model)
    (hC : (centralizer (X : Set Model)).map (MulAut.conj g).toMonoidHom = nativeEight 1) :
    ∃ k : Model, normalizer (X : Set Model) ≤
      LinearFive.fullNormalizer.map (MulAut.conj (g⁻¹*k)).toMonoidHom := by
  obtain ⟨k,hk⟩ := h8
  have hn0 := map_mono (f := (MulAut.conj g).toMonoidHom)
    (normalizer_le_normalizer_centralizer X)
  have hn : (normalizer (X : Set Model)).map (MulAut.conj g).toMonoidHom ≤
      normalizer (nativeEight 1 : Set Model) := by
    have hcN : (normalizer (centralizer (X : Set Model) : Set Model)).map
        (MulAut.conj g).toMonoidHom = normalizer (nativeEight 1 : Set Model) := by
      rw [map_equiv_normalizer_eq, hC]
    exact hcN ▸ hn0
  have ht := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) (hn.trans hk)
  rw [map_conj_mul,inv_mul_cancel,map_conj_one,map_conj_mul] at ht
  exact ⟨k,ht⟩

/-- Maximality among TWO-locals gives the exact F equality for the same
native-eight exception of Section 2.1. -/
theorem fused_eight_maximal (h8 : EightNormalizerPlacement)
    (X : Subgroup Model) (g : Model)
    (hC : (centralizer (X : Set Model)).map (MulAut.conj g).toMonoidHom = nativeEight 1)
    (hM : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    ∃ k : Model, normalizer (X : Set Model) =
      LinearFive.fullNormalizer.map (MulAut.conj (g⁻¹*k)).toMonoidHom := by
  obtain ⟨k,hk⟩ := fused_eight_normalizer h8 X g hC
  have hlocal : IsTwoLocal LinearFive.fullNormalizer := by
    rw [← LinearFive.M_F_eq_fullNormalizer]
    exact nativeF_generated_isTwoLocal
  exact ⟨k,hM.eq_of_le (hlocal.map_equiv (MulAut.conj (g⁻¹*k))) hk⟩

/-- The exceptional order-256 branch applied to an original radical. The
whole-eight placement is the only external premise; all restriction maps are
computed in the actual conjugate of `LinearFive.fullNormalizer`. -/
theorem fused_eight_radical (h8 : EightNormalizerPlacement)
    (P X : Subgroup Model) (hP : P.IsPRadical 2)
    (g : Model)
    (hC : (centralizer (X : Set Model)).map (MulAut.conj g).toMonoidHom = nativeEight 1)
    (hNX : normalizer (P : Set Model) ≤ normalizer (X : Set Model)) :
    ∃ k : Model, let M : Subgroup Model :=
      LinearFive.fullNormalizer.map ((MulAut.conj (g⁻¹*k)).toMonoidHom)
      IsTwoLocal M ∧ normalizer (P : Set Model) ≤ M ∧ P ≤ M ∧
      (normalizer (P.subgroupOf M : Set M)).map M.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf M).IsPRadical 2 ∧
      (normalizer (P.subgroupOf M : Set M)).pCoreIn 2 = P.subgroupOf M ∧
      ((normalizer (P.subgroupOf M : Set M)).pCoreIn 2).map M.subtype = P := by
  obtain ⟨k,hk⟩ := fused_eight_normalizer h8 X g hC
  let M : Subgroup Model :=
    LinearFive.fullNormalizer.map ((MulAut.conj (g⁻¹*k)).toMonoidHom)
  have hNM : normalizer (P : Set Model) ≤ M := hNX.trans hk
  have hPM := P.le_normalizer.trans hNM
  have hNN := hNM.trans M.le_normalizer
  have hcore := hP.normalizer_core_subgroupOf M hPM hNN
  have hlocal : IsTwoLocal M := by
    have hF : IsTwoLocal LinearFive.fullNormalizer := by
      rw [← LinearFive.M_F_eq_fullNormalizer]
      exact nativeF_generated_isTwoLocal
    exact hF.map_equiv (MulAut.conj (g⁻¹*k))
  refine ⟨k,hlocal,hNM,hPM,?_,
    hP.subgroupOf_of_normalizer_normalizes M hPM hNN,hcore,?_⟩
  · rw [← subgroupOf_normalizer_eq hPM,map_subgroupOf_eq_of_le hNM]
  · rw [hcore,map_subgroupOf_eq_of_le hPM]

/-- The rank-one source branch applied to an arbitrary original radical,
retaining its literal full normalizer and embedded core maps. -/
theorem order_two_radical (P X : Subgroup Model) (hP : P.IsPRadical 2)
    (hcard : Nat.card X = 2) (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hNX : normalizer (P : Set Model) ≤ normalizer (X : Set Model)) :
    ∃ g : Model, let M := sourceSubgroup.map (MulAut.conj g).toMonoidHom
      IsTwoLocal M ∧ normalizer (P : Set Model) ≤ M ∧ P ≤ M ∧
      (normalizer (P.subgroupOf M : Set M)).map M.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf M).IsPRadical 2 ∧
      (normalizer (P.subgroupOf M : Set M)).pCoreIn 2 = P.subgroupOf M ∧
      ((normalizer (P.subgroupOf M : Set M)).pCoreIn 2).map M.subtype = P := by
  obtain ⟨g,hg⟩ := order_two_normalizer X hcard hpure
  let M := sourceSubgroup.map (MulAut.conj g).toMonoidHom
  have hNM : normalizer (P : Set Model) ≤ M := by
    change normalizer (P : Set Model) ≤ sourceSubgroup.map (MulAut.conj g).toMonoidHom
    rwa [← hg]
  have hPM := P.le_normalizer.trans hNM
  have hNN := hNM.trans M.le_normalizer
  have hc := hP.normalizer_core_subgroupOf M hPM hNN
  refine ⟨g,sourceSubgroup_isTwoLocal.map_equiv (MulAut.conj g),hNM,hPM,?_,
    hP.subgroupOf_of_normalizer_normalizes M hPM hNN,hc,?_⟩
  · rw [← subgroupOf_normalizer_eq hPM,map_subgroupOf_eq_of_le hNM]
  · rw [hc,map_subgroupOf_eq_of_le hPM]

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA
