module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.PositivePerpendicularBranch
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalSmallCharacteristic

/-!
# Original endpoint applications of positive perpendicular support

The original core equivalences identify both its Frattini and derived images
inside the same marked quotient. A whole perpendicular root in the former
image forces the near equality. In the vanishing near-commutator branch both
images meet the perpendicular root in precisely Omega. The endpoint maps and
the specialization to Q.q preserve the full original marking in either
orientation, without assuming the original ambient group finite.

Source: Fong--Seitz I (1973), pp.52--53, the positive branch of (6H)(b).
The remaining proper-support branch, field pairing, and odd degree are not
asserted here. The original F.1.1 hypothesis supplies core self-centralization.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (split : SplitData Q.tits) (i j : Fin 2)
  (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup m : Set _))
  (n : ℕ) (hn : 0 < n)
  (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set _))

private theorem endpoint_image (A : Subgroup (X ⧸ Q.D)) (hA : A ≤ Endpoint Q i) :
    (A.comap (endpointMap Q e i)).map (endpointMap Q e i) = A := by
  have hr : (endpointMap Q e i).range = Endpoint Q i := by
    rw [endpointMap,MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (endpoint Q e i).surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  rw [map_comap_eq,hr]
  exact inf_eq_right.mpr hA

include e μ hB in
private theorem core_images :
    (frattini (pCore 2 (parabolic L S i))).map
        ((endpointMap Q e i).comp (pCore 2 (parabolic L S i)).subtype) =
      (frattini (simpleRemainder Q split i)).map (simpleRemainder Q split i).subtype ∧
    (commutator (pCore 2 (parabolic L S i))).map
        ((endpointMap Q e i).comp (pCore 2 (parabolic L S i)).subtype) =
      (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)) := by
  let hV := marked_suzuki_remainder_le_kernel Q split i m μ hB
  constructor
  · apply le_antisymm
    · rintro x ⟨v,hv,rfl⟩
      exact (originalPhiRadicalEquiv Q e split i hV ⟨v,hv⟩).property
    · intro x hx
      obtain ⟨v,hv⟩ := (originalPhiRadicalEquiv Q e split i hV).surjective ⟨x,hx⟩
      exact ⟨v.val,v.property,congrArg Subtype.val hv⟩
  · apply le_antisymm
    · rintro x ⟨v,hv,rfl⟩
      exact (originalDerivedRadicalEquiv Q e split i hV ⟨v,hv⟩).property
    · intro x hx
      obtain ⟨v,hv⟩ := (originalDerivedRadicalEquiv Q e split i hV).surjective ⟨x,hx⟩
      exact ⟨v.val,v.property,congrArg Subtype.val hv⟩

private theorem near_images (hm : rotationOrder Q = 8) (hij : i ≠ j) :
    ((simpleRoot Q split i).comap (endpointMap Q e i)).map (endpointMap Q e i) =
      simpleRoot Q split i ∧
    ((rootAt Q split i (Q.simple j*Q.simple i)).comap (endpointMap Q e i)).map
      (endpointMap Q e i) = rootAt Q split i (Q.simple j*Q.simple i) ∧
    ((rootAt Q split j (Q.simple i)).comap (endpointMap Q e i)).map (endpointMap Q e i) =
      rootAt Q split j (Q.simple i) := by
  have hp : split.U ≤ Endpoint Q i := split.U_le.trans (Q.tits.B_le_standardParabolic _)
  have hv := octagon_three_roots_le_remainder Q split hm i j hij
  exact ⟨endpoint_image Q e i _ ((simpleRoot_le Q split i).trans hp),
    endpoint_image Q e i _ (hv.2.1.trans (inf_le_left.trans hp)),
    endpoint_image Q e i _ (hv.1.trans (inf_le_left.trans hp))⟩

include e μ hB hn ν hC in
/-- Original whole-root Frattini containment discharges the near-equality branch. -/
theorem original_positive_near_eq_of_perpendicular_le_frattini
    (h : HypothesisF11 L S) (hmpos : 0 < m) (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : Nat.card (BinaryGaloisField n) ≤ 2^(2*m+1))
    (hE : rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) ≤
      (frattini (pCore 2 (parabolic L S i))).map
        ((endpointMap Q e i).comp (pCore 2 (parabolic L S i)).subtype)) :
    ⁅(simpleRoot Q split i).comap (endpointMap Q e i),
      (rootAt Q split i (Q.simple j*Q.simple i)).comap (endpointMap Q e i)⁆ =
      (rootAt Q split j (Q.simple i)).comap (endpointMap Q e i) := by
  rw [(core_images Q e split i m μ hB).1] at hE
  have he := near_images Q e split i j hm hij
  apply map_injective (f := endpointMap Q e i)
    ((Endpoint Q i).subtype_injective.comp (endpoint Q e i).injective)
  rw [map_commutator,he.1,he.2.1,he.2.2]
  exact source_positive_near_eq_of_perpendicular_le_frattini Q split i j m μ hB n hn ν T hC
    hmpos (parabolic_core_selfCentralizing Q e h i) hm hij hsize hE

include e μ hB hn ν hC in
/-- Both original core images have exactly Omega perpendicular support in the near-zero branch. -/
theorem original_positive_perpendicular_support_of_near_trivial
    (h : HypothesisF11 L S) (hmpos : 0 < m) (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : Nat.card (BinaryGaloisField n) ≤ 2^(2*m+1))
    (hnear : ⁅(simpleRoot Q split i).comap (endpointMap Q e i),
      (rootAt Q split i (Q.simple j*Q.simple i)).comap (endpointMap Q e i)⁆ = ⊥) :
    let f := (endpointMap Q e i).comp (pCore 2 (parabolic L S i)).subtype
    let E := rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)
    (frattini (pCore 2 (parabolic L S i))).map f ⊓ E = omegaOneAmbient E ∧
      (commutator (pCore 2 (parabolic L S i))).map f ⊓ E = omegaOneAmbient E := by
  have he := near_images Q e split i j hm hij
  have hh := congrArg (fun A : Subgroup (parabolic L S i) => A.map (endpointMap Q e i)) hnear
  rw [map_commutator,he.1,he.2.1,Subgroup.map_bot] at hh
  dsimp only
  rw [(core_images Q e split i m μ hB).1,(core_images Q e split i m μ hB).2]
  exact ⟨source_positive_perpendicular_frattini_of_near_trivial Q split i j m μ hB n hn ν T hC
      hmpos (parabolic_core_selfCentralizing Q e h i) hm hij hsize hh,
    source_positive_perpendicular_derived_of_near_trivial Q split i j m μ hB n hn ν T hC
      hmpos (parabolic_core_selfCentralizing Q e h i) hm hij hsize hh⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits) (i j : Fin 2)
  (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup m : Set _))
  (n : ℕ) (hn : 0 < n)
  (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set _))

include μ hB hn ν hC in
/-- Whole-root containment in the literal Q.q Frattini image gives the original near equality. -/
theorem original_positive_near_eq_of_perpendicular_le_frattini_quotient
    (h : HypothesisF11 L S) (hmpos : 0 < m) (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : Nat.card (BinaryGaloisField n) ≤ 2^(2*m+1))
    (hE : rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) ≤
      (frattini (pCore 2 (parabolic L S i))).map
        ((Q.q.comp (inclusion (parabolic_le_generated i))).comp (pCore 2 (parabolic L S i)).subtype)) :
    ⁅(simpleRoot Q split i).comap (Q.q.comp (inclusion (parabolic_le_generated i))),
      (rootAt Q split i (Q.simple j*Q.simple i)).comap
        (Q.q.comp (inclusion (parabolic_le_generated i)))⁆ =
      (rootAt Q split j (Q.simple i)).comap (Q.q.comp (inclusion (parabolic_le_generated i))) := by
  have hf : Q.q.comp (inclusion (parabolic_le_generated i)) =
      MarkedLocal.endpointMap Q (originalMarkedIso Q) i := by
    ext g
    fin_cases i
    · exact (originalMarkedIso_left_apply Q g).symm
    · exact (originalMarkedIso_right_apply Q g).symm
  rw [hf] at hE ⊢
  exact original_positive_near_eq_of_perpendicular_le_frattini Q (originalMarkedIso Q)
    split i j m μ hB n hn ν T hC h hmpos hm hij hsize hE

include μ hB hn ν hC in
/-- The remaining branch has exact perpendicular support in both literal Q.q core images. -/
theorem original_positive_perpendicular_support_of_near_trivial_quotient
    (h : HypothesisF11 L S) (hmpos : 0 < m) (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : Nat.card (BinaryGaloisField n) ≤ 2^(2*m+1))
    (hnear : ⁅(simpleRoot Q split i).comap (Q.q.comp (inclusion (parabolic_le_generated i))),
      (rootAt Q split i (Q.simple j*Q.simple i)).comap
        (Q.q.comp (inclusion (parabolic_le_generated i)))⁆ = ⊥) :
    let f := (Q.q.comp (inclusion (parabolic_le_generated i))).comp (pCore 2 (parabolic L S i)).subtype
    let E := rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)
    (frattini (pCore 2 (parabolic L S i))).map f ⊓ E = omegaOneAmbient E ∧
      (commutator (pCore 2 (parabolic L S i))).map f ⊓ E = omegaOneAmbient E := by
  have hf : Q.q.comp (inclusion (parabolic_le_generated i)) =
      MarkedLocal.endpointMap Q (originalMarkedIso Q) i := by
    ext g
    fin_cases i
    · exact (originalMarkedIso_left_apply Q g).symm
    · exact (originalMarkedIso_right_apply Q g).symm
  dsimp only
  rw [hf] at hnear ⊢
  exact original_positive_perpendicular_support_of_near_trivial Q (originalMarkedIso Q)
    split i j m μ hB n hn ν T hC h hmpos hm hij hsize hnear
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
