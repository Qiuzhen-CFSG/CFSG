module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.Centralizers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalEffectiveRadical
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearThreePresentation

/-!
# Exact source centralizers on the original two-core

The actual endpoint equivalence carries the original two-core centralizers
onto the three-factor source centralizer and the perpendicular root fixed
by the full source Suzuki actor. It also carries the original center onto
the radical center, giving the proved perpendicular Omega inclusion there.
Hypothesis F.1.1 discharges the Borel core and local characteristic-two
premises. The final applications use literally Q.q after the original
parabolic inclusion; no original ambient finiteness is required.

Source: Fong--Seitz I (1973), proof of (6H)(c),(g), printed p.55.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (split : SplitData Q.tits)
  (n : ℕ) (hn : Odd n) (m : ℕ)
  (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
  (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q 1).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup m : Set _))

private theorem endpoint_image (A : Subgroup (X ⧸ Q.D)) (hA : A ≤ Endpoint Q 1) :
    (A.comap (endpointMap Q e 1)).map (endpointMap Q e 1) = A := by
  have hr : (endpointMap Q e 1).range = Endpoint Q 1 := by
    rw [endpointMap,MonoidHom.range_comp,MonoidHom.range_eq_top.mpr (endpoint Q e 1).surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  rw [map_comap_eq,hr]
  exact inf_eq_right.mpr hA

include μ hB in
private theorem core_centralizer_image (A : Subgroup (X ⧸ Q.D)) (hA : A ≤ Endpoint Q 1) :
    (pCore 2 (parabolic L S 1) ⊓ centralizer (A.comap (endpointMap Q e 1) : Set (parabolic L S 1))).map
      (endpointMap Q e 1) = simpleRemainder Q split 1 ⊓ centralizer (A : Set (X ⧸ Q.D)) := by
  let f := originalCoreCentralizerEquiv Q e split 1
    (marked_suzuki_remainder_le_kernel Q split 1 m μ hB)
    (A.comap (endpointMap Q e 1) : Set (parabolic L S 1))
  have he : endpointMap Q e 1 '' (A.comap (endpointMap Q e 1) : Set (parabolic L S 1)) =
      (A : Set (X ⧸ Q.D)) := congrArg (fun R : Subgroup (X ⧸ Q.D) => (R : Set (X ⧸ Q.D)))
        (endpoint_image Q e A hA)
  have hf : (pCore 2 (parabolic L S 1) ⊓ centralizer (A.comap (endpointMap Q e 1) : Set (parabolic L S 1))).map
      (endpointMap Q e 1) = simpleRemainder Q split 1 ⊓ centralizer
        (endpointMap Q e 1 '' (A.comap (endpointMap Q e 1) : Set (parabolic L S 1))) := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact (f ⟨x,hx⟩).property
    · intro hz
      obtain ⟨x,hx⟩ := f.surjective ⟨z,hz⟩
      exact ⟨x,x.property,congrArg Subtype.val hx⟩
  rwa [he] at hf

include ν hC μ hB hn in
/-- The original two-core centralizer has the literal three-factor image and order q⁴. -/
theorem original_source_suzuki_radical_centralizer
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    (((pCore 2 (parabolic L S 1) ⊓ centralizer
      ((simpleRoot Q split 1).comap (endpointMap Q e 1) : Set (parabolic L S 1))).map
        (endpointMap Q e 1) : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) =
      (rootAt Q split 0 (Q.simple 1) : Set (X ⧸ Q.D)) *
      (omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) : Set (X ⧸ Q.D)) *
      (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) : Set (X ⧸ Q.D)) ∧
    Nat.card (pCore 2 (parabolic L S 1) ⊓ centralizer
      ((simpleRoot Q split 1).comap (endpointMap Q e 1) : Set (parabolic L S 1)) :
        Subgroup (parabolic L S 1)) = (2^(2*m+1))^4 := by
  have hA : simpleRoot Q split 1 ≤ Endpoint Q 1 := (simpleRoot_le Q split 1).trans (split.U_le.trans (Q.tits.B_le_standardParabolic _))
  have hi := core_centralizer_image Q e split m μ hB (simpleRoot Q split 1) hA
  have hs := source_suzuki_radical_centralizer Q split n hn m ν T hC μ hB hm
    (LinearThreePresentation.borel_core_eq_bot Q e h) (parabolic_core_selfCentralizing Q e h 1)
  constructor
  · rw [hi]; exact hs.1
  · rw [←card_map_of_injective (f := endpointMap Q e 1)
      ((Endpoint Q 1).subtype_injective.comp (endpoint Q e 1).injective),hi]
    exact hs.2

include ν hC μ hB hn in
/-- The original two-core fixed by the full pulled-back Suzuki actor maps exactly to E. -/
theorem original_source_suzuki_actor_radical_centralizer
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    (pCore 2 (parabolic L S 1) ⊓ centralizer
      ((rankOne Q split 1).comap (endpointMap Q e 1) : Set (parabolic L S 1))).map (endpointMap Q e 1) =
      rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) := by
  rw [core_centralizer_image Q e split m μ hB _ (rankOne_le_parabolic Q split 1)]
  exact source_suzuki_actor_radical_centralizer Q split n hn m ν T hC μ hB hm
    (LinearThreePresentation.borel_core_eq_bot Q e h) (parabolic_core_selfCentralizing Q e h 1)

include ν hC μ hB hn in
/-- The perpendicular Omega is in the actual image of the original two-core center. -/
theorem original_source_perpendicular_omega_le_center_image
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) ≤
      (center (pCore 2 (parabolic L S 1))).map
        ((endpointMap Q e 1).comp (pCore 2 (parabolic L S 1)).subtype) := by
  let hV := marked_suzuki_remainder_le_kernel Q split 1 m μ hB
  let f := originalRadicalEquiv Q e split 1 hV
  have he : (endpointMap Q e 1).comp (pCore 2 (parabolic L S 1)).subtype =
      (simpleRemainder Q split 1).subtype.comp f.toMonoidHom := by
    ext x
    exact (originalRadicalEquiv_apply Q e split 1 hV x).symm
  rw [he,←map_map,center_map_equiv]
  exact (source_perpendicular_omega_le_centers Q split n hn m ν T hC μ hB hm
    (LinearThreePresentation.borel_core_eq_bot Q e h) (parabolic_core_selfCentralizing Q e h 1)).2

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits)
  (n : ℕ) (hn : Odd n) (m : ℕ)
  (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
  (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q 1).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup m : Set _))


include ν hC μ hB hn in
/-- The preceding identity with the literal original quotient homomorphism Q.q. -/
theorem original_source_suzuki_radical_centralizer_quotient
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    (((pCore 2 (parabolic L S 1) ⊓ centralizer
      ((simpleRoot Q split 1).comap (Q.q.comp (inclusion (parabolic_le_generated 1))) : Set (parabolic L S 1))).map
        (Q.q.comp (inclusion (parabolic_le_generated 1))) : Subgroup ((generated L S) ⧸ Q.D)) : Set ((generated L S) ⧸ Q.D)) =
      (rootAt Q split 0 (Q.simple 1) : Set ((generated L S) ⧸ Q.D)) *
      (omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) : Set ((generated L S) ⧸ Q.D)) *
      (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) : Set ((generated L S) ⧸ Q.D)) ∧
    Nat.card (pCore 2 (parabolic L S 1) ⊓ centralizer
      ((simpleRoot Q split 1).comap (Q.q.comp (inclusion (parabolic_le_generated 1))) : Set (parabolic L S 1)) :
        Subgroup (parabolic L S 1)) = (2^(2*m+1))^4 := by
  have hf : Q.q.comp (inclusion (parabolic_le_generated 1)) =
      MarkedLocal.endpointMap Q (originalMarkedIso Q) 1 := by
    ext g
    exact (originalMarkedIso_right_apply Q g).symm
  rw [hf]
  exact original_source_suzuki_radical_centralizer Q (originalMarkedIso Q) split n hn m ν T hC μ hB h hm

include ν hC μ hB hn in
/-- The preceding identity with the literal original quotient homomorphism Q.q. -/
theorem original_source_suzuki_actor_radical_centralizer_quotient
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    (pCore 2 (parabolic L S 1) ⊓ centralizer
      ((rankOne Q split 1).comap (Q.q.comp (inclusion (parabolic_le_generated 1))) : Set (parabolic L S 1))).map (Q.q.comp (inclusion (parabolic_le_generated 1))) =
      rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) := by
  have hf : Q.q.comp (inclusion (parabolic_le_generated 1)) =
      MarkedLocal.endpointMap Q (originalMarkedIso Q) 1 := by
    ext g
    exact (originalMarkedIso_right_apply Q g).symm
  rw [hf]
  exact original_source_suzuki_actor_radical_centralizer Q (originalMarkedIso Q) split n hn m ν T hC μ hB h hm

include ν hC μ hB hn in
/-- The preceding identity with the literal original quotient homomorphism Q.q. -/
theorem original_source_perpendicular_omega_le_center_image_quotient
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) :
    omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) ≤
      (center (pCore 2 (parabolic L S 1))).map
        ((Q.q.comp (inclusion (parabolic_le_generated 1))).comp (pCore 2 (parabolic L S 1)).subtype) := by
  have hf : Q.q.comp (inclusion (parabolic_le_generated 1)) =
      MarkedLocal.endpointMap Q (originalMarkedIso Q) 1 := by
    ext g
    exact (originalMarkedIso_right_apply Q g).symm
  rw [hf]
  exact original_source_perpendicular_omega_le_center_image Q (originalMarkedIso Q) split n hn m ν T hC μ hB h hm

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
