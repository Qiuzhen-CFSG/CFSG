module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.PositiveNearEquality

/-!
# The complete near-root equality on the original source

The injective original endpoint map transports the equality on the same
marked quotient. F.1.1 supplies two-core self-centralization. The second
theorem retains Q.q composed with the original parabolic inclusion; the
ambient original group need not be finite. Both full endpoint markings
are retained in the original amalgam isomorphism.

Source: Fong--Seitz I (1973), (6H)(b), pp.53--54. Natural panel markings,
odd linear degree and faithful Borel remain earlier source inputs. All
Suzuki parameters are covered, including the full binary case.
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

private theorem endpoint_subgroup_image (A : Subgroup (X ⧸ Q.D))
    (hA : A ≤ Endpoint Q i) :
    (A.comap (endpointMap Q e i)).map (endpointMap Q e i) = A := by
  have hr : (endpointMap Q e i).range = Endpoint Q i := by
    rw [endpointMap, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (endpoint Q e i).surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  rw [map_comap_eq, hr]
  exact inf_eq_right.mpr hA

private theorem endpoint_root_images (hm : rotationOrder Q = 8)
    (hij : i ≠ j) :
    ((simpleRoot Q split i).comap (endpointMap Q e i)).map (endpointMap Q e i) =
        simpleRoot Q split i ∧
    ((rootAt Q split i (Q.simple j * Q.simple i)).comap (endpointMap Q e i)).map
        (endpointMap Q e i) = rootAt Q split i (Q.simple j * Q.simple i) ∧
    ((rootAt Q split j (Q.simple i)).comap (endpointMap Q e i)).map
        (endpointMap Q e i) = rootAt Q split j (Q.simple i) := by
  have hV := octagon_three_roots_le_remainder Q split hm i j hij
  have hUP : split.U ≤ Endpoint Q i :=
    split.U_le.trans (Q.tits.B_le_standardParabolic _)
  exact ⟨endpoint_subgroup_image Q e i _ ((simpleRoot_le Q split i).trans hUP),
    endpoint_subgroup_image Q e i _ (hV.2.1.trans (inf_le_left.trans hUP)),
    endpoint_subgroup_image Q e i _ (hV.1.trans (inf_le_left.trans hUP))⟩


/-- The complete near-root equality on the original marked endpoint.
Odd linear degree remains an earlier source premise; no mixed-commutator
premise remains and every Suzuki parameter is included. -/
theorem original_source_near_eq_of_odd_degree
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (n : ℕ) (hn : Odd n)
    (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
    (m : ℕ) (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
    (hB : (quotientBorel Q 1).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup m : Set _)) :
    ⁅(simpleRoot Q split 1).comap (endpointMap Q e 1),
      (rootAt Q split 1 (Q.simple 0*Q.simple 1)).comap (endpointMap Q e 1)⁆ =
      (rootAt Q split 0 (Q.simple 1)).comap (endpointMap Q e 1) := by
  have he := endpoint_root_images Q e split 1 0 hm (by decide)
  apply map_injective (f := endpointMap Q e 1)
    ((Endpoint Q 1).subtype_injective.comp (endpoint Q e 1).injective)
  rw [map_commutator,he.1,he.2.1,he.2.2]
  exact source_near_eq_of_odd_degree Q split n hn m ν T hC μ hB hm hcore
    (parabolic_core_selfCentralizing Q e h 1)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits)

/-- The complete near equality through the literal quotient map of the
original generated carrier, with the original parabolic inclusion. -/
theorem original_source_near_eq_of_odd_degree_quotient
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (n : ℕ) (hn : Odd n)
    (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
    (m : ℕ) (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
    (hB : (quotientBorel Q 1).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup m : Set _)) :
    ⁅(simpleRoot Q split 1).comap (Q.q.comp (inclusion (parabolic_le_generated 1))),
      (rootAt Q split 1 (Q.simple 0*Q.simple 1)).comap (Q.q.comp (inclusion (parabolic_le_generated 1)))⁆ =
      (rootAt Q split 0 (Q.simple 1)).comap (Q.q.comp (inclusion (parabolic_le_generated 1))) := by
  have hf : Q.q.comp (inclusion (parabolic_le_generated 1)) =
      MarkedLocal.endpointMap Q (originalMarkedIso Q) 1 := by
    ext g
    exact (originalMarkedIso_right_apply Q g).symm
  rw [hf]
  exact original_source_near_eq_of_odd_degree Q (originalMarkedIso Q) split h hm hcore n hn ν T hC m μ hB

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
