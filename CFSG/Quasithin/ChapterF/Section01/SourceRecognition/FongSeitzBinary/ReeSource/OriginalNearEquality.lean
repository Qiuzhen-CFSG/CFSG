module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.BinaryTerminal

/-!
# Original endpoint and quotient applications of the near-root equality

Injectivity of either original endpoint map transports the marked equality
of the near commutator with the whole intervening linear root. The general
parameter theorem retains its nonzero premise. The binary theorem uses the
completed two-case p.53 proof and needs no nonzero or Omega-movement premise.
F.1.1 supplies its two-core self-centralization on the actual quotient.

Both results specialize to Q.q composed with the original parabolic
inclusion. The full original markings and both endpoint orientations are
retained; the original ambient group need not be finite. Natural panel
markings and the binary linear size comparison remain explicit. The
positive-parameter source case and remaining (6H) obligations are unfinished.

Source: Fong--Seitz I (1973), the equality in (6H)(b), pp.53--54.
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

include e in
/-- A nonzero near commutator is the whole intervening root on the original
endpoint, with the full original hypotheses and either orientation retained. -/
theorem original_source_near_eq_of_nonzero
    (_h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (n : ℕ) (hn : 0 < n)
    (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set _))
    (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
    (hB : (quotientBorel Q i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set _))
    (hne : ⁅(simpleRoot Q split i).comap (endpointMap Q e i),
      (rootAt Q split i (Q.simple j * Q.simple i)).comap (endpointMap Q e i)⁆ ≠ ⊥) :
    ⁅(simpleRoot Q split i).comap (endpointMap Q e i),
      (rootAt Q split i (Q.simple j * Q.simple i)).comap (endpointMap Q e i)⁆ =
      (rootAt Q split j (Q.simple i)).comap (endpointMap Q e i) := by
  have hi : Function.Injective (endpointMap Q e i) :=
    (Endpoint Q i).subtype_injective.comp (endpoint Q e i).injective
  have he := endpoint_root_images Q e split i j hm hij
  have hnz : ⁅simpleRoot Q split i,
      rootAt Q split i (Q.simple j * Q.simple i)⁆ ≠ ⊥ := by
    intro hz
    apply hne
    apply map_injective (f := endpointMap Q e i) hi
    rw [map_commutator, he.1, he.2.1, Subgroup.map_bot, hz]
  apply map_injective (f := endpointMap Q e i) hi
  rw [map_commutator, he.1, he.2.1, he.2.2]
  exact source_near_eq_of_nonzero Q split i j m μ hB n hn ν T hC hm hij hnz

/-- Both binary terminal branches are discharged on either original endpoint.
F.1.1 supplies the actual two-core self-centralization. -/
theorem original_source_binary_near_eq
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (n : ℕ) (hn : 0 < n)
    (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set _))
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup 0)
    (hB : (quotientBorel Q i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup 0 : Set _))
    (hsize : Nat.card (BinaryGaloisField n) ≤ 2) :
    ⁅(simpleRoot Q split i).comap (endpointMap Q e i),
      (rootAt Q split i (Q.simple j*Q.simple i)).comap (endpointMap Q e i)⁆ =
      (rootAt Q split j (Q.simple i)).comap (endpointMap Q e i) := by
  have hi : Function.Injective (endpointMap Q e i) :=
    (Endpoint Q i).subtype_injective.comp (endpoint Q e i).injective
  have he := endpoint_root_images Q e split i j hm hij
  apply map_injective (f := endpointMap Q e i) hi
  rw [map_commutator,he.1,he.2.1,he.2.2]
  exact source_binary_near_eq Q split i j μ hB n hn ν T hC
    (parabolic_core_selfCentralizing Q e h i) hm hij hsize

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits) (i j : Fin 2)

include i j in
/-- The same equality with the literal generated-carrier quotient `Q.q`. -/
theorem original_source_near_eq_of_nonzero_quotient
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (n : ℕ) (hn : 0 < n)
    (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set _))
    (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
    (hB : (quotientBorel Q i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set _))
    (hne : ⁅(simpleRoot Q split i).comap
        (Q.q.comp (Subgroup.inclusion (parabolic_le_generated i))),
      (rootAt Q split i (Q.simple j * Q.simple i)).comap
        (Q.q.comp (Subgroup.inclusion (parabolic_le_generated i)))⁆ ≠ ⊥) :
    ⁅(simpleRoot Q split i).comap
        (Q.q.comp (Subgroup.inclusion (parabolic_le_generated i))),
      (rootAt Q split i (Q.simple j * Q.simple i)).comap
        (Q.q.comp (Subgroup.inclusion (parabolic_le_generated i)))⁆ =
      (rootAt Q split j (Q.simple i)).comap
        (Q.q.comp (Subgroup.inclusion (parabolic_le_generated i))) := by
  have hf : Q.q.comp (Subgroup.inclusion (parabolic_le_generated i)) =
      MarkedLocal.endpointMap Q (originalMarkedIso Q) i := by
    ext g
    fin_cases i
    · exact (originalMarkedIso_left_apply Q g).symm
    · exact (originalMarkedIso_right_apply Q g).symm
  rw [hf] at hne ⊢
  exact original_source_near_eq_of_nonzero Q (originalMarkedIso Q) split i j h hm hij
    n hn ν T hC m μ hB hne

/-- The binary equality on the literal generated-carrier quotient, with no
commutator nonvanishing or movement premise. -/
theorem original_source_binary_near_eq_quotient
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (n : ℕ) (hn : 0 < n)
    (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set _))
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup 0)
    (hB : (quotientBorel Q i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup 0 : Set _))
    (hsize : Nat.card (BinaryGaloisField n) ≤ 2) :
    ⁅(simpleRoot Q split i).comap
        (Q.q.comp (Subgroup.inclusion (parabolic_le_generated i))),
      (rootAt Q split i (Q.simple j*Q.simple i)).comap
        (Q.q.comp (Subgroup.inclusion (parabolic_le_generated i)))⁆ =
      (rootAt Q split j (Q.simple i)).comap
        (Q.q.comp (Subgroup.inclusion (parabolic_le_generated i))) := by
  have hf : Q.q.comp (Subgroup.inclusion (parabolic_le_generated i)) =
      MarkedLocal.endpointMap Q (originalMarkedIso Q) i := by
    ext g
    fin_cases i
    · exact (originalMarkedIso_left_apply Q g).symm
    · exact (originalMarkedIso_right_apply Q g).symm
  rw [hf]
  exact original_source_binary_near_eq Q (originalMarkedIso Q) split i j h hm hij
    n hn ν T hC μ hB hsize

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
