module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.PerpendicularNonzero

/-!
# Original endpoint applications of the source nonzero reductions

The actual endpoint equivalence transports each of the three shifted roots,
the whole near commutator, and the perpendicular normalizer condition.
Injectivity also transports the literal Omega subgroup in the binary case.
Hypothesis F.1.1 supplies self-centralization of the endpoint two-core.
The common-field specialization discharges the size comparison using the
existing theorem with its odd-linear-degree premise still explicit.

Both final theorems use exactly Q.q composed with the original parabolic
inclusion. They keep the full original endpoint and either orientation;
there is no finiteness assumption on the ambient group. The second
alternatives remain to be excluded by the preceding positive and binary
arguments on p.53. Pairing, odd degree, the rest of (6H), Section 10 and
the final full-model marked comparison remain unfinished.

Source: Fong--Seitz I (1973), terminal contradictions in (6H)(b), pp.53--54.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
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

private theorem endpoint_subgroup_image (A : Subgroup (X ⧸ Q.D)) (hA : A ≤ Endpoint Q i) :
    (A.comap (endpointMap Q e i)).map (endpointMap Q e i) = A := by
  have hr : (endpointMap Q e i).range = Endpoint Q i := by
    rw [endpointMap,MonoidHom.range_comp,MonoidHom.range_eq_top.mpr (endpoint Q e i).surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  rw [map_comap_eq,hr]
  exact inf_eq_right.mpr hA

private theorem endpoint_root_images (hm : rotationOrder Q = 8) (hij : i ≠ j) :
    ((simpleRoot Q split i).comap (endpointMap Q e i)).map (endpointMap Q e i) = simpleRoot Q split i ∧
    ((rootAt Q split i (Q.simple j*Q.simple i)).comap (endpointMap Q e i)).map (endpointMap Q e i) =
      rootAt Q split i (Q.simple j*Q.simple i) ∧
    ((rootAt Q split j (Q.simple i)).comap (endpointMap Q e i)).map (endpointMap Q e i) =
      rootAt Q split j (Q.simple i) ∧
    ((rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)).comap (endpointMap Q e i)).map (endpointMap Q e i) =
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) := by
  have hV := octagon_three_roots_le_remainder Q split hm i j hij
  have hUP := split.U_le.trans (Q.tits.B_le_standardParabolic {Q.simple i})
  exact ⟨endpoint_subgroup_image Q e i _ ((simpleRoot_le Q split i).trans hUP),
    endpoint_subgroup_image Q e i _ (hV.2.1.trans (inf_le_left.trans hUP)),
    endpoint_subgroup_image Q e i _ (hV.1.trans (inf_le_left.trans hUP)),
    endpoint_subgroup_image Q e i _ (hV.2.2.trans (inf_le_left.trans hUP))⟩

/-- The full original endpoint satisfies the terminal source reduction, in either orientation. -/
theorem original_source_near_eq_or_perpendicular_not_normalized
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (n : ℕ) (hn : 0 < n) (m : ℕ)
    (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set _))
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
    (hB : (quotientBorel Q i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (hsize : Nat.card (BinaryGaloisField n) ≤ 2^(2*m+1)) :
    ⁅(simpleRoot Q split i).comap (endpointMap Q e i),
      (rootAt Q split i (Q.simple j*Q.simple i)).comap (endpointMap Q e i)⁆ =
      (rootAt Q split j (Q.simple i)).comap (endpointMap Q e i) ∨
    ¬ (simpleRoot Q split i).comap (endpointMap Q e i) ≤ normalizer
      ((rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)).comap (endpointMap Q e i) :
        Set (parabolic L S i)) := by
  have he := endpoint_root_images Q e split i j hm hij
  rcases source_near_eq_or_perpendicular_not_normalized Q split i j m μ hB n hn ν T hC
    (parabolic_core_selfCentralizing Q e h i) hm hij hsize with hh | hh
  · left
    apply map_injective (f := endpointMap Q e i)
      ((Endpoint Q i).subtype_injective.comp (endpoint Q e i).injective)
    rw [map_commutator,he.1,he.2.1,he.2.2.1]
    exact hh
  · right
    intro hnrm
    apply hh
    have hnmap := (map_mono (f := endpointMap Q e i) hnrm).trans (le_normalizer_map _)
    rwa [he.1,he.2.2.2] at hnmap

/-- The binary original endpoint reduction retains the literal Omega commutator. -/
theorem original_source_binary_near_eq_or_omega_perpendicular_nonzero
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (n : ℕ) (hn : 0 < n)
    (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set _))
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup 0)
    (hB : (quotientBorel Q i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)))
    (hsize : Nat.card (BinaryGaloisField n) = 2) :
    ⁅(simpleRoot Q split i).comap (endpointMap Q e i),
      (rootAt Q split i (Q.simple j*Q.simple i)).comap (endpointMap Q e i)⁆ =
      (rootAt Q split j (Q.simple i)).comap (endpointMap Q e i) ∨
    ⁅omegaOneAmbient ((simpleRoot Q split i).comap (endpointMap Q e i)),
      (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)).comap (endpointMap Q e i)⁆ ≠ ⊥ := by
  have hi := (Endpoint Q i).subtype_injective.comp (endpoint Q e i).injective
  have he := endpoint_root_images Q e split i j hm hij
  rcases source_binary_near_eq_or_omega_perpendicular_nonzero Q split i j n hn ν T hC μ hB
    (parabolic_core_selfCentralizing Q e h i) hm hij hsize with hh | hh
  · left
    apply map_injective (f := endpointMap Q e i) hi
    rw [map_commutator,he.1,he.2.1,he.2.2.1]
    exact hh
  · right
    intro hz
    apply hh
    have hmapped := congrArg (Subgroup.map (endpointMap Q e i)) hz
    rwa [map_commutator,Subgroup.map_bot,map_omegaOneAmbient_injective _ hi,he.1,he.2.2.2] at hmapped

/-- The existing common-field theorem supplies the size comparison, with odd degree retained. -/
theorem original_source_near_reduction_of_odd_degree
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8)
    (n : ℕ) (hn : Odd n) (m : ℕ)
    (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
    (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
    (hB : (quotientBorel Q 1).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (hcore : Q.tits.B.normalCore = ⊥) :
    ⁅(simpleRoot Q split 1).comap (endpointMap Q e 1),
      (rootAt Q split 1 (Q.simple 0*Q.simple 1)).comap (endpointMap Q e 1)⁆ =
      (rootAt Q split 0 (Q.simple 1)).comap (endpointMap Q e 1) ∨
    ¬ (simpleRoot Q split 1).comap (endpointMap Q e 1) ≤ normalizer
      ((rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)).comap (endpointMap Q e 1) :
        Set (parabolic L S 1)) := by
  let : NeZero n := ⟨hn.pos.ne'⟩
  have he := ree_common_field_exponent Q split hm n hn m ν T hC μ hB
    (UnitarySource.actorReflection Q split) hcore
  apply original_source_near_eq_or_perpendicular_not_normalized Q e split 1 0 h hm
    (by decide) n hn.pos m ν T hC μ hB
  rw [GaloisField.card 2 n hn.pos.ne',he]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits) (i j : Fin 2)

/-- The terminal reduction pulled back through the literal original quotient homomorphism. -/
theorem original_source_near_reduction_quotient
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (n : ℕ) (hn : 0 < n) (m : ℕ)
    (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set _))
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
    (hB : (quotientBorel Q i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (hsize : Nat.card (BinaryGaloisField n) ≤ 2^(2*m+1)) :
    let f : parabolic L S i →* (generated L S) ⧸ Q.D :=
      Q.q.comp (Subgroup.inclusion (parabolic_le_generated i))
    ⁅(simpleRoot Q split i).comap f,
      (rootAt Q split i (Q.simple j*Q.simple i)).comap f⁆ =
      (rootAt Q split j (Q.simple i)).comap f ∨
    ¬ (simpleRoot Q split i).comap f ≤ normalizer
      ((rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)).comap f : Set (parabolic L S i)) := by
  dsimp only
  have hf : Q.q.comp (Subgroup.inclusion (parabolic_le_generated i)) =
      MarkedLocal.endpointMap Q (originalMarkedIso Q) i := by
    ext g
    fin_cases i
    · exact (originalMarkedIso_left_apply Q g).symm
    · exact (originalMarkedIso_right_apply Q g).symm
  rw [hf]
  exact original_source_near_eq_or_perpendicular_not_normalized Q (originalMarkedIso Q) split i j
    h hm hij n hn m ν T hC μ hB hsize

/-- The binary reduction uses the literal Q.q and Omega of its actual pulled-back root. -/
theorem original_source_binary_near_reduction_quotient
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (n : ℕ) (hn : 0 < n)
    (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set _))
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup 0)
    (hB : (quotientBorel Q i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)))
    (hsize : Nat.card (BinaryGaloisField n) = 2) :
    let f : parabolic L S i →* (generated L S) ⧸ Q.D :=
      Q.q.comp (Subgroup.inclusion (parabolic_le_generated i))
    ⁅(simpleRoot Q split i).comap f,
      (rootAt Q split i (Q.simple j*Q.simple i)).comap f⁆ =
      (rootAt Q split j (Q.simple i)).comap f ∨
    ⁅omegaOneAmbient ((simpleRoot Q split i).comap f),
      (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)).comap f⁆ ≠ ⊥ := by
  dsimp only
  have hf : Q.q.comp (Subgroup.inclusion (parabolic_le_generated i)) =
      MarkedLocal.endpointMap Q (originalMarkedIso Q) i := by
    ext g
    fin_cases i
    · exact (originalMarkedIso_left_apply Q g).symm
    · exact (originalMarkedIso_right_apply Q g).symm
  rw [hf]
  exact original_source_binary_near_eq_or_omega_perpendicular_nonzero Q (originalMarkedIso Q) split i j
    h hm hij n hn ν T hC μ hB hsize

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
