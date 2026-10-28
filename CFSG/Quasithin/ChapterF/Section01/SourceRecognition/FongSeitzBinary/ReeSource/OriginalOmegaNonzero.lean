module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OmegaNonzero

/-!
# Original endpoint applications of the Omega commutator steps

The actual endpoint equivalence transports the full nonzero (6.4)
commutator equality and the all-parameter near-commutator reduction.
Injectivity identifies each transported Omega with Omega of the original
pulled-back root. The shifted linear root is placed in the whole endpoint
by its actual octagon word length. Hypothesis F.1.1 supplies the original
two-core self-centralization needed by the source estimates.

Both applications specialize to Q.q composed with the original parabolic
inclusion. The index is arbitrary, preserving both orientations, and the
ambient original group need not be finite. Independent panel markings and
the actual size comparisons remain explicit. Omega movement must still be
excluded to prove unconditional (6H)(b); the nonzero premise in (6.4) is
also retained. No rank-one pairing, odd-degree or Section 10 conclusion is
claimed here.

Source: Fong--Seitz I (1973), proof of (6H)(b), printed p.53.
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

/-- The all-parameter original endpoint reduction retains the literal Omega commutator. -/
theorem original_source_near_eq_or_omega_perpendicular_nonzero
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
    ⁅omegaOneAmbient ((simpleRoot Q split i).comap (endpointMap Q e i)),
      (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)).comap (endpointMap Q e i)⁆ ≠ ⊥ := by
  have hi := (Endpoint Q i).subtype_injective.comp (endpoint Q e i).injective
  have he := endpoint_root_images Q e split i j hm hij
  rcases source_near_eq_or_omega_perpendicular_nonzero Q split i j m μ hB n hn ν T hC
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

private theorem fourth_root_le_endpoint (hm : rotationOrder Q = 8) (hij : i ≠ j) :
    rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) ≤ Endpoint Q i := by
  apply le_trans ?_ (split.U_le.trans (Q.tits.B_le_standardParabolic _))
  rw [←unipotentConjugate_one split]
  apply rootAt_le_conjugate
  have hs (k : Fin 2) : (Q.simple k)⁻¹ = Q.simple k := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem k)).2)
  simp only [one_mul,mul_inv_rev,hs,←mul_assoc]
  have hh (b : Bool) := And.intro
    (wordLength_alternatingWord Q b (n := 3) (by omega))
    (wordLength_alternatingWord Q b (n := 4) (by omega))
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · have ht := hh false
    simp only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,
      Bool.not_true,mul_one,←mul_assoc] at ht
    rw [ht.1,ht.2]
  · have ht := hh true
    simp only [alternatingWord,Bool.false_eq_true,↓reduceIte,Bool.not_false,
      Bool.not_true,mul_one,←mul_assoc] at ht
    rw [ht.1,ht.2]
  · exact (hij rfl).elim

/-- A nonzero original (6.4) commutator is the entire original shifted Omega subgroup. -/
theorem original_source_six_four_eq_of_nonzero
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (n : ℕ) (hn : 0 < n) (m : ℕ)
    (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set _))
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
    (hB : (quotientBorel Q i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (hsize : (Nat.card (BinaryGaloisField n))^4 < (2^(2*m+1))^6)
    (hne : ⁅(simpleRoot Q split i).comap (endpointMap Q e i),
      (rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)).comap (endpointMap Q e i)⁆ ≠ ⊥) :
    ⁅(simpleRoot Q split i).comap (endpointMap Q e i),
      (rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)).comap (endpointMap Q e i)⁆ =
      omegaOneAmbient ((rootAt Q split i (Q.simple j*Q.simple i)).comap (endpointMap Q e i)) := by
  have hi := (Endpoint Q i).subtype_injective.comp (endpoint Q e i).injective
  have he := endpoint_root_images Q e split i j hm hij
  have hd := endpoint_subgroup_image Q e i _ (fourth_root_le_endpoint Q split i j hm hij)
  have hnz : ⁅simpleRoot Q split i,rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)⁆ ≠ ⊥ := by
    intro hz
    apply hne
    apply map_injective (f := endpointMap Q e i) hi
    rw [map_commutator,he.1,hd,Subgroup.map_bot,hz]
  apply map_injective (f := endpointMap Q e i) hi
  rw [map_commutator,he.1,hd,map_omegaOneAmbient_injective _ hi,he.2.1]
  exact source_six_four_eq_of_nonzero Q split i j m μ hB n hn ν T hC
    (parabolic_core_selfCentralizing Q e h i) hm hij hsize hnz

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits) (i j : Fin 2)

/-- The all-parameter reduction uses the literal Q.q and Omega of its actual pulled-back root. -/
theorem original_source_omega_near_reduction_quotient
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
  exact original_source_near_eq_or_omega_perpendicular_nonzero Q (originalMarkedIso Q) split i j
    h hm hij n hn m ν T hC μ hB hsize

/-- The entire nonzero-commutator equality is transported by the literal original quotient. -/
theorem original_source_six_four_eq_quotient
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (n : ℕ) (hn : 0 < n) (m : ℕ)
    (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set _))
    (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
    (hB : (quotientBorel Q i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (hsize : (Nat.card (BinaryGaloisField n))^4 < (2^(2*m+1))^6) :
    let f : parabolic L S i →* (generated L S) ⧸ Q.D :=
      Q.q.comp (Subgroup.inclusion (parabolic_le_generated i))
    ⁅(simpleRoot Q split i).comap f,
      (rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)).comap f⁆ ≠ ⊥ →
    ⁅(simpleRoot Q split i).comap f,
      (rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)).comap f⁆ =
      omegaOneAmbient ((rootAt Q split i (Q.simple j*Q.simple i)).comap f) := by
  dsimp only
  have hf : Q.q.comp (Subgroup.inclusion (parabolic_le_generated i)) =
      MarkedLocal.endpointMap Q (originalMarkedIso Q) i := by
    ext g
    fin_cases i
    · exact (originalMarkedIso_left_apply Q g).symm
    · exact (originalMarkedIso_right_apply Q g).symm
  rw [hf]
  exact original_source_six_four_eq_of_nonzero Q (originalMarkedIso Q) split i j
    h hm hij n hn m ν T hC μ hB hsize

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
