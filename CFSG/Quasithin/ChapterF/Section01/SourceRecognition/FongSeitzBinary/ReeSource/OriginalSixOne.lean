module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.PositiveRadicalBounds
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalBinaryCentralizers

/-!
# Source (6.1) at the actual original endpoints, for every Suzuki parameter

The naturally marked linear panel supplies source (6.3), and the Suzuki
marking identifies the actual rank-one actor and its simple root. Combining
the binary and positive-parameter fixed-index arguments proves both (6.1)
centralizer bounds on the whole radical. The literal endpoint equivalence
transports them to O₂ of the original parabolic; HypothesisF11 supplies its
self-centralization. The final theorem uses exactly the original quotient
homomorphism Q.q, with the entire original endpoint retained.

The common-field specialization gives the printed q⁴ and q⁶ bounds. It uses
the existing equality of field degrees conditional on odd linear degree;
it does not establish the rank-one family selection or that oddness.
The nonzero mixed-commutator cases on p.53, the remaining (6H) clauses,
compatible Section 10 coordinates and relations, and full-model comparison
remain separate obligations of this source construction.

Source: Fong--Seitz I (1973), proof of (6H), printed p.52, equation (6.1).
All Suzuki parameters m ≥ 0 are retained, including the full binary row.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal
variable {G X F : Type*} [Group G] [Group X] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (split : SplitData Q.tits) (i j : Fin 2)
  (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL(2,F))
  (T : Sylow 2 PSL(2,F))
  (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set PSL(2,F)))
  (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

include ν hC μ hB in
/-- Both whole-radical estimates (6.1) from the actual panel markings, for every m ≥ 0. -/
theorem source_six_one
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (hij : i ≠ j) (hsize : Nat.card F ≤ 2^(2*m+1)) :
    Nat.card (simpleRemainder Q split i ⊓ centralizer (simpleRoot Q split i : Set (X ⧸ Q.D)) :
        Subgroup (X ⧸ Q.D)) ≤ (Nat.card F)^4 ∧
    Nat.card (simpleRemainder Q split i ⊓
      centralizer (omegaOneAmbient (simpleRoot Q split i) : Set (X ⧸ Q.D)) :
        Subgroup (X ⧸ Q.D)) ≤ (2^(2*m+1))^2*(Nat.card F)^4 := by
  have hcard : Nat.card (simpleRoot Q split j) = Nat.card F := by
    rw [Nat.card_congr (linearRootEquiv Q split j ν T hC).toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F)]
  let hVi := marked_suzuki_remainder_le_kernel Q split i m μ hB
  have hcomm := (source_six_three Q split i j m μ hB ν T hC hm hij).2
  by_cases hm0 : m=0
  · subst m
    have hh := binary_source_six_one Q split i hVi μ hB hc hm j hij hcomm
    simpa only [hcard,Nat.mul_zero,Nat.zero_add,Nat.reducePow] using hh
  · have hh := positive_source_six_one Q split i hVi m μ hB hc hm j hij
      (by omega) hcomm (hcard ▸ hsize)
    simpa only [hcard] using hh

variable
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)

private theorem endpoint_root_image :
    ((simpleRoot Q split i).comap (endpointMap Q e i)).map (endpointMap Q e i) = simpleRoot Q split i := by
  have hr : (endpointMap Q e i).range = Endpoint Q i := by
    rw [endpointMap,MonoidHom.range_comp,MonoidHom.range_eq_top.mpr (endpoint Q e i).surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  rw [map_comap_eq,hr]
  exact inf_eq_right.mpr ((simpleRoot_le Q split i).trans
    (split.U_le.trans (Q.tits.B_le_standardParabolic _)))

include e ν hC μ hB in
/-- The actual original two-core satisfies (6.1), including Sz(2).
Self-centralization is supplied by the original F.1.1 hypothesis. -/
theorem original_source_six_one
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : Nat.card F ≤ 2^(2*m+1)) :
    Nat.card (pCore 2 (parabolic L S i) ⊓
      centralizer ((simpleRoot Q split i).comap (endpointMap Q e i) : Set (parabolic L S i)) :
        Subgroup (parabolic L S i)) ≤ (Nat.card F)^4 ∧
    Nat.card (pCore 2 (parabolic L S i) ⊓
      centralizer (omegaOneAmbient ((simpleRoot Q split i).comap (endpointMap Q e i)) :
        Set (parabolic L S i)) : Subgroup (parabolic L S i)) ≤ (2^(2*m+1))^2*(Nat.card F)^4 := by
  let hVi := marked_suzuki_remainder_le_kernel Q split i m μ hB
  have hh := source_six_one Q split i j ν T hC m μ hB
    (parabolic_core_selfCentralizing Q e h i) hm hij hsize
  have hr : endpointMap Q e i '' ((simpleRoot Q split i).comap (endpointMap Q e i) :
      Set (parabolic L S i)) = (simpleRoot Q split i : Set (X ⧸ Q.D)) :=
    congrArg (fun A : Subgroup (X ⧸ Q.D) => (A : Set (X ⧸ Q.D)))
      (endpoint_root_image Q split i e)
  have ho : endpointMap Q e i '' (omegaOneAmbient ((simpleRoot Q split i).comap (endpointMap Q e i)) :
      Set (parabolic L S i)) = (omegaOneAmbient (simpleRoot Q split i) : Set (X ⧸ Q.D)) := by
    have he := map_omegaOneAmbient_injective (endpointMap Q e i)
      ((Endpoint Q i).subtype_injective.comp (endpoint Q e i).injective)
      ((simpleRoot Q split i).comap (endpointMap Q e i))
    rw [endpoint_root_image] at he
    exact congrArg (fun A : Subgroup (X ⧸ Q.D) => (A : Set (X ⧸ Q.D))) he
  rw [Nat.card_congr (originalCoreCentralizerEquiv Q e split i hVi
      ((simpleRoot Q split i).comap (endpointMap Q e i) : Set (parabolic L S i))).toEquiv,hr,
    Nat.card_congr (originalCoreCentralizerEquiv Q e split i hVi
      (omegaOneAmbient ((simpleRoot Q split i).comap (endpointMap Q e i)) :
        Set (parabolic L S i))).toEquiv,ho]
  exact hh

omit F [Field F] [Finite F] [CharP F 2] i j ν T hC m μ hB in
/-- The printed q⁴ and q⁶ bounds, using the preceding conditional common-field theorem.
The odd linear degree and natural panel markings remain explicit. -/
theorem original_source_six_one_of_odd_degree
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (n : ℕ) (hn : Odd n) (m : ℕ)
    (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
    (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
    (hB : (quotientBorel Q 1).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (hcore : Q.tits.B.normalCore = ⊥) :
    Nat.card (pCore 2 (parabolic L S 1) ⊓
      centralizer ((simpleRoot Q split 1).comap (endpointMap Q e 1) : Set (parabolic L S 1)) :
        Subgroup (parabolic L S 1)) ≤ (2^(2*m+1))^4 ∧
    Nat.card (pCore 2 (parabolic L S 1) ⊓
      centralizer (omegaOneAmbient ((simpleRoot Q split 1).comap (endpointMap Q e 1)) :
        Set (parabolic L S 1)) : Subgroup (parabolic L S 1)) ≤ (2^(2*m+1))^6 := by
  let : NeZero n := ⟨hn.pos.ne'⟩
  have he := ree_common_field_exponent Q split hm n hn m ν T hC μ hB
    (UnitarySource.actorReflection Q split) hcore
  have hcard : Nat.card (BinaryGaloisField n) = 2^(2*m+1) := by
    rw [GaloisField.card 2 n hn.pos.ne',he]
  have hh := original_source_six_one Q split 1 0 ν T hC m μ hB e h hm (by decide) hcard.le
  rw [hcard,←pow_add] at hh
  exact hh

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {G F : Type*} [Group G] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits) (i j : Fin 2)
  (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL(2,F))
  (T : Sylow 2 PSL(2,F))
  (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set PSL(2,F)))
  (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

include ν hC μ hB in
/-- Source (6.1) for the root pulled back through the literal original quotient map Q.q. -/
theorem original_source_six_one_quotient
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : Nat.card F ≤ 2^(2*m+1)) :
    let f : parabolic L S i →* (generated L S) ⧸ Q.D :=
      Q.q.comp (Subgroup.inclusion (parabolic_le_generated i))
    Nat.card (pCore 2 (parabolic L S i) ⊓
      centralizer ((simpleRoot Q split i).comap f : Set (parabolic L S i)) :
        Subgroup (parabolic L S i)) ≤ (Nat.card F)^4 ∧
    Nat.card (pCore 2 (parabolic L S i) ⊓
      centralizer (omegaOneAmbient ((simpleRoot Q split i).comap f) :
        Set (parabolic L S i)) : Subgroup (parabolic L S i)) ≤ (2^(2*m+1))^2*(Nat.card F)^4 := by
  dsimp only
  have hf : Q.q.comp (Subgroup.inclusion (parabolic_le_generated i)) =
      MarkedLocal.endpointMap Q (originalMarkedIso Q) i := by
    ext g
    fin_cases i
    · exact (originalMarkedIso_left_apply Q g).symm
    · exact (originalMarkedIso_right_apply Q g).symm
  rw [hf]
  exact original_source_six_one Q split i j ν T hC m μ hB (originalMarkedIso Q) h hm hij hsize

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
