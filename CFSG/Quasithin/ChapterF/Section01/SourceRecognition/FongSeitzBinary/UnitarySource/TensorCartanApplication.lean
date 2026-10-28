module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.TensorApplication
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.TensorCartan

/-!
# Original U₄ coordinates with the full scalar torus

The actual Hermitian intertwiner supplied by TensorApplication determines
how the source Cartan kernel acts on those same coordinates. TensorCartan
identifies these operators with all nonzero fixed-field scalars; the exact
kernel order is proved here from the original actor quotient maps. Hence
the entire source torus is constructed, with the four exact field weights,
without a scalar compatibility or tensor realization premise.

The same maps satisfy the positive relations, collect the literal Q.q-image
of S, generate U and, with the marked Weyl lifts, the whole quotient. Their
torus is the full B ∩ N, so they give the full Borel and both oriented
endpoint placements. The actual large-actor reflection satisfies the B/D
exchange, conjugation on C, Cartan swap and A-root Bruhat equation. Both
orientations and q=2 are retained; neither endpoint is assumed perfect.

The original quotient maps, radical clauses and remainder containments
remain the earlier-source inputs of QuadraticLinearActors, whose structural
producer is qt-dgs85-quadrangle-structure; row selection belongs to
qt-dgs85-split-quotient-recognition. This is a constructed increment toward
FourData, not full unitary recognition. Aligning the smaller source root,
the second-reflection equations and the entire U₅ coordinate reconstruction
remain with this source owner. The arbitrary Hermitian intertwiner does not
by itself identify the B coordinate with that smaller simple root.

Source: Fong--Seitz I (6A)(b), pp.37--38; II (8B), pp.201--202;
DGS (11.7), pp.174--175. Consumers: UnitaryPresentation.SourceCollection
and the partial equation scheme of UnitaryPresentation.QuotientData.FourData.
-/

@[expose] public noncomputable section
open Subgroup Representation Matrix Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
open Theory.PSL2.SemilinearCoverage
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
open Representation.OrthogonalFourMinus Representation.OrthogonalFourMinus.FiniteModel
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource

variable {G F k : Type*} [Group G]
  [Field F] [Finite F] [CharP F 2] [Field k] [Finite k] [CharP k 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (si : RootReflection Q split i) (sj : RootReflection Q split j)
  (fi : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,F))
  (fj : (S ⊔ L j).subgroupOf (parabolic L S j) →* SL(2,k))
  (hfi : Function.Surjective fi) (hfj : Function.Surjective fj)
  (hki : fi.ker = (pCore 2 (parabolic L S i)).subgroupOf ((S ⊔ L i).subgroupOf (parabolic L S i)))
  (hkj : fj.ker = (pCore 2 (parabolic L S j)).subgroupOf ((S ⊔ L j).subgroupOf (parabolic L S j)))
  (hfields : Nat.card F = Nat.card k ^ 2)
  (hindexi : (commonBorel L S).relIndex (parabolic L S i) = Nat.card F + 1)
  (hindexj : (commonBorel L S).relIndex (parabolic L S j) = Nat.card k + 1)
  (helem : IsElementaryAbelian 2 ((parabolic L S i).pCoreIn 2))
  (hQi : letI := QuadrangleStructure.original_core_normal_in_sylow (L := L) (S := S) i
    IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
  (hQj : letI := QuadrangleStructure.original_core_normal_in_sylow (L := L) (S := S) j
    IsElementaryAbelian 2 (S ⧸ ((parabolic L S j).pCoreIn 2).subgroupOf S))
  (hne : ⁅(parabolic L S j).pCoreIn 2,(parabolic L S j).pCoreIn 2⁆ ≠ ⊥)
  (n : ℕ) [NeZero n] (hk : Nat.card k = 2^n)

include hVj sj fj hfj hkj hfields hindexi hindexj helem hQi hQj hne hk hm hij in
/-- Construct the full torus and its exact weights on the same tensor coordinates,
from the original quadratic profile, with no scalar or intertwining premise. -/
theorem original_quadratic_tensor_cartan :
    let μ := markedLinearLocalMarking Q (originalMarkedIso Q) h split i hVi fi hfi hki
    ∃ (f : F ≃+* Field n)
      (e : Multiplicative (Space n) ≃* simpleRemainder Q split i)
      (t : FourWeyl.torusParameters (Field n) (conjugation n) →* (generated L S) ⧸ Q.D),
      let l := fieldRelabelledActor Q split i hVi μ si n f
      let v := tensorEmbedding Q split (conjugation n) (conjugation_involutive n) i e
      let r := FourTensor.roots (Field n) (conjugation n) (conjugation_involutive n) l v
      FourPositive.Relations (Field n) (conjugation n) (conjugation_involutive n) r ∧
      r.generated = split.U ∧ r.TorusLaws t ∧ t.range = Q.tits.B ⊓ Q.tits.N ∧
      (∀ p, (∀ a : Field n, t p * r.A (.ofAdd a) * (t p)⁻¹ =
        r.A (.ofAdd (((p.val.1 : Field n) / (p.val.2 : Field n)) * a))) ∧
        (∀ d : fixedField n, t p * r.D (.ofAdd d) * (t p)⁻¹ =
          r.D (.ofAdd (FourPositive.normParameter (Field n) (conjugation n)
            (conjugation_involutive n) p.val.1 d))) ∧
        (∀ c : Field n, t p * r.C (.ofAdd c) * (t p)⁻¹ =
          r.C (.ofAdd (((p.val.1 : Field n) * conjugation n (p.val.2 : Field n)) * c))) ∧
        (∀ b : fixedField n, t p * r.B (.ofAdd b) * (t p)⁻¹ =
          r.B (.ofAdd (FourPositive.normParameter (Field n) (conjugation n)
            (conjugation_involutive n) p.val.2 b)))) ∧
      r.borel t = Q.tits.B ∧
      r.borel t ⊔ closure {(si.val : (generated L S) ⧸ Q.D)} =
        Q.tits.standardParabolic {Q.simple i} ∧
      r.borel t ⊔ closure {(sj.val : (generated L S) ⧸ Q.D)} =
        Q.tits.standardParabolic {Q.simple j} ∧
      (∀ x ∈ (S.subgroupOf (generated L S)).map Q.q, ∃ a d c b, x = r.word a d c b) ∧
      (∀ b : fixedField n, (si.val : (generated L S) ⧸ Q.D) * r.B (.ofAdd b) * si.val =
        r.D (.ofAdd b)) ∧
      (∀ d : fixedField n, (si.val : (generated L S) ⧸ Q.D) * r.D (.ofAdd d) * si.val =
        r.B (.ofAdd d)) ∧
      (∀ c : Field n, (si.val : (generated L S) ⧸ Q.D) * r.C (.ofAdd c) * si.val =
        r.C (.ofAdd (conjugation n c))) ∧
      (∀ p, (si.val : (generated L S) ⧸ Q.D) * t p * si.val =
        t (FourCells.swapParameter (Field n) (conjugation n) p)) ∧
      (∀ (a : Field n) (ha : a ≠ 0),
        (si.val : (generated L S) ⧸ Q.D) * r.A (.ofAdd a) * si.val =
          r.A (.ofAdd a⁻¹) * t (FourBruhat.aTorus (Field n) (conjugation n) a ha) *
            si.val * r.A (.ofAdd a⁻¹)) ∧
      ∀ (w : Fin 2 → Q.tits.N)
        (_hw : ∀ a, QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) (w a) = Q.simple a),
        r.generated ⊔ closure (Set.range (fun a => (w a : (generated L S) ⧸ Q.D))) = ⊤ := by
  dsimp only
  let μ := markedLinearLocalMarking Q (originalMarkedIso Q) h split i hVi fi hfi hki
  obtain ⟨f,e,he⟩ := marked_quadratic_tensor_realization Q (originalMarkedIso Q) h split
    hm i j hij hVi hVj si sj fi fj hfi hfj hki hkj hfields hindexi hindexj helem hQi hQj hne n hk
  have hF : Nat.card F = (2^n)^2 := by rw [hfields,hk]
  obtain ⟨_,_,hcard,_⟩ := marked_four_actor_cartan_cards Q (originalMarkedIso Q) h split
    hm j i hij.symm hVj hVi fj fi hfj hfi hkj hki n (NeZero.pos n) hk hF helem
  let hc := MarkedLocal.parabolic_core_selfCentralizing Q (originalMarkedIso Q) h i
  let l := fieldRelabelledActor Q split i hVi μ si n f
  let v := tensorEmbedding Q split (conjugation n) (conjugation_involutive n) i e
  let r := FourTensor.roots (Field n) (conjugation n) (conjugation_involutive n) l v
  let t := tensorCartan Q split i hVi μ si n f e he hc hcard
  let c := tensorScalar Q split i hVi μ si n f e he hc hcard
  have hcl := tensorScalar_commute Q split i hVi μ si n f e he hc hcard
  have hA := fieldRelabelledActor_root_range Q split i hVi μ si n f
  have hV := tensorEmbedding_range Q split (conjugation n) (conjugation_involutive n) i e
  have hgen : r.generated = split.U :=
    four_generated_eq_unipotent Q split (conjugation n) (conjugation_involutive n) l v i hA hV
  have ht : t.range = Q.tits.B ⊓ Q.tits.N :=
    tensorCartan_range Q split i hVi μ si n f e he hc hcard
  have hB : r.borel t = Q.tits.B := by
    change r.generated ⊔ t.range = _
    rw [hgen,ht]
    exact split.factorization
  have hs : l (weyl (Field n)) = (si.val : (generated L S) ⧸ Q.D) :=
    fieldRelabelledActor_weyl Q split i hVi μ si n f
  refine ⟨f,e,t,FourTensor.relations (Field n) (conjugation n) (conjugation_involutive n) l v he,
    hgen,tensorCartan_torusLaws Q split i hVi μ si n f e he hc hcard,ht,?_,hB,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro p
    have hscalar := tensorScalar_conjugation Q split i hVi μ si n f e he hc hcard
    exact ⟨FourCartan.hom_A (Field n) (conjugation n) (conjugation_involutive n) l c hcl v p,
      FourCartan.hom_D (Field n) (conjugation n) (conjugation_involutive n) l c hcl v he hscalar p,
      FourCartan.hom_C (Field n) (conjugation n) (conjugation_involutive n) l c hcl v he hscalar p,
      FourCartan.hom_B (Field n) (conjugation n) (conjugation_involutive n) l c hcl v he hscalar p⟩
  · rw [hB]
    exact (MarkedWeyl.Lifts.simple_parabolic Q i si.val si.class_eq).symm
  · rw [hB]
    exact (MarkedWeyl.Lifts.simple_parabolic Q j sj.val sj.class_eq).symm
  · exact four_originalS_collected_of_realization Q split (conjugation n)
      (conjugation_involutive n) l h i e hA he
  · intro b
    rw [←hs]
    exact FourCartan.weyl_B (Field n) (conjugation n) (conjugation_involutive n) l v he b
  · intro d
    have hs2 : l (weyl (Field n)) * l (weyl (Field n)) = 1 := by
      rw [←map_mul,weyl_sq,map_one]
    have hb := FourCartan.weyl_B (Field n) (conjugation n) (conjugation_involutive n) l v he d
    rw [←hs,←hb]
    calc
      _ = (l (weyl (Field n)) * l (weyl (Field n))) * r.B (.ofAdd d) *
          (l (weyl (Field n)) * l (weyl (Field n))) := by simp only [r,mul_assoc]
      _ = _ := by rw [hs2,one_mul,mul_one]
  · intro a
    rw [←hs]
    exact FourCartan.weyl_C (Field n) (conjugation n) (conjugation_involutive n) l v he a
  · intro p
    rw [←hs]
    exact FourCartan.weyl_hom (Field n) (conjugation n) l c hcl p
  · intro a ha
    rw [←hs]
    exact FourCartan.weyl_A (Field n) (conjugation n) (conjugation_involutive n) l c hcl v a ha
  · intro w hw
    exact four_tensor_and_lifts_generate Q split w hw (conjugation n)
      (conjugation_involutive n) l v h i hA hV

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
