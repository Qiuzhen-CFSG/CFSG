module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.TensorRootApplication
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.TensorSecondReflection

/-!
# The original U₄ tensor coordinates normalized to both endpoint reflections

All four coordinate maps first have their actual source root ranges. The
full Cartan supplies every common scalar on A and C inside the smaller
actor's centralizing kernel. Its reflection therefore exchanges A and C
up to one scalar. The trace commutator forces that scalar into the fixed
field. Rescaling the same Hermitian intertwiner by that unit gives the
literal equations tA(a)t=C(a) and tC(a)t=A(a), preserving the entire large
actor action. The smaller actor also fixes D pointwise.

The second theorem applies these normalized maps to the literal Q.q-image
of S, U and the whole original quotient. It retains the full source Cartan,
Borel and both endpoint placements. Both orientations, q=2 and q=4, and
nonperfect original endpoints are included. No field-compatibility,
reflection equation, tensor-realization or root-alignment callback is input.

The original actor maps, radical/index profile and remainder containments
remain the earlier-source inputs of QuadraticLinearActors, supplied by
qt-dgs85-quadrangle-structure and selected by
qt-dgs85-split-quotient-recognition. The labelled second Cartan action and
smaller rank-one Bruhat equation, FourData assembly, and full U₅ family
remain with this source owner; these theorems do not assert recognition.
Source: Fong--Seitz I (6A)(b), pp.37--38; II (8B), pp.201--202,
with the common scalar comparison and trace equation (8.9).
Consumer: UnitaryPresentation.SourceCollection.four_originalS_collected
and the literal equation scheme of QuotientData.FourData.
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
/-- Normalize the same tensor intertwiner to the actual second reflection,
using the common source Cartan and the trace commutator. -/
theorem original_quadratic_tensor_reflection_realization :
    let μ := markedLinearLocalMarking Q (originalMarkedIso Q) h split i hVi fi hfi hki
    ∃ (f : F ≃+* Field n)
      (e : Multiplicative (Space n) ≃* simpleRemainder Q split i),
      let l := fieldRelabelledActor Q split i hVi μ si n f
      let v := tensorEmbedding Q split (conjugation n) (conjugation_involutive n) i e
      let r := FourTensor.roots (Field n) (conjugation n) (conjugation_involutive n) l v
      (∀ (g : SL(2,Field n)) (p : Space n), l g * (e (.ofAdd p) : (generated L S) ⧸ Q.D) *
        (l g)⁻¹ = e (.ofAdd (action n g p))) ∧
      (∀ a : Field n, (sj.val : (generated L S) ⧸ Q.D) * r.A (.ofAdd a) * sj.val = r.C (.ofAdd a)) ∧
      (∀ a : Field n, (sj.val : (generated L S) ⧸ Q.D) * r.C (.ofAdd a) * sj.val = r.A (.ofAdd a)) := by
  dsimp only
  let μ := markedLinearLocalMarking Q (originalMarkedIso Q) h split i hVi fi hfi hki
  obtain ⟨f,e,he,hA,hBroot,hC,hD,hfix⟩ := marked_quadratic_tensor_roots Q (originalMarkedIso Q) h split
    hm i j hij hVi hVj si sj fi fj hfi hfj hki hkj hfields hindexi hindexj helem hQi hQj hne n hk
  have hF : Nat.card F = (2^n)^2 := by rw [hfields,hk]
  obtain ⟨_,_,hcard,_⟩ := marked_four_actor_cartan_cards Q (originalMarkedIso Q) h split
    hm j i hij.symm hVj hVi fj fi hfj hfi hkj hki n (NeZero.pos n) hk hF helem
  let hc := MarkedLocal.parabolic_core_selfCentralizing Q (originalMarkedIso Q) h i
  let l := fieldRelabelledActor Q split i hVi μ si n f
  let v := tensorEmbedding Q split (conjugation n) (conjugation_involutive n) i e
  let r := FourTensor.roots (Field n) (conjugation n) (conjugation_involutive n) l v
  let torus := tensorCartan Q split i hVi μ si n f e he hc hcard
  let scalar := tensorScalar Q split i hVi μ si n f e he hc hcard
  have hcl := tensorScalar_commute Q split i hVi μ si n f e he hc hcard
  have hscalar := tensorScalar_conjugation Q split i hVi μ si n f e he hc hcard
  have htorus := tensorCartan_range Q split i hVi μ si n f e he hc hcard
  have hl : Function.Injective l :=
    (GTwoSource.alignedPinningHom_injective Q split i hVi μ si).comp (Atlas.fieldEquivSL 2 f.symm).injective
  have hAi : Function.Injective r.A := hl.comp (SpecialLinearGroup.upperUnipotentHom_injective (Field n))
  let μj := markedLinearLocalMarking Q (originalMarkedIso Q) h split j hVj fj hfj hkj
  have ht2 : (sj.val : (generated L S) ⧸ Q.D) * sj.val = 1 := by
    rw [←GTwoSource.alignedPinningHom_weyl Q split j hVj μj sj,←map_mul,weyl_sq,map_one]
  obtain ⟨c,hc0,hAC,hCA⟩ := secondReflection_AC_fixedScalar Q split i j (conjugation n) (conjugation_involutive n)
    r torus hBroot htorus.le
    (FourCartan.hom_B (Field n) (conjugation n) (conjugation_involutive n) l scalar hcl v he hscalar)
    hA hC hAi
    (FourCartan.hom_A (Field n) (conjugation n) (conjugation_involutive n) l scalar hcl v)
    (FourCartan.hom_C (Field n) (conjugation n) (conjugation_involutive n) l scalar hcl v he hscalar)
    sj (FourTensor.relations (Field n) (conjugation n) (conjugation_involutive n) l v he)
    (tensor_D_injective Q split n i l e) ht2
  let cfixed : fixedField n := c
  let cunit : (fixedField n)ˣ := Units.mk0 cfixed hc0
  let e' := (FourTensor.scale (Field n) (conjugation n) (conjugation_involutive n) cunit).trans e
  have he' (g : SL(2,Field n)) (p : Space n) :
      l g * (e' (.ofAdd p) : (generated L S) ⧸ Q.D) * (l g)⁻¹ = e' (.ofAdd (action n g p)) := by
    change l g * (e (.ofAdd (cfixed • p)) : (generated L S) ⧸ Q.D) * (l g)⁻¹ = e (.ofAdd (cfixed • action n g p))
    rw [he,map_smul]
  have hscaled (a : Field n) :
      (e' (.ofAdd (FourTensor.offDiagonal (Field n) (conjugation n) (conjugation_involutive n) a)) : (generated L S) ⧸ Q.D) =
        r.C (.ofAdd ((c : Field n)*a)) := by
    exact congrArg (fun p : FourTensor.Core (Field n) (conjugation n) (conjugation_involutive n) =>
      (e (.ofAdd p) : (generated L S) ⧸ Q.D))
      (FourTensor.scale_off (Field n) (conjugation n) (conjugation_involutive n) cunit a)
  have htinv : (sj.val : (generated L S) ⧸ Q.D)⁻¹ = sj.val := inv_eq_of_mul_eq_one_right ht2
  refine ⟨f,e',he',?_,?_⟩
  · intro a
    change (sj.val : (generated L S) ⧸ Q.D) * r.A (.ofAdd a) * sj.val = _
    exact (htinv ▸ hAC a).trans (hscaled a).symm
  · intro a
    change (sj.val : (generated L S) ⧸ Q.D) * (e' (.ofAdd (FourTensor.offDiagonal (Field n) (conjugation n) (conjugation_involutive n) a)) : (generated L S) ⧸ Q.D) * sj.val = r.A (.ofAdd a)
    rw [hscaled]
    have hcE : (c : Field n) ≠ 0 := fun hh => hc0 (Subtype.ext hh)
    simpa only [htinv,←mul_assoc,inv_mul_cancel₀ hcE,one_mul] using hCA ((c : Field n)*a)

include hVj sj fj hfj hkj hfields hindexi hindexj helem hQi hQj hne hk hm hij in
/-- Literal original-S collection, all actual root ranges and all three second-reflection root laws,
with the full Cartan and both endpoint placements on this same quotient. -/
theorem original_quadratic_tensor_reflection_collected :
    let μ := markedLinearLocalMarking Q (originalMarkedIso Q) h split i hVi fi hfi hki
    ∃ (f : F ≃+* Field n)
      (e : Multiplicative (Space n) ≃* simpleRemainder Q split i)
      (t : FourWeyl.torusParameters (Field n) (conjugation n) →* (generated L S) ⧸ Q.D),
      let l := fieldRelabelledActor Q split i hVi μ si n f
      let v := tensorEmbedding Q split (conjugation n) (conjugation_involutive n) i e
      let r := FourTensor.roots (Field n) (conjugation n) (conjugation_involutive n) l v
      FourPositive.Relations (Field n) (conjugation n) (conjugation_involutive n) r ∧
      r.generated = split.U ∧ r.TorusLaws t ∧ t.range = Q.tits.B ⊓ Q.tits.N ∧
      r.A.range = simpleRoot Q split i ∧ r.B.range = simpleRoot Q split j ∧
      r.C.range = rootAt Q split i (Q.simple j) ∧ r.D.range = rootAt Q split j (Q.simple i) ∧
      rankOne Q split j ≤ centralizer (r.D.range : Set ((generated L S) ⧸ Q.D)) ∧
      (∀ a : Field n, (sj.val : (generated L S) ⧸ Q.D) * r.A (.ofAdd a) * sj.val = r.C (.ofAdd a)) ∧
      (∀ a : Field n, (sj.val : (generated L S) ⧸ Q.D) * r.C (.ofAdd a) * sj.val = r.A (.ofAdd a)) ∧
      (∀ d : fixedField n, (sj.val : (generated L S) ⧸ Q.D) * r.D (.ofAdd d) *
        (sj.val : (generated L S) ⧸ Q.D)⁻¹ = r.D (.ofAdd d)) ∧
      r.borel t = Q.tits.B ∧
      r.borel t ⊔ closure {(si.val : (generated L S) ⧸ Q.D)} =
        Q.tits.standardParabolic {Q.simple i} ∧
      r.borel t ⊔ closure {(sj.val : (generated L S) ⧸ Q.D)} =
        Q.tits.standardParabolic {Q.simple j} ∧
      (∀ x ∈ (S.subgroupOf (generated L S)).map Q.q, ∃ a d c b, x = r.word a d c b) ∧
      ∀ (w : Fin 2 → Q.tits.N)
        (_hw : ∀ a, QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) (w a) = Q.simple a),
        r.generated ⊔ closure (Set.range (fun a => (w a : (generated L S) ⧸ Q.D))) = ⊤ := by
  dsimp only
  let μ := markedLinearLocalMarking Q (originalMarkedIso Q) h split i hVi fi hfi hki
  obtain ⟨f,e,he,htA,htC⟩ := original_quadratic_tensor_reflection_realization Q h split
    hm i j hij hVi hVj si sj fi fj hfi hfj hki hkj hfields hindexi hindexj helem hQi hQj hne n hk
  obtain ⟨_,_,_,hri,hrj,_⟩ := QuadrangleStructure.marked_quadratic_linear_sixA Q (originalMarkedIso Q) h split
    hm i j hij hVi hVj si sj fi fj hfi hfj hki hkj hfields hindexi hindexj helem hQi hQj hne
  have hsmall : Nat.card (simpleRoot Q split j) = 2^n := hrj.trans hk
  have hlarge : Nat.card (simpleRoot Q split i) = Nat.card (Field n) :=
    (hri.trans hfields.symm).trans (Nat.card_congr f.toEquiv)
  have hA := fieldRelabelledActor_root_range Q split i hVi μ si n f
  have hs := fieldRelabelledActor_weyl Q split i hVi μ si n f
  have hBroot := tensor_B_range Q split n i j hij hm hVi hVj si _ e he hA hs hsmall
  have hC := tensor_C_range Q split n i j hij hm hVi hVj si _ e he hA hs hsmall hlarge
  have hD := tensor_D_range Q split n i j hij hm hVi hVj _ e he hA hsmall
  have hfix := tensor_smallActor_centralizes_D Q split n i j hij hm hVi hVj si _ e he hA hs hsmall
  have hF : Nat.card F = (2^n)^2 := by rw [hfields,hk]
  obtain ⟨_,_,hcard,_⟩ := marked_four_actor_cartan_cards Q (originalMarkedIso Q) h split
    hm j i hij.symm hVj hVi fj fi hfj hfi hkj hki n (NeZero.pos n) hk hF helem
  let hc := MarkedLocal.parabolic_core_selfCentralizing Q (originalMarkedIso Q) h i
  let l := fieldRelabelledActor Q split i hVi μ si n f
  let v := tensorEmbedding Q split (conjugation n) (conjugation_involutive n) i e
  let r := FourTensor.roots (Field n) (conjugation n) (conjugation_involutive n) l v
  let t := tensorCartan Q split i hVi μ si n f e he hc hcard
  have hV := tensorEmbedding_range Q split (conjugation n) (conjugation_involutive n) i e
  have hgen : r.generated = split.U :=
    four_generated_eq_unipotent Q split (conjugation n) (conjugation_involutive n) l v i hA hV
  have ht : t.range = Q.tits.B ⊓ Q.tits.N :=
    tensorCartan_range Q split i hVi μ si n f e he hc hcard
  have hB : r.borel t = Q.tits.B := by
    change r.generated ⊔ t.range = _
    rw [hgen,ht]
    exact split.factorization
  refine ⟨f,e,t,FourTensor.relations (Field n) (conjugation n) (conjugation_involutive n) l v he,
    hgen,tensorCartan_torusLaws Q split i hVi μ si n f e he hc hcard,ht,
    hA,hBroot,hC,hD,hfix,htA,htC,?_,hB,?_,?_,?_,?_⟩
  · intro d
    have heq := mem_centralizer_iff.mp (hfix sj.mem_rankOne) (r.D (.ofAdd d)) ⟨.ofAdd d,rfl⟩
    rw [←heq,mul_inv_cancel_right]
  · rw [hB]
    exact (MarkedWeyl.Lifts.simple_parabolic Q i si.val si.class_eq).symm
  · rw [hB]
    exact (MarkedWeyl.Lifts.simple_parabolic Q j sj.val sj.class_eq).symm
  · exact four_originalS_collected_of_realization Q split (conjugation n)
      (conjugation_involutive n) l h i e hA he
  · intro w hw
    exact four_tensor_and_lifts_generate Q split w hw (conjugation n)
      (conjugation_involutive n) l v h i hA hV


end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
