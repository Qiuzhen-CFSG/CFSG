module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.TensorCartanApplication
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.TensorRoots

/-!
# Original U₄ tensor coordinates with all actual source root ranges

The original quadratic profile constructs a Hermitian intertwiner, and the
structural root orders identify all four tensor summands with the actual
simple and crossed roots. The whole smaller root actor therefore fixes
the labelled D root. This proves the second-reflection D equation on the
same quotient, rather than assuming it as coordinate compatibility.

The original application retains the full scalar torus, positive relations,
U-generation, literal Q.q-image of S, whole-quotient generation and full
Borel and both endpoint placements. The marked construction also applies
to the geometric quotient. All fields, both orientations and q=2 survive.
TensorReflectionApplication normalizes the labelled A/C exchange on these
same roots. The second torus and rank-one laws, FourData assembly and the
entire U₅ reconstruction remain with this task.

Earlier inputs are the literal original actor quotient maps, radical and
index profile, and remainder containments of QuadraticLinearActors,
produced by qt-dgs85-quadrangle-structure and selected by
qt-dgs85-split-quotient-recognition. Neither a root-alignment equation nor
a tensor-module premise is assumed here.
Source: Fong--Seitz I (6A)(b), pp.37--38; II (8B), pp.201--202.
Consumer: UnitaryPresentation.SourceCollection.four_originalS_collected,
and the root placements and second D law required by QuotientData.FourData.
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

variable {G X F k : Type*} [Group G] [Group X]
  [Field F] [Finite F] [CharP F 2] [Field k] [Finite k] [CharP k 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (mark : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
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
/-- The constructed tensor coordinates label all four actual Weyl roots. -/
theorem marked_quadratic_tensor_roots :
    let μ := markedLinearLocalMarking Q mark h split i hVi fi hfi hki
    ∃ (f : F ≃+* Field n)
      (e : Multiplicative (Space n) ≃* simpleRemainder Q split i),
      let l := fieldRelabelledActor Q split i hVi μ si n f
      let v := (simpleRemainder Q split i).subtype.comp e.toMonoidHom
      let r := FourTensor.roots (Field n) (conjugation n) (conjugation_involutive n) l v
      (∀ (g : SL(2,Field n)) (p : Space n),
        l g * (e (.ofAdd p) : X ⧸ Q.D) * (l g)⁻¹ = e (.ofAdd (action n g p))) ∧
      r.A.range = simpleRoot Q split i ∧
      r.B.range = simpleRoot Q split j ∧
      r.C.range = rootAt Q split i (Q.simple j) ∧
      r.D.range = rootAt Q split j (Q.simple i) ∧
      rankOne Q split j ≤ centralizer (r.D.range : Set (X ⧸ Q.D)) := by
  dsimp only
  obtain ⟨f,e,he⟩ := marked_quadratic_tensor_realization Q mark h split
    hm i j hij hVi hVj si sj fi fj hfi hfj hki hkj hfields hindexi hindexj helem hQi hQj hne n hk
  obtain ⟨_,_,_,hri,hrj,_⟩ := QuadrangleStructure.marked_quadratic_linear_sixA Q mark h split
    hm i j hij hVi hVj si sj fi fj hfi hfj hki hkj hfields hindexi hindexj helem hQi hQj hne
  have hA := fieldRelabelledActor_root_range Q split i hVi
    (markedLinearLocalMarking Q mark h split i hVi fi hfi hki) si n f
  have hs := fieldRelabelledActor_weyl Q split i hVi
    (markedLinearLocalMarking Q mark h split i hVi fi hfi hki) si n f
  have hsmall : Nat.card (simpleRoot Q split j) = 2^n := hrj.trans hk
  have hlarge : Nat.card (simpleRoot Q split i) = Nat.card (Field n) :=
    (hri.trans hfields.symm).trans (Nat.card_congr f.toEquiv)
  exact ⟨f,e,he,hA,
    tensor_B_range Q split n i j hij hm hVi hVj si _ e he hA hs hsmall,
    tensor_C_range Q split n i j hij hm hVi hVj si _ e he hA hs hsmall hlarge,
    tensor_D_range Q split n i j hij hm hVi hVj _ e he hA hsmall,
    tensor_smallActor_centralizes_D Q split n i j hij hm hVi hVj si _ e he hA hs hsmall⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource

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
/-- Literal original-S collection, all actual root ranges and the second D law,
with the full Cartan and both endpoint placements on this same quotient. -/
theorem original_quadratic_tensor_root_collected :
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
  obtain ⟨f,e,he,hA,hBroot,hC,hD,hfix⟩ := marked_quadratic_tensor_roots Q (originalMarkedIso Q) h split
    hm i j hij hVi hVj si sj fi fj hfi hfj hki hkj hfields hindexi hindexj helem hQi hQj hne n hk
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
    hA,hBroot,hC,hD,hfix,?_,hB,?_,?_,?_,?_⟩
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
