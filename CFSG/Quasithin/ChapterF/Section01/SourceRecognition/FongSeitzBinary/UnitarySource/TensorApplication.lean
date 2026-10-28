module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.TensorRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.ActorCartanApplication
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.TensorRealization
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.QuadraticLinearActors

/-!
# Constructed U₄ tensor coordinates on the original split quotient

The two original linear actor quotient maps, full Borel indices and
radical clauses feed the proved quadratic structural theorem. Its actual
commutator, elementary remainder and orders then force the Hermitian
module by TensorRecognition. TensorRealization relabels the entire same
root actor and constructs the equivariant coordinates on that remainder.
No tensor intertwiner, irreducibility, coefficient equation or mixed
polynomial law is an input of either theorem below.

For the original SourceQuotient, these constructed coordinates prove all
FourPositive.Relations, generation of U, the specified linear reflection,
collection of the literal Q.q-image of S, and whole-quotient generation
with any two marked Weyl lifts. The marked realization also permits the
geometric amalgam. Both endpoint orientations and n=1 (q=2) are retained;
perfectness of the smaller original endpoint is not assumed.

The exact earlier-source producer is
QuadraticLinearActors.marked_quadratic_linear_sixA, owned by
qt-dgs85-quadrangle-structure. Its original quotient/profile and remainder
hypotheses remain explicit here; original row selection remains with
qt-dgs85-split-quotient-recognition. This is not full unitary recognition:
matching the scalar-coordinate field and the smaller endpoint's actual
root labels, the remaining torus/Weyl equations and FourData assembly stay
with this unitary source task, as does the entire U₅ branch. The arbitrary
Hermitian intertwiner does not by itself mark the other simple root.

Source: Fong--Seitz I (4C), (6A)(b), pp.20--21,37--38;
II (8B), pp.201--202; DGS (11.7), pp.174--175.
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
/-- Construct the actual tensor module from the original marked quadratic profile. -/
theorem marked_quadratic_tensor_realization :
    let μ := markedLinearLocalMarking Q mark h split i hVi fi hfi hki
    ∃ (f : F ≃+* Field n)
      (e : Multiplicative (FourTensor.Core (Field n) (conjugation n) (conjugation_involutive n)) ≃*
        simpleRemainder Q split i),
      ∀ (g : SL(2,Field n)) (p : FourTensor.Core (Field n) (conjugation n) (conjugation_involutive n)),
        fieldRelabelledActor Q split i hVi μ si n f g * (e (.ofAdd p) : X ⧸ Q.D) *
          (fieldRelabelledActor Q split i hVi μ si n f g)⁻¹ =
        e (.ofAdd (hermitianAction (FourTensor.conjugation (Field n) (conjugation n))
          (conjugation_involutive n) g p)) := by
  dsimp only
  obtain ⟨_,_,_,_,hrj,he,hR,_,hcomm,_⟩ :=
    QuadrangleStructure.marked_quadratic_linear_sixA Q mark h split hm i j hij hVi hVj si sj
      fi fj hfi hfj hki hkj hfields hindexi hindexj helem hQi hQj hne
  let := he
  have hF : Nat.card F = 2^(2*n) := by rw [hfields,hk,←pow_mul,Nat.mul_comm n 2]
  have hc : Nat.card (simpleRemainder Q split i) = Nat.card F ^ 2 := by
    rw [hR,hfields]; ring
  exact tensorRealization_of_hermitian Q split i hVi _ si n
    (aligned_remainder_hermitian Q split i j hij hm hVi _ si n (NeZero.pos n)
      hF hc (hrj.trans hk) hcomm)

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
/-- Construct and collect the four positive maps on the SAME original quotient. -/
theorem original_quadratic_tensor_collected :
    let μ := markedLinearLocalMarking Q (originalMarkedIso Q) h split i hVi fi hfi hki
    ∃ (f : F ≃+* Field n)
      (e : Multiplicative (FourTensor.Core (Field n) (conjugation n) (conjugation_involutive n)) ≃*
        simpleRemainder Q split i),
      let l := fieldRelabelledActor Q split i hVi μ si n f
      let v := tensorEmbedding Q split (conjugation n) (conjugation_involutive n) i e
      let r := FourTensor.roots (Field n) (conjugation n) (conjugation_involutive n) l v
      FourPositive.Relations (Field n) (conjugation n) (conjugation_involutive n) r ∧
      r.generated = split.U ∧
      l (weyl (Field n)) = (si.val : (generated L S) ⧸ Q.D) ∧
      (∀ x ∈ (S.subgroupOf (generated L S)).map Q.q,
        ∃ a d c b, x = r.word a d c b) ∧
      ∀ (w : Fin 2 → Q.tits.N)
        (_hw : ∀ a, QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) (w a) = Q.simple a),
        r.generated ⊔ closure (Set.range (fun a => (w a : (generated L S) ⧸ Q.D))) = ⊤ := by
  dsimp only
  obtain ⟨f,e,he⟩ := marked_quadratic_tensor_realization Q (originalMarkedIso Q) h split
    hm i j hij hVi hVj si sj fi fj hfi hfj hki hkj hfields hindexi hindexj helem hQi hQj hne n hk
  let μ := markedLinearLocalMarking Q (originalMarkedIso Q) h split i hVi fi hfi hki
  let l := fieldRelabelledActor Q split i hVi μ si n f
  let v := tensorEmbedding Q split (conjugation n) (conjugation_involutive n) i e
  have hA := fieldRelabelledActor_root_range Q split i hVi μ si n f
  have hV := tensorEmbedding_range Q split (conjugation n) (conjugation_involutive n) i e
  refine ⟨f,e,FourTensor.relations (Field n) (conjugation n) (conjugation_involutive n) l v he,
    four_generated_eq_unipotent Q split (conjugation n) (conjugation_involutive n) l v i hA hV,
    fieldRelabelledActor_weyl Q split i hVi μ si n f,?_,?_⟩
  · exact four_originalS_collected_of_realization Q split (conjugation n)
      (conjugation_involutive n) l h i e hA he
  · intro w hw
    exact four_tensor_and_lifts_generate Q split w hw (conjugation n)
      (conjugation_involutive n) l v h i hA hV

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
