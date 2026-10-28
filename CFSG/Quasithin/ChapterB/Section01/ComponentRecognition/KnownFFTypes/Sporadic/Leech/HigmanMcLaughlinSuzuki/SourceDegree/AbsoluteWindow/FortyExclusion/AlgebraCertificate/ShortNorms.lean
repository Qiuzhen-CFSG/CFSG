module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FortyExclusion.AlgebraCertificate.ShortRelations
import all Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.FiveSubgroup

/-!
# Three additional norm relations on short HS words

Explicit words in the actual degree-100 HS carrier conjugate the published
five-element B to the three words below. Their cyclic norms therefore belong
to the literal five-center norm ideal. GAP supplies candidate conjugators;
Lean checks the inverse tables, word membership, and all conjugacy equations.
These relations are inputs for the universal norm-algebra calculation, not
a completed spanning or nilpotence certificate.

Source: ATLAS HSG1-p100B0; the Guralnick--Malle Proposition 5.1 HS application.
The reproducible search and candidate tables are in `source/`.
-/

@[expose] public section
open scoped BigOperators MonoidAlgebra
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FortyExclusion.AlgebraCertificate
namespace ShortNorms
open Theory.GroupTheory _root_.Sporadic.LeechRelated.HS

/-- Short products of A and powers of B; indices use `ShortRelations.letter`. -/
def shortWord (i : Fin 3) : List (Fin 3) :=
  match i.val with
  | 0 => [0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 1, 1, 0, 1, 1]
  | 1 => [0, 2, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1]
  | _ => [0, 2, 0, 2, 0, 1, 0, 2, 0, 1]

/-- An element of the exact carrier used by `NormCertificate`. -/
noncomputable def shortElement (i : Fin 3) : KnownSimple.SporadicName.hs.Carrier :=
  evalWord ShortRelations.letter (shortWord i)

private def packedLetter (s : Fin 3) : _root_.Sporadic.LeechRelated.HS.Carrier :=
  if s = 0 then FiveSubgroup.a else if s = 1 then FiveSubgroup.b else FiveSubgroup.b⁻¹

private theorem b_eq_generatorB : FiveSubgroup.b = generatorBElement := by
  apply Subtype.ext
  exact FiveSubgroup.bPerm_eq_generator

private theorem packedLetter_eq : packedLetter = ShortRelations.letter := by
  have ha : FiveSubgroup.a = generatorAElement := by
    apply Subtype.ext
    exact FiveSubgroup.aPerm_eq_generator
  funext s
  simp only [packedLetter, ShortRelations.letter, ha, b_eq_generatorB]
  rfl

private def conjugatorWord (i : Fin 3) : List (Fin 3) :=
  match i.val with
  | 0 => [0, 1, 1, 0, 2, 0, 1, 1, 0, 2, 0, 1, 1, 0, 2, 0, 1, 0, 2, 2, 0, 1, 0, 1, 0, 2, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 2, 0, 1, 0, 2, 0, 1]
  | 1 => [1, 1, 0, 1, 0, 2, 2, 0, 2, 0, 1, 1, 0, 2, 0, 1, 0, 2, 2, 0, 1, 0, 2, 0, 2, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 2, 0, 1, 1, 0, 2, 0, 2, 0, 1, 1, 0, 2, 2, 0, 1, 0, 1, 0, 2, 2, 0, 1]
  | _ => [0, 2, 0, 1, 0, 2, 0, 1, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 2, 0, 1, 0, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 2, 2, 2, 0, 1, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1]

private def conjugatorCode (i : Fin 3) : ℕ :=
  match i.val with
  | 0 => 336248760075952811760082247233250109305228441588705151944148192426708659239126121336694559112790195046987480215357081674495592771092435021764652832188525387468579622246351660402412199343541372400520272355790859
  | 1 => 3473250639148485470409459230559012738432877797236746827587275704964936112459695664359582619744527102314742249915705276921891533211009345765344552930352581085010138108197211427608704414128488935545422420950867595
  | _ => 3888076269636075989270879173160266686506483874298271862403425912064431711497575858293802799417430493203242512151921237176092167565838257632773029491272347096798493958247295352263113577605018883668433921727697547

private def conjugatorInvCode (i : Fin 3) : ℕ :=
  match i.val with
  | 0 => 3517928304494111366014505744683971947923947003713694018829806808469825745772465550831795043273808804292987530007200821604554780473889229580986062567225971624779945476332483891370373548494310607935609312995676212
  | 1 => 3101868397181161970915021204701693143508081669426889520260868886003549150984690089706397945376754418962470963469861137650493534993318480029011071587058640223163224436071224032653718659887631622662653591720185923
  | _ => 831935089335930444733021376911535239021256880539601142107790456346829228708243833521187674924867749015734414504698662698530614756117569485791989050880026216113288636532989536207132788541825491188157161943603419

private def conjugatorMap (i : Fin 3) (x : Fin 100) : Fin 100 :=
  ⟨(conjugatorCode i >>> (7 * x.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private def conjugatorInvMap (i : Fin 3) (x : Fin 100) : Fin 100 :=
  ⟨(conjugatorInvCode i >>> (7 * x.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem conjugatorLeft (i : Fin 3) :
    ∀ x, conjugatorInvMap i (conjugatorMap i x) = x := by
  fin_cases i <;> apply FiveSubgroup.allFin <;> decide +kernel

private def conjugatorPerm (i : Fin 3) : Equiv.Perm (Fin 100) :=
  tablePerm (conjugatorMap i) (conjugatorInvMap i) (conjugatorLeft i)
    (rightInverse_of_leftInverse_fin (conjugatorLeft i))

private theorem conjugatorPerm_eq_word (i : Fin 3) :
    conjugatorPerm i = ((evalWord packedLetter (conjugatorWord i) : _root_.Sporadic.LeechRelated.HS.Carrier) : Equiv.Perm (Fin 100)) := by
  fin_cases i <;> apply Equiv.ext <;> apply FiveSubgroup.allFin <;> decide +kernel

private def conjugator (i : Fin 3) : _root_.Sporadic.LeechRelated.HS.Carrier :=
  ⟨conjugatorPerm i, (conjugatorPerm_eq_word i).symm ▸
    (evalWord packedLetter (conjugatorWord i)).property⟩

private theorem conjugator_relation (i : Fin 3) :
    (conjugator i)⁻¹ * FiveSubgroup.b * conjugator i =
      evalWord packedLetter (shortWord i) := by
  fin_cases i <;> apply Subtype.ext <;> apply Equiv.ext <;>
    apply FiveSubgroup.allFin <;> decide +kernel

set_option backward.isDefEq.respectTransparency false in
/-- Each short word is conjugate to B by an actual carrier element. -/
theorem shortElement_conjugate_generatorB (i : Fin 3) :
    ∃ c : _root_.Sporadic.LeechRelated.HS.Carrier,
      c⁻¹ * generatorBElement * c = (shortElement i : _root_.Sporadic.LeechRelated.HS.Carrier) := by
  refine ⟨conjugator i, ?_⟩
  simpa only [b_eq_generatorB, packedLetter_eq, shortElement] using conjugator_relation i

/-- The cyclic norm on the short representative, in the literal binary algebra. -/
noncomputable def shortNorm (i : Fin 3) : BinaryAlgebra :=
  ∑ t : Fin 5, MonoidAlgebra.single (shortElement i ^ t.val) 1

private theorem norm_conjugate {G : Type*} [Group G] (g c : G) :
    (MonoidAlgebra.single c⁻¹ 1 : (ZMod 2)[G]) *
        (∑ t : Fin 5, MonoidAlgebra.single (g ^ t.val) 1) *
        MonoidAlgebra.single c 1 =
      ∑ t : Fin 5, MonoidAlgebra.single ((c⁻¹ * g * c) ^ t.val) 1 := by
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  simp only [MonoidAlgebra.single_mul_single, one_mul]
  apply congrArg (fun h : G => (MonoidAlgebra.single h 1 : (ZMod 2)[G]))
  simpa only [inv_inv] using (conj_pow (i := t.val) (a := c⁻¹) (b := g)).symm

set_option backward.isDefEq.respectTransparency false in
/-- These are universal norm-ideal relations, not checks in one representation. -/
theorem shortNorm_mem_fiveNormIdeal (i : Fin 3) : shortNorm i ∈ fiveNormIdeal := by
  obtain ⟨c, hc⟩ := shortElement_conjugate_generatorB i
  have he : (MonoidAlgebra.single c⁻¹ 1 : BinaryAlgebra) * generatorNorm *
      MonoidAlgebra.single c 1 = shortNorm i := by
    simpa only [generatorNorm, shortNorm, hc] using norm_conjugate generatorBElement c
  rw [← he]
  exact generatorNorm_translate_mem c⁻¹ c

/-- Any two-sided short-norm translate is permitted by the original contract. -/
theorem shortNorm_translate_mem (i : Fin 3)
    (g h : KnownSimple.SporadicName.hs.Carrier) :
    MonoidAlgebra.single g 1 * shortNorm i * MonoidAlgebra.single h 1 ∈
      fiveNormIdeal := by
  apply fiveNormIdeal.mul_mem_right
  apply fiveNormIdeal.mul_mem_left
  exact shortNorm_mem_fiveNormIdeal i

/-- The parent annihilation theorem applies to these literal additional seeds. -/
theorem shortNorm_action_eq_zero {K W : Type*} [Field K] [CharP K 2]
    [AddCommGroup W] [Module K W]
    (τ : Representation K KnownSimple.SporadicName.hs.Carrier W)
    (hfix : Representation.invariants (τ.comp fiveCenter.subtype) = ⊥) (i : Fin 3) :
    binaryAction τ (shortNorm i) = 0 :=
  (TwoSidedIdeal.mem_ker (binaryAction τ)).mp
    (fiveNormIdeal_le_kernel τ hfix (shortNorm_mem_fiveNormIdeal i))

end ShortNorms
end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FortyExclusion.AlgebraCertificate
