module

public import Theory.SpecificGroups.Monster.Construction.LocalC.LatticeComparison

/-!
# Source words and Leech representatives for the short families

The four words in Aschbacher 27.8 are defined in the actual extraspecial
image `Q1Image` inside `N/K`. Their factors are reversed to translate the
book's right actions into Lean's left composition; `loopImage_val` and
`cocodeImage_val` identify the factors with the actual triality generators.
The fixed `sourceLatticeComparison` sends every word to its stated Leech
representative modulo twice the lattice.

For octads, the representative is constructed inside the lattice as
`f_c - f(J) - (|J|/2) f_X`; for even `J` its coordinates are `2 c - 4 J`.
For the odd family it is `f_(d + epsilon_x(d) X) - lambda_x`.
The pair representatives are `4(e_x + e_y)` and `4(e_x - e_y)`.
No representative is chosen from an abstract quadratic-space isometry.

`OctadParameters` records only the source parameter restrictions. Membership
in the minimal shell and exhaustion of the octad and odd families are separate
obligations. The common transfer lemmas identify tensors and corrections once
an explicit shell representative has been proved. The ATLAS shell theorem
already gives the three possible shapes for any actual short lift.

Source: Michael Aschbacher, *Sporadic Groups*, Lemma 27.8 and its preceding
remark, printed p. 150 (PDF page 81, left page). The lattice results are
reused from the attributed ATLAS ports; no ATLAS source is copied here.
-/

@[expose] public section
noncomputable section
open Atlas.Codes Atlas.Fischer Atlas.Lattices
open scoped BigOperators
namespace Sporadic.Monster.Construction.LocalC.ShortFamilies
open TrialitySpin
attribute [local instance] Classical.propDecidable

abbrev Lift := ShortLift sourceLatticeComparison

abbrev Space := ShortSpace sourceLatticeComparison

def pointWord (x : Omega) : BinaryWord := Pi.single x 1

def pairWord (x y : Omega) : BinaryWord := pointWord x + pointWord y

/-- The actual image of the first Parker-loop triality generator. -/
def loopImage (d : ParkerLoop) : Q1Image := q1ImageMap (q1Param (d,0,0))

/-- The actual image of the source automorphism `psi_1(alpha_J)`. -/
def cocodeImage (J : BinaryWord) : Q1Image :=
  q1ImageMap (q1Param (loopOne,0,Submodule.Quotient.mk J))

theorem loopImage_val (d : ParkerLoop) :
    (loopImage d).val = nQuotientMap (psi1N d) := by
  change nQuotientMap (q1Word d 0 0).val = _
  rw [q1Word_cocode_zero]
  change nQuotientMap (psi2N loopOne * psi1N d) = _
  rw [TrialityGeneratorCalculation.psi2_one, one_mul]

theorem cocodeImage_val (J : BinaryWord) :
    (cocodeImage J).val = nQuotientMap (psiAut1N
      (parkerCocodeStandard (Submodule.Quotient.mk J))) := by
  change nQuotientMap (psiAut1N _ * psi2N loopOne * psi1N loopOne) = _
  rw [TrialityGeneratorCalculation.psi2_one, TrialityGeneratorCalculation.psi1_one,
    mul_one, mul_one]

theorem loopImage_class (d : ParkerLoop) :
    latticeClass sourceLatticeComparison (loopImage d) =
      leechReduction (sourceCodeVector d.1) := by
  rw [loopImage, sourceLatticeClass_image, sourceQ1LatticeHom_apply, q1Coordinates_param]
  simp [sourceCoordinateMap, q1WordCoordinates]

theorem cocodeImage_class (J : BinaryWord) :
    latticeClass sourceLatticeComparison (cocodeImage J) = sourceWordClass J := by
  rw [cocodeImage, sourceLatticeClass_image, sourceQ1LatticeHom_apply, q1Coordinates_param]
  simp [sourceCoordinateMap, q1WordCoordinates, loopOne, sourceWordClass_eq_reduction]

theorem loopImage_sign (s : ParkerBit) (d : ParkerLoop) :
    loopImage (parkerSign s d) = q1ImageCenterGenerator ^ s.val * loopImage d := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_pow, loopImage_val, psi1N_sign, map_mul, map_pow]
  rfl

/-- The source `r(c,J)` word, before imposing the octad parameter restrictions. -/
def rOctadElement (c : ParkerLoop) (J : BinaryWord) : Q1Image :=
  loopImage parkerOmega ^ (hammingNorm J / 2) * cocodeImage J * loopImage c

/-- The source `r(x,d)` word, with its prescribed point-dependent exponent. -/
def rOddElement (x : Omega) (d : ParkerLoop) : Q1Image :=
  loopImage d * loopImage parkerOmega ^ (d.1.val x).val * cocodeImage (pointWord x)

/-- The source `r_u(xy)`, with the factors in left-composition order. -/
def ruElement (x y : Omega) : Q1Image :=
  loopImage parkerOmega * cocodeImage (pairWord x y)

/-- The source `r_v(xy)`. -/
def rvElement (x y : Omega) : Q1Image := cocodeImage (pairWord x y)

/-- An octad lift and an even subset of its support, exactly as in 27.8(2). -/
structure OctadParameters where
  c : ParkerLoop
  J : BinaryWord
  octad : hammingNorm c.1.val = 8
  supported : ∀ i, J i ≠ 0 → c.1.val i ≠ 0
  even : Even (hammingNorm J)

def octadCoordinates (c : ParkerLoop) (J : BinaryWord) : IntegerCoordinates :=
  fun i => 2 * golayIntegerLift c.1.val i - 4 * golayIntegerLift J i

def octadRepresentative (c : ParkerLoop) (J : BinaryWord) : leech :=
  sourceCodeVector c.1 - sourceCocodeVector J -
    (hammingNorm J / 2) • sourceCodeVector golayOne

def oddCode (x : Omega) (d : ParkerLoop) : golay := d.1 + d.1.val x • golayOne

def oddRepresentative (x : Omega) (d : ParkerLoop) : leech :=
  sourceCodeVector (oddCode x d) + sourcePointVector x

def uRepresentative (x y : Omega) : leech :=
  sourcePointVector x + sourcePointVector y + sourceCodeVector golayOne

def vRepresentative (x y : Omega) : leech := sourcePointVector x - sourcePointVector y

theorem sourceWordClass_point (x : Omega) :
    sourceWordClass (pointWord x) = leechReduction (sourcePointVector x) := by
  simp [sourceWordClass, pointWord, Pi.single_apply]

theorem sourceWordClass_pair (x y : Omega) :
    sourceWordClass (pairWord x y) =
      leechReduction (sourcePointVector x) + leechReduction (sourcePointVector y) := by
  rw [pairWord, map_add, sourceWordClass_point, sourceWordClass_point]

theorem class_pow (q : Q1Image) (n : ℕ) :
    latticeClass sourceLatticeComparison (q ^ n) = n • latticeClass sourceLatticeComparison q := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ,latticeClass_mul,ih,add_nsmul,one_nsmul]

theorem rOctadElement_class (c : ParkerLoop) (J : BinaryWord) :
    latticeClass sourceLatticeComparison (rOctadElement c J) =
      leechReduction (octadRepresentative c J) := by
  simp only [rOctadElement,latticeClass_mul,class_pow,loopImage_class,cocodeImage_class,
    octadRepresentative,sub_eq_add_neg,map_add,leechReduction_neg,map_nsmul,
    sourceWordClass_eq_reduction]
  change (hammingNorm J / 2) • leechReduction (sourceCodeVector golayOne) +
      leechReduction (sourceCocodeVector J) + leechReduction (sourceCodeVector c.1) = _
  abel

theorem octadRepresentative_apply (c : ParkerLoop) (J : BinaryWord) (hJ : Even (hammingNorm J))
    (i : Omega) : (octadRepresentative c J).val i = octadCoordinates c J i := by
  have he : (hammingNorm J : ℤ) = 2 * (hammingNorm J / 2 : ℕ) := by
    obtain ⟨k,hk⟩ := hJ
    have hn : hammingNorm J = 2 * (hammingNorm J / 2) := by omega
    exact_mod_cast hn
  change (sourceCodeVector c.1).val i - (sourceCocodeVector J).val i -
    (hammingNorm J / 2 : ℕ) • (sourceCodeVector golayOne).val i = _
  rw [sourceCodeVector_apply,sourceCocodeVector_apply,sourceCodeVector_one_apply]
  simp only [octadCoordinates,nsmul_eq_mul,he]
  ring

theorem rOddElement_class (x : Omega) (d : ParkerLoop) :
    latticeClass sourceLatticeComparison (rOddElement x d) =
      leechReduction (oddRepresentative x d) := by
  rw [rOddElement,latticeClass_mul,latticeClass_mul,loopImage_class,class_pow,
    loopImage_class,cocodeImage_class,sourceWordClass_point]
  simp only [oddRepresentative,map_add,oddCode,sourceCodeClass_add_smul_one]
  change _ + (d.1.val x).val • leechReduction (sourceCodeVector golayOne) + _ = _
  rw [← Nat.cast_smul_eq_nsmul Bit, ZMod.natCast_zmod_val]

/-- Attach a proved minimal representative to an actual extraspecial element. -/
def ofRepresentative (q : Q1Image) (v : LeechShell 4)
    (h : latticeClass sourceLatticeComparison q = leechReduction v.val) : Lift :=
  ⟨q, h ▸ (shortReduction v).prop⟩

theorem ofRepresentative_class (q : Q1Image) (v : LeechShell 4)
    (h : latticeClass sourceLatticeComparison q = leechReduction v.val) :
    shortLiftClass sourceLatticeComparison (ofRepresentative q v h) = shortReduction v :=
  Subtype.ext h

theorem ofRepresentative_tensor (q : Q1Image) (v : LeechShell 4)
    (h : latticeClass sourceLatticeComparison q = leechReduction v.val) :
    shortLiftTensor sourceLatticeComparison (ofRepresentative q v h) = rankOne (leechVector v.val) := by
  rw [shortLiftTensor, ofRepresentative_class, shortTensor_eq]

theorem ofRepresentative_correction (q : Q1Image) (v : LeechShell 4)
    (h : latticeClass sourceLatticeComparison q = leechReduction v.val) (a : NaturalSpace) :
    shortLiftCorrection sourceLatticeComparison (ofRepresentative q v h) a =
      vectorCorrection (leechVector v.val) a := by
  rw [shortLiftCorrection, ofRepresentative_class, shortCorrection_eq]

/-- An actual short lift whose lattice class has a representative in the specified shell family. -/
def HasShape (S : Finset IntegerCoordinates) (q : Lift) : Prop :=
  ∃ v : LeechShell 4, shortReduction v = shortLiftClass sourceLatticeComparison q ∧ v.val.val ∈ S

theorem shape_trichotomy (q : Lift) :
    HasShape (twoFourFamily 8 0) q ∨ HasShape (oddNoFiveVectors 1) q ∨
      HasShape (twoFourFamily 0 2) q := by
  obtain ⟨v, hv⟩ := shortReduction_surjective (shortLiftClass sourceLatticeComparison q)
  have h : v.val.val ∈ minimalVectors := (minimalVectors_iff _).mpr ⟨v.val.prop, v.prop⟩
  rcases Finset.mem_union.mp h with h | h
  · rcases Finset.mem_union.mp h with h | h
    · exact Or.inr (Or.inr ⟨v, hv, h⟩)
    · exact Or.inl ⟨v, hv, h⟩
  · exact Or.inr (Or.inl ⟨v, hv, h⟩)

theorem form_vector (q r : Lift) :
    shortForm sourceLatticeComparison (shortVector sourceLatticeComparison q)
      (shortVector sourceLatticeComparison r) =
      (if q = r then 1 else 0) - (if q = (shortLiftSigns sourceLatticeComparison).flip r then 1 else 0) :=
  (shortLiftSigns sourceLatticeComparison).form_delta q _

theorem form_vector_eq_zero (q r : Lift)
    (h : shortLiftClass sourceLatticeComparison q ≠ shortLiftClass sourceLatticeComparison r) :
    shortForm sourceLatticeComparison (shortVector sourceLatticeComparison q)
      (shortVector sourceLatticeComparison r) = 0 := by
  have hn := not_or.mp (mt (shortLiftClass_eq_iff sourceLatticeComparison q r).mpr h)
  rw [form_vector, if_neg hn.1, if_neg hn.2, sub_self]

theorem span_shortVectors :
    Submodule.span ℝ (Set.range (shortVector sourceLatticeComparison)) = ⊤ := by
  apply top_unique
  rw [← (shortBasis sourceLatticeComparison).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨a,rfl⟩
  exact ⟨_, (shortBasis_eq_vector sourceLatticeComparison a).symm⟩

theorem magnitudeSupport_neg (a : IntegerCoordinates) (r : ℤ) :
    evenMagnitudeSupport (-a) r = evenMagnitudeSupport a r := by
  ext i
  simp [evenMagnitudeSupport]

theorem support_eq_of_reduction_eq (a b : LeechShell 4) (h : shortReduction a = shortReduction b)
    (r : ℤ) : evenMagnitudeSupport a.val.val r = evenMagnitudeSupport b.val.val r := by
  rcases (shortReduction_eq_iff _ _).mp h with h | h
  · rw [h]
  · rw [h]
    exact magnitudeSupport_neg b.val.val r

theorem hasShape_flip (S : Finset IntegerCoordinates) (q : Lift) :
    HasShape S ((shortLiftSigns sourceLatticeComparison).flip q) ↔ HasShape S q := by
  have h : shortLiftClass sourceLatticeComparison ((shortLiftSigns sourceLatticeComparison).flip q) =
      shortLiftClass sourceLatticeComparison q :=
    (shortLiftClass_eq_iff sourceLatticeComparison _ _).mpr (Or.inr rfl)
  simp only [HasShape,h]

end Sporadic.Monster.Construction.LocalC.ShortFamilies
