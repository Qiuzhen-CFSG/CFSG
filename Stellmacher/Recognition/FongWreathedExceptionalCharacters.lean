module
public import Stellmacher.Recognition.FongWreathedRationalRows
public import Stellmacher.Recognition.FongWreathedEightConstituents
public import Stellmacher.Recognition.FongWreathedInducedBlockMembership
public import Stellmacher.Recognition.FongWreathedContributionBounds

/-!
# Fong's exceptional characters

From a height-two wreathed Sylow subgroup and one solvable involution
centralizer, choose a compatible presentation and construct eight distinct
genuine principal-block irreducibles. Both signed induced-character
decompositions and the complete F and F³ columns are retained. The first four
are integer-valued, and every nonprincipal member has a faithful model.

The rational rows satisfy equations (8), (9), both order-four sum identities,
and all corrected degree conditions. Contribution estimates bound the J and
F² values by five; actual Sylow restriction supplies divisibility by 32.
Embedding the four rational characters in the whole block gives the required
square-sum inequality at XF², without asserting that they exhaust the block.

Source: P. Fong, *Some Sylow subgroups of order 32 and a characterization of
U(3,3)*, J. Algebra 6 (1967), printed pp.72–74; and
refs/original/n-group-global/sylow32-source-audit/fong-degree-calculation-audit.md.
-/

public section
noncomputable section
open scoped BigOperators
open Theory.Character ModularBlock PrincipalBlockConstruction
namespace Stellmacher.Recognition
open FongWreathedIntrinsic FongWreathedInduction
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

namespace FongRationalConstituents
variable {S : Sylow 2 G} {P : ABG.Wreathed.Presentation S 2}
variable (r : FongRationalConstituents (actualInducedOne S P) ((J P : S) : G))

omit [IsSimpleGroup G] in
/-- The four rational characters occupy distinct positions in the whole block,
so their squared order-four values have sum at most sixteen. -/
theorem orderFour_square_bound (d : PrincipalCongruenceBlockData G)
    (hc : LocalPrincipalColumnNormData S P d)
    (e : EightConstituents S P d r) :
    1 + r.row₂.b ^ 2 + r.row₃.b ^ 2 + r.row₄.b ^ 2 ≤ 16 := by
  classical
  have hm (i : Fin 4) : ∃ j ∈ d.block, ∀ g, r.four i g = d.chi j (ConjClasses.mk g) := by
    fin_cases i
    · simpa [four, e.first_four.1] using e.in_block 0
    · simpa [four, e.first_four.2.1] using e.in_block 1
    · simpa [four, e.first_four.2.2.1] using e.in_block 2
    · simpa [four, e.first_four.2.2.2] using e.in_block 3
  choose f hf hχ using hm
  have hfi : Function.Injective f := by
    intro i j hij
    apply r.four_injective
    ext g
    rw [hχ i g, hχ j g, hij]
  let g : G := ((X P * F P ^ 2 : S) : G)
  have hreal := congrArg Complex.re hc.XF_sq_column
  simp only [Complex.re_sum, Complex.star_def, Complex.mul_conj, Complex.ofReal_re] at hreal
  have hb : ∑ i, Complex.normSq (r.four i g) ≤ 16 := by
    calc
      _ = ∑ j ∈ Finset.univ.image f, Complex.normSq (d.chi j (ConjClasses.mk g)) := by
        rw [Finset.sum_image (fun i _ j _ h => hfi h)]
        exact Finset.sum_congr rfl (fun i _ => congrArg Complex.normSq (hχ i g))
      _ ≤ ∑ j ∈ d.block, Complex.normSq (d.chi j (ConjClasses.mk g)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
          exact hf i
        · intro j _ _
          exact Complex.normSq_nonneg _
      _ = 16 := hreal
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, four,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Pi.one_apply, g,
    r.row₂_values.2.2.1, r.row₃_values.2.2.1, r.row₄_values.2.2.1,
    Complex.normSq_one, Complex.normSq_intCast] at hb
  have hb' : 1 + (r.row₂.b * r.row₂.b + (r.row₃.b * r.row₃.b +
      r.row₄.b * r.row₄.b)) ≤ 16 := by exact_mod_cast hb
  nlinarith [hb']

/-- All numerical degree premises for the actual rational constituents. -/
theorem degree_conditions (d : PrincipalCongruenceBlockData G)
    (hl : LocalBlockData S P d) (e : EightConstituents S P d r) :
    FongDegreeConditions r.row₂ r.row₃ r.row₄ := by
  have hF₂ : r.χ₂ ((F P : S) : G) = (1 : ℤ) := by
    simpa [e.first_four.2.1] using e.F_values 1
  have hF₃ : r.χ₃ ((F P : S) : G) = (-1 : ℤ) := by
    simpa [e.first_four.2.2.1] using e.F_values 2
  have hF₄ : r.χ₄ ((F P : S) : G) = (-1 : ℤ) := by
    simpa [e.first_four.2.2.2] using e.F_values 3
  have hd₂ : r.row₂.d = r.d₂ := by exact_mod_cast r.row₂_values.1.symm.trans r.degrees.1
  have hd₃ : r.row₃.d = r.d₃ := by exact_mod_cast r.row₃_values.1.symm.trans r.degrees.2.1
  have hd₄ : r.row₄.d = r.d₄ := by exact_mod_cast r.row₄_values.1.symm.trans r.degrees.2.2
  have ha₂ : r.row₂.a = r.a₂ := by
    exact_mod_cast r.row₂_values.2.1.symm.trans r.involution_values.1
  have ha₃ : r.row₃.a = r.a₃ := by
    exact_mod_cast r.row₃_values.2.1.symm.trans r.involution_values.2.1
  have ha₄ : r.row₄.a = r.a₄ := by
    exact_mod_cast r.row₄_values.2.1.symm.trans r.involution_values.2.2
  refine ⟨?_, ?_, ?_, by simpa [hd₂, hd₃, hd₄] using r.degree_equation,
    by simpa [ha₂, ha₃, ha₄] using r.involution_equation,
    r.orderFour_sum, r.centralFour_sum,
    by simpa [hd₂, hd₃, hd₄, ha₂, ha₃, ha₄] using r.rational_identity,
    r.orderFour_square_bound d hl.toLocalPrincipalColumnNormData e⟩
  · exact fongRowConditions_of_character S P d hl r.irreducible.1 r.nonprincipal.1
      (by simpa [e.first_four.2.1] using e.in_block 1) r.integer_values.1 _ _
      r.row₂_values.1 r.row₂_values.2.1 r.row₂_values.2.2.1 r.row₂_values.2.2.2
      hF₂ (Or.inl rfl)
  · exact fongRowConditions_of_character S P d hl r.irreducible.2.1 r.nonprincipal.2.1
      (by simpa [e.first_four.2.2.1] using e.in_block 2) r.integer_values.2.1 _ _
      r.row₃_values.1 r.row₃_values.2.1 r.row₃_values.2.2.1 r.row₃_values.2.2.2
      hF₃ (Or.inr rfl)
  · exact fongRowConditions_of_character S P d hl r.irreducible.2.2 r.nonprincipal.2.2
      (by simpa [e.first_four.2.2.2] using e.in_block 3) r.integer_values.2.2 _ _
      r.row₄_values.1 r.row₄_values.2.1 r.row₄_values.2.2.1 r.row₄_values.2.2.2
      hF₄ (Or.inr rfl)
end FongRationalConstituents

namespace FongWreathedExceptional
/-- Actual exceptional characters with compatible local data and all the
corrected degree conditions. The packet retains both signed decompositions,
principal-block membership, and the complete F and F³ columns. -/
structure Characters (S : Sylow 2 G) (P : ABG.Wreathed.Presentation S 2)
    (d : PrincipalCongruenceBlockData G) where
  localData : LocalBlockData S P d
  rational : FongRationalConstituents (actualInducedOne S P) ((J P : S) : G)
  eight : EightConstituents S P d rational
  conditions : FongDegreeConditions rational.row₂ rational.row₃ rational.row₄

/-- Every nonprincipal character in the full packet admits a faithful
irreducible representation. -/
theorem Characters.faithful {S : Sylow 2 G} {P : ABG.Wreathed.Presentation S 2}
    {d : PrincipalCongruenceBlockData G} (c : Characters S P d)
    (i : Fin 8) (hi : i ≠ 0) :
    ∃ (m : ℕ) (ρ : Representation ℂ G (Fin m → ℂ)),
      Representation.IsIrreducible ρ ∧ c.eight.chi i = ρ.character ∧
        Function.Injective ρ := by
  apply (c.eight.irreducible i).exists_faithful_of_ne_one
  intro he
  apply hi
  exact c.eight.injective (he.trans c.eight.first_four.1.symm)

/-- Construct the complete packet from actual local data at a fixed
presentation. Every character and block-membership premise is discharged. -/
theorem characters_of_localBlockData (S : Sylow 2 G)
    (P : ABG.Wreathed.Presentation S 2) (d : PrincipalCongruenceBlockData G)
    (hl : LocalBlockData S P d) (x : G) (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))] :
    Nonempty (Characters S P d) := by
  obtain ⟨r⟩ := actual_rational_constituents S P
  obtain ⟨e⟩ := actual_eight_constituents S P d hl.toLocalPrincipalColumnNormData r
    (fun χ hχ hc => hc.elim
      (actualInducedOne_constituent_mem S P x hx d χ hχ)
      (actualInducedTwo_constituent_mem S P x hx d χ hχ))
  exact ⟨⟨hl, r, e, r.degree_conditions d hl e⟩⟩

/-- A wreathed Sylow subgroup of height two and one solvable involution
centralizer supply the complete exceptional packet in any actual principal block. -/
theorem exists_characters_for_block (S : Sylow 2 G) (hS : ABG.IsWreathedOfHeight S 2)
    (x : G) (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))]
    (d : PrincipalCongruenceBlockData G) :
    ∃ P : ABG.Wreathed.Presentation S 2, Nonempty (Characters S P d) := by
  obtain ⟨P, hl⟩ := exists_localBlockData S hS x hx d
  exact ⟨P, characters_of_localBlockData S P d hl x hx⟩

/-- Unconditional existence from the original group hypotheses, including
the actual principal-block datum and the compatible presentation. -/
theorem exists_characters (S : Sylow 2 G) (hS : ABG.IsWreathedOfHeight S 2)
    (x : G) (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))] :
    ∃ (P : ABG.Wreathed.Presentation S 2) (d : PrincipalCongruenceBlockData G),
      Nonempty (Characters S P d) := by
  obtain ⟨d⟩ := exists_principalCongruenceBlockData (G := G)
  obtain ⟨P, hc⟩ := exists_characters_for_block S hS x hx d
  exact ⟨P, d, hc⟩
end FongWreathedExceptional
end Stellmacher.Recognition
