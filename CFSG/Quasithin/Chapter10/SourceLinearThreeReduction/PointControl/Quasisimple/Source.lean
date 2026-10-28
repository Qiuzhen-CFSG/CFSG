module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Contracts
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Symplectic
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.RankTwo.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.SixDimensional
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.BinaryFour
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.Rudvalis
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.Held
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.JankoNatural
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.JankoNaturalDual
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.LinearNatural
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.MathieuNatural
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.HSNatural
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.MathieuTwentyThree
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.LargeMoved

/-!
# Conditional assembly of the non-A₅ quasisimple point branch

The full Theorem C carrier catalogue gives an exhaustive split. Both
inspections feed common centralization or the marked symplectic exception;
the original moved normalizer and the proved prime-scalar obstruction
close those endpoints. The two inspections remain independent source
obligations, so this module does not yet assert unconditional 10.2.9.

The final application supplies this branch to the parent's actual
point-control assembly. Source: Aschbacher--Smith 10.2.9, pp.750--751.
The completed comparisons exclude the entire non-A₅ binary rank-one
family. The final Ree comparison places the actual smaller subgroup in
the linear parabolic residual and proves common centralization.
The native Held and Rudvalis two-local orders, M₂₄ large-elementary
normalizers, and J₄ prime-31 and Sylow-three exponent comparisons exclude
every complementary rank-one row.
The original binary-three family has no rank-two or M₂₂ containing carrier.
The four-natural binary-three row is excluded by the size of its literal
moved image. Every reduced binary-three section of order at least 64
now leaves only J₄, by the literal automorphism-rank saturation argument.
The seven-element fixer comparison also excludes L₄(2) for every original
binary-three row. The Rudvalis involution-centralizer comparison excludes
that carrier for every such row, including natural sections. The full-Sylow
maximal two-local comparison also excludes Held on every such row. The
J₄ natural and dual sections are excluded by the full-Sylow extraspecial-core
comparison, retaining fixed kernels. The trivial-commutant argument also
excludes J₄ for the natural-plus-dual row, completing that entire row. The
L₅(2) transvection-core comparison, the M₂₄ central-involution comparison,
and the HS Sylow-normalized section comparison exclude those carriers.
The actual moved-normalizer restriction excludes M₂₃ for every binary-three
row, completing the natural and dual sections, including their fixed kernels
and nonsplit extensions.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The refined source catalogue after the nonbinary exceptional and J₁
comparisons. Each surviving carrier retains an actual model isomorphism. -/
theorem center_quotient_remaining_carriers_refined
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I) :
    RankTwo.ResidualModel (I ⧸ center I) ∨
    (∃ n, (n = 4 ∨ n = 5) ∧ ClassicalGroup.IsPSL (I ⧸ center I) n 2) ∨
    (∃ name : ClassificationModels.SporadicName,
      (name = .m22 ∨ name = .m23 ∨ name = .m24 ∨ name = .j4 ∨
        name = .hs ∨ name = .he ∨ name = .ru) ∧
      Nonempty ((I ⧸ center I) ≃* name.Carrier)) := by
  by_cases hm : ∃ n, ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) n
  · exact .inl (RankTwo.remaining_exceptional_models D c hm)
  · exact .inr (Other.remaining_binary_or_sporadic D c hm)

/-- The actual point-control carrier list after both G₂ branches have
been discharged. Every remaining alternative retains its model equivalence. -/
theorem center_quotient_remaining_nonderived_carriers
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I) :
    Nonempty ((I ⧸ center I) ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) ∨
    (∃ m, 1 ≤ m ∧ Nonempty ((I ⧸ center I) ≃* ReeF4.Model m)) ∨
    (∃ n, (n = 4 ∨ n = 5) ∧ ClassicalGroup.IsPSL (I ⧸ center I) n 2) ∨
    (∃ name : ClassificationModels.SporadicName,
      (name = .m22 ∨ name = .m23 ∨ name = .m24 ∨ name = .j4 ∨
        name = .hs ∨ name = .he ∨ name = .ru) ∧
      Nonempty ((I ⧸ center I) ≃* name.Carrier)) := by
  by_cases hm : ∃ n, ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) n
  · rcases RankTwo.remaining_triality_or_ree D c hm with ht | hr
    · exact .inl ht
    · exact .inr (.inl hr)
  · exact .inr (.inr (Other.remaining_binary_or_sporadic D c hm))

/-- The original binary-three point branch has no rank-two containing carrier.
This applies to every module row and to the literal escaping component. -/
theorem center_quotient_remaining_carriers_of_binary_three
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I)
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) :
    (∃ n, (n = 4 ∨ n = 5) ∧ ClassicalGroup.IsPSL (I ⧸ center I) n 2) ∨
    (∃ name : ClassificationModels.SporadicName,
      (name = .m22 ∨ name = .m23 ∨ name = .m24 ∨ name = .j4 ∨
        name = .hs ∨ name = .he ∨ name = .ru) ∧
      Nonempty ((I ⧸ center I) ≃* name.Carrier)) :=
  Other.remaining_binary_or_sporadic D c (RankTwo.not_rank_two_of_binary_three D c dL)

/-- The refined original binary-three carrier list excludes M₂₂ by its
seven-free full-Sylow two-locals. No module row or fixed vector is omitted. -/
theorem center_quotient_remaining_carriers_of_binary_three_refined
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I)
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) :
    (∃ n, (n = 4 ∨ n = 5) ∧ ClassicalGroup.IsPSL (I ⧸ center I) n 2) ∨
    (∃ name : ClassificationModels.SporadicName,
      (name = .m23 ∨ name = .m24 ∨ name = .j4 ∨
        name = .hs ∨ name = .he ∨ name = .ru) ∧
      Nonempty ((I ⧸ center I) ≃* name.Carrier)) :=
  Other.remaining_of_binary_three D c dL (RankTwo.not_rank_two_of_binary_three D c dL)

/-- The actual binary-three configuration now leaves only L₅(2) and the
six complementary sporadic carriers. The seven-element fixer excludes
L₄(2) on the literal embedding, for every module row and fixed kernel. -/
theorem center_quotient_remaining_five_or_sporadic_of_binary_three
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I)
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) :
    ClassicalGroup.IsPSL (I ⧸ center I) 5 2 ∨
    (∃ name : ClassificationModels.SporadicName,
      (name = .m23 ∨ name = .m24 ∨ name = .j4 ∨
        name = .hs ∨ name = .he ∨ name = .ru) ∧
      Nonempty ((I ⧸ center I) ≃* name.Carrier)) := by
  rcases center_quotient_remaining_carriers_of_binary_three_refined D c dL with
    ⟨n,hn,hm⟩ | hs
  · rcases hn with rfl | rfl
    · exact (Other.not_binary_four_of_binary_three D c dL hm).elim
    · exact .inl hm
  · exact .inr hs

/-- The remaining original binary-three carriers after the literal Rudvalis
fixer comparison. All module rows and fixed kernels are retained. -/
theorem center_quotient_remaining_carriers_of_binary_three_without_rudvalis
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I)
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) :
    ClassicalGroup.IsPSL (I ⧸ center I) 5 2 ∨
    (∃ name : ClassificationModels.SporadicName,
      (name = .m23 ∨ name = .m24 ∨ name = .j4 ∨ name = .hs ∨ name = .he) ∧
      Nonempty ((I ⧸ center I) ≃* name.Carrier)) := by
  rcases center_quotient_remaining_five_or_sporadic_of_binary_three D c dL with
    hlinear | ⟨name,hname,⟨e⟩⟩
  · exact .inl hlinear
  · rcases hname with rfl | rfl | rfl | rfl | rfl | rfl
    · exact .inr ⟨.m23,by simp,⟨e⟩⟩
    · exact .inr ⟨.m24,by simp,⟨e⟩⟩
    · exact .inr ⟨.j4,by simp,⟨e⟩⟩
    · exact .inr ⟨.hs,by simp,⟨e⟩⟩
    · exact .inr ⟨.he,by simp,⟨e⟩⟩
    · exact (Other.not_rudvalis_of_binary_three D c dL e).elim

/-- The literal full-Sylow Held comparison further reduces the original
binary-three carrier list, including natural sections and fixed kernels. -/
theorem center_quotient_remaining_carriers_of_binary_three_without_held
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I)
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) :
    ClassicalGroup.IsPSL (I ⧸ center I) 5 2 ∨
    (∃ name : ClassificationModels.SporadicName,
      (name = .m23 ∨ name = .m24 ∨ name = .j4 ∨ name = .hs) ∧
      Nonempty ((I ⧸ center I) ≃* name.Carrier)) := by
  rcases center_quotient_remaining_carriers_of_binary_three_without_rudvalis D c dL with
    hlinear | ⟨name,hname,⟨e⟩⟩
  · exact .inl hlinear
  · rcases hname with rfl | rfl | rfl | rfl | rfl
    · exact .inr ⟨.m23,by simp,⟨e⟩⟩
    · exact .inr ⟨.m24,by simp,⟨e⟩⟩
    · exact .inr ⟨.j4,by simp,⟨e⟩⟩
    · exact .inr ⟨.hs,by simp,⟨e⟩⟩
    · exact (Other.not_held_of_binary_three D c dL e).elim

/-- A genuinely irreducible reduced binary-three section excludes J₄ by
its literal core comparison. Irreducibility is an explicit property of these
coordinates, never inferred for an arbitrary selected setup. -/
theorem center_quotient_remaining_carriers_of_irreducible_binary_three
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I)
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) L W} [ρ.IsIrreducible]
    (d : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)) ρ)
    (hc : 2 < Nat.card W) :
    ClassicalGroup.IsPSL (I ⧸ center I) 5 2 ∨
    (∃ name : ClassificationModels.SporadicName,
      (name = .m23 ∨ name = .m24 ∨ name = .hs) ∧
      Nonempty ((I ⧸ center I) ≃* name.Carrier)) := by
  rcases center_quotient_remaining_carriers_of_binary_three_without_held D c dL with
    hlinear | ⟨name,hname,⟨e⟩⟩
  · exact .inl hlinear
  · rcases hname with rfl | rfl | rfl | rfl
    · exact .inr ⟨.m23,by simp,⟨e⟩⟩
    · exact .inr ⟨.m24,by simp,⟨e⟩⟩
    · exact (Other.not_jankoFour_of_irreducible_section D c d hc e).elim
    · exact .inr ⟨.hs,by simp,⟨e⟩⟩

/-- The actual natural section supplies the irreducibility premise and removes
J₄ from the source carrier list without changing its fixed kernel. -/
theorem center_quotient_remaining_carriers_of_natural_binary_three
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I)
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (d : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
      ((Representation.specialLinearNatural (k := ZMod 2) 3).comp
        (dL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    ClassicalGroup.IsPSL (I ⧸ center I) 5 2 ∨
    (∃ name : ClassificationModels.SporadicName,
      (name = .m23 ∨ name = .m24 ∨ name = .hs) ∧
      Nonempty ((I ⧸ center I) ≃* name.Carrier)) := by
  let q := dL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let : Representation.IsIrreducible
      ((Representation.specialLinearNatural (k := ZMod 2) 3).comp q) :=
    (Representation.irreducible_comp_surjective_iff q
      (dL.surjective.comp (QuotientGroup.mk'_surjective _)) _).mpr
      BinaryLinearThree.IrreducibleCatalogue.natural_irreducible
  exact center_quotient_remaining_carriers_of_irreducible_binary_three D c dL d (by
    simp only [Nat.card_fun,Nat.card_fin,Nat.card_zmod]; decide)

/-- The three native model comparisons leave only M₂₃ for a reduced
irreducible section of order at least eight, retaining its fixed kernel. -/
theorem center_quotient_mathieuTwentyThree_of_large_irreducible_binary_three
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I)
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) L W} [ρ.IsIrreducible]
    (d : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)) ρ)
    (hc : 8 ≤ Nat.card W) : Nonempty ((I ⧸ center I) ≃* Sporadic.Mathieu.M23) := by
  have h168 : 168 ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr dL.toEquiv,Matrix.PSL3Two.card_SL]
  have hsmall : 2 < Nat.card W := lt_of_lt_of_le (by decide) hc
  rcases center_quotient_remaining_carriers_of_irreducible_binary_three D c dL d hsmall with
    hlinear | ⟨name,hname,⟨e⟩⟩
  · exact (Other.not_binary_five_model_of_irreducible_section D c d hsmall
      ((by decide : 7 ∣ 168).trans h168) hlinear).elim
  · rcases hname with rfl | rfl | rfl
    · exact ⟨e⟩
    · exact (Other.not_mathieuTwentyFour_of_irreducible_section D c d hsmall e).elim
    · exact (Other.not_higmanSims_of_large_section D c d hc h168 e).elim

/-- The actual natural binary-three coordinates supply all module premises. -/
theorem center_quotient_mathieuTwentyThree_of_natural_binary_three
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I)
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (d : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
      ((Representation.specialLinearNatural (k := ZMod 2) 3).comp
        (dL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    Nonempty ((I ⧸ center I) ≃* Sporadic.Mathieu.M23) := by
  let q := dL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let : Representation.IsIrreducible
      ((Representation.specialLinearNatural (k := ZMod 2) 3).comp q) :=
    (Representation.irreducible_comp_surjective_iff q
      (dL.surjective.comp (QuotientGroup.mk'_surjective _)) _).mpr
      BinaryLinearThree.IrreducibleCatalogue.natural_irreducible
  exact center_quotient_mathieuTwentyThree_of_large_irreducible_binary_three D c dL d (by
    simp only [Nat.card_fun,Nat.card_fin,Nat.card_zmod]; decide)

/-- The dual marking gives the same literal M₂₃ frontier. -/
theorem center_quotient_mathieuTwentyThree_of_dual_binary_three
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I)
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (d : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
      ((Representation.specialLinearNatural (k := ZMod 2) 3).dual.comp
        (dL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    Nonempty ((I ⧸ center I) ≃* Sporadic.Mathieu.M23) := by
  let q := dL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let : Representation.IsIrreducible
      ((Representation.specialLinearNatural (k := ZMod 2) 3).dual.comp q) :=
    (Representation.irreducible_comp_surjective_iff q
      (dL.surjective.comp (QuotientGroup.mk'_surjective _)) _).mpr
      BinaryLinearThree.IrreducibleCatalogue.dual_irreducible
  apply center_quotient_mathieuTwentyThree_of_large_irreducible_binary_three D c dL d
  rw [Nat.card_congr (Pi.basisFun (ZMod 2) (Fin 3)).dualBasis.equivFun.toEquiv,
    Nat.card_fun,Nat.card_fin,Nat.card_zmod]
  decide

/-- The even-degree rank-one source family also reduces to the complementary
carriers, without an A₅ identification or a module irreducibility premise. -/
theorem center_quotient_remaining_carriers_of_even_binary_quotient
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I)
    {n : ℕ} (hn : 0 < n) (he : Even n)
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) :
    (∃ r, (r = 4 ∨ r = 5) ∧ ClassicalGroup.IsPSL (I ⧸ center I) r 2) ∨
    (∃ name : ClassificationModels.SporadicName,
      (name = .m22 ∨ name = .m23 ∨ name = .m24 ∨ name = .j4 ∨
        name = .hs ∨ name = .he ∨ name = .ru) ∧
      Nonempty ((I ⧸ center I) ≃* name.Carrier)) :=
  Other.remaining_binary_or_sporadic D c
    (RankTwo.not_rank_two_of_even_binary_quotient D c hn he hL)

/-- Apply the completed carrier exclusions to the actual point-control
configuration. The remaining alternatives retain genuine model equivalences;
their embedding and module comparisons are still source obligations. -/
theorem center_quotient_remaining_carriers
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I) :
    RankTwo.RemainingModel (I ⧸ center I) ∨
    (∃ n, (n = 4 ∨ n = 5) ∧ ClassicalGroup.IsPSL (I ⧸ center I) n 2) ∨
    (∃ name : ClassificationModels.SporadicName,
      (name = .m22 ∨ name = .m23 ∨ name = .m24 ∨ name = .j4 ∨
        name = .hs ∨ name = .he ∨ name = .ru) ∧
      Nonempty ((I ⧸ center I) ≃* name.Carrier)) ∨
    Nonempty ((I ⧸ center I) ≃* Janko1.Model) := by
  by_cases hm : ∃ n, ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) n
  · exact .inl (RankTwo.remaining_models D c hm)
  · exact .inr (Other.remaining_carriers D c hm)

/-- The complete quasisimple exclusion for every non-A₅ even-degree
binary rank-one original quotient. It applies to the literal escaping
component, retaining fixed vectors and every module row. -/
theorem quasisimple_impossible_of_even_binary_quotient
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I)
    {n : ℕ} (hn : 1 < n) (he : Even n)
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))) : False :=
  Other.not_remaining_of_even_binary_quotient D c hn he hL hna
    (center_quotient_remaining_carriers_of_even_binary_quotient D c (by omega) he hL)

/-- Apply the degree sieve to the complete source catalogue. A remaining
rank-one configuration has either an actual Ree carrier or degree three or
five; no module-irreducibility or later generation bound is assumed. -/
theorem ree_or_binary_degree_three_or_five
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I)
    {n : ℕ} (hn : 1 < n)
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))) :
    (∃ m, 1 ≤ m ∧ Nonempty ((I ⧸ center I) ≃* ReeF4.Model m)) ∨ (n = 3 ∨ n = 5) := by
  by_cases hm : ∃ r, ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) r
  · exact .inl (RankTwo.remaining_ree_models D c hm)
  · exact .inr (Other.binary_degree_three_or_five D c hn hL hna
      (Other.remaining_binary_or_sporadic D c hm))

/-- The precise remaining rank-one carrier pairs, on the original quotient
and point configuration. All higher binary-linear containing carriers have
been excluded, with no irreducibility or later generation-bound premise. -/
theorem ree_or_rankone_sporadic_residual
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I)
    {n : ℕ} (hn : 1 < n)
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))) :
    (∃ m, 1 ≤ m ∧ Nonempty ((I ⧸ center I) ≃* ReeF4.Model m)) ∨
    (n = 3 ∧ ∃ name : ClassificationModels.SporadicName,
      (name = .m24 ∨ name = .j4 ∨ name = .he ∨ name = .ru) ∧
      Nonempty ((I ⧸ center I) ≃* name.Carrier)) ∨
    (n = 5 ∧ Nonempty ((I ⧸ center I) ≃* Janko4.Model)) := by
  by_cases hm : ∃ r, ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) r
  · exact .inl (RankTwo.remaining_ree_models D c hm)
  · exact .inr (Other.binary_quotient_sporadic_residual D c hn hL hna
      (Other.remaining_binary_or_sporadic D c hm))

/-- The original rank-one quotient now leaves only Ree or J₄. The J₄
branch retains its actual central-quotient isomorphism and degree. -/
theorem ree_or_janko_four
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I)
    {n : ℕ} (hn : 1 < n)
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))) :
    (∃ m, 1 ≤ m ∧ Nonempty ((I ⧸ center I) ≃* ReeF4.Model m)) ∨
      ((n = 3 ∨ n = 5) ∧ Nonempty ((I ⧸ center I) ≃* Janko4.Model)) := by
  by_cases hr : ∃ r, ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) r
  · exact .inl (RankTwo.remaining_ree_models D c hr)
  · exact .inr (Other.binary_quotient_janko_four D c hn hL hna hr)

/-- The entire original non-A₅ binary rank-one family now leaves only
an actual Ree central quotient. All complementary cases have been
excluded on their literal embeddings, retaining fixed vectors. -/
theorem center_quotient_ree_of_binary_quotient
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I)
    {n : ℕ} (hn : 1 < n)
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))) :
    ∃ m, 1 ≤ m ∧ Nonempty ((I ⧸ center I) ≃* ReeF4.Model m) := by
  by_cases hr : ∃ r, ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) r
  · exact RankTwo.remaining_ree_models D c hr
  · exact (Other.not_complementary_of_binary_quotient D c hn hL hna hr).elim

/-- The complete quasisimple exclusion for every non-A₅ binary rank-one
original quotient. Ree placement and its automorphism fixer discharge the
last carrier, retaining the original module and all nonidentity vectors. -/
theorem quasisimple_impossible_of_binary_quotient
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I)
    {n : ℕ} (hn : 1 < n)
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))) : False := by
  obtain ⟨m,hm,⟨e⟩⟩ := center_quotient_ree_of_binary_quotient D c hn hL hna
  exact RankTwo.not_ree_of_binary_quotient D c (by omega) hL hm e

/-- Every containing carrier is excluded for the literal four-natural
binary-three section, including its fixed-vector and nonsplit variants. -/
theorem quasisimple_impossible_of_four_binary_three
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I)
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (d : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
      (fourBinaryThreeNatural.comp
        (dL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) : False :=
  not_complementary_of_four_binary_three D c dL d
    (RankTwo.not_rank_two_of_binary_three D c dL)

/-- Apply the full containing-carrier catalogue to a literal reduced section
of dimension at least six. All carriers except J₄ are discharged, including
fixed-vector and nonsplit extensions of the natural-plus-dual module. -/
theorem center_quotient_janko_four_of_large_binary_three_section
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I)
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) L W}
    (d : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)) ρ)
    (h64 : 64 ≤ Nat.card W) : Nonempty ((I ⧸ center I) ≃* Janko4.Model) :=
  Other.remaining_janko_four_of_large_binary_three_section D c d h64 dL
    (RankTwo.not_rank_two_of_binary_three D c dL)

/-- The source natural-plus-dual binary-three row leaves only J₄. The
section uses the original two-core quotient map and retains its fixed kernel. -/
theorem center_quotient_janko_four_of_natural_dual_binary_three
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I)
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (d : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
      (((Representation.specialLinearNatural (k := ZMod 2) 3).prod
        (Representation.specialLinearNatural 3).dual).comp
          (dL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    Nonempty ((I ⧸ center I) ≃* Janko4.Model) := by
  apply center_quotient_janko_four_of_large_binary_three_section D c dL d
  have hd : Nat.card (Module.Dual (ZMod 2) (Fin 3 → ZMod 2)) = 8 := by
    rw [Nat.card_congr (Pi.basisFun (ZMod 2) (Fin 3)).dualBasis.equivFun.toEquiv,
      Nat.card_fun,Nat.card_fin,Nat.card_zmod]
    decide
  simp only [Nat.card_prod,Nat.card_fun,Nat.card_fin,Nat.card_zmod,hd]
  decide

/-- The full natural-plus-dual binary-three row is impossible. The last
J₄ comparison uses the literal coordinates through the original central
quotient, retaining the fixed kernel and nonsplit extensions. -/
theorem quasisimple_impossible_of_natural_dual_binary_three
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I)
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (d : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
      (((Representation.specialLinearNatural (k := ZMod 2) 3).prod
        (Representation.specialLinearNatural 3).dual).comp
          (dL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) : False := by
  obtain ⟨e⟩ := center_quotient_janko_four_of_natural_dual_binary_three D c dL d
  exact Other.not_jankoFour_of_natural_dual D c dL d e

/-- The last M₂₃ comparison completes every literal irreducible binary-three
section of order at least eight, retaining its full fixed kernel. -/
theorem quasisimple_impossible_of_large_irreducible_binary_three
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I)
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) L W} [ρ.IsIrreducible]
    (d : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)) ρ)
    (hc : 8 ≤ Nat.card W) : False := by
  obtain ⟨e⟩ := center_quotient_mathieuTwentyThree_of_large_irreducible_binary_three D c dL d hc
  exact Other.not_mathieuTwentyThree_of_binary_three D c dL e

/-- All containing carriers are excluded for the actual natural section,
with no splitting or zero-fixed-kernel assumption. -/
theorem quasisimple_impossible_of_natural_binary_three
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I)
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (d : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
      ((Representation.specialLinearNatural (k := ZMod 2) 3).comp
        (dL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) : False := by
  obtain ⟨e⟩ := center_quotient_mathieuTwentyThree_of_natural_binary_three D c dL d
  exact Other.not_mathieuTwentyThree_of_binary_three D c dL e

/-- The dual natural row is excluded with the same literal quotient map
and the whole original fixed kernel. -/
theorem quasisimple_impossible_of_dual_binary_three
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I)
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (d : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
      ((Representation.specialLinearNatural (k := ZMod 2) 3).dual.comp
        (dL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) : False := by
  obtain ⟨e⟩ := center_quotient_mathieuTwentyThree_of_dual_binary_three D c dL d
  exact Other.not_mathieuTwentyThree_of_binary_three D c dL e


/-- The existing common-centralizer contradiction on the literal escaping
component, independent of its family and of any A₅ isomorphism. -/
theorem common_centralizer_impossible
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
    (hc : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (I : Set G)) : False :=
  source_a5_point_component_common_centralizer_impossible D c.t_mem c.moved_normalizer I c.escapes hc

/-- The two source inspections exhaust the quasisimple branch. The endpoint
proofs discharge all scalar, residual and normalizer premises here. -/
theorem quasisimpleExclusion_of_inspections
    (hrank : RankTwoInspectionAt T) (hother : OtherInspectionAt T) :
    QuasisimpleExclusionAt T := by
  intro hmany L D hminimal ha t v I c hI
  let := hI
  by_cases hm : ∃ n, ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) n
  · rcases hrank hmany L D hminimal ha t v I c hI hm with hc | hs
    · exact common_centralizer_impossible D c hc
    · obtain ⟨F,hfield,hfinite,n,hF,hn,eI,hmark⟩ := hs
      let := hfield
      let := hfinite
      exact symplectic_marking_impossible D c hF hn eI hmark
  · exact common_centralizer_impossible D c
      (hother hmany L D hminimal ha t v I c hI (center_quotient_model D c) hm)

/-- Actual consumer: discharge the quasisimple argument of the original
point-control assembly. The other three source branches keep their owners. -/
theorem pointControl_of_inspections
    (hhalf : HalfSylowUniqueAt T) (hselect : SelectionAt T)
    (hrank : RankTwoInspectionAt T) (hother : OtherInspectionAt T)
    (hconstrained : ConstrainedExclusionAt T) : SourceNonnormalPointControlAt T :=
  source_nonnormalPointControl_of_sourceSteps hhalf hselect
    (quasisimpleExclusion_of_inspections hrank hother) hconstrained

end CFSG.Quasithin.Chapter10.PointControl.Quasisimple
