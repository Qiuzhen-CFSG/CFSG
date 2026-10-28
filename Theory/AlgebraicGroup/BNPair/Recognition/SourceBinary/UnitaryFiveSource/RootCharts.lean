module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.RootProducts
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.UnitaryRootDerived
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FivePositive
public import Mathlib.FieldTheory.Finite.GaloisField

/-!+# Full source root charts for the unitary quadrangle

The actual panel markings identify the two simple roots with the additive
matrix field and the entire nonabelian Hermitian group. Transport by the
specified source Weyl lifts supplies the other two roots. Their ordered
product is a bijection onto U, and three of the six crossing laws follow
from the source radical containments.

Equal field orders allow these initial charts to use one matrix field.
This choice does not yet synchronize the two actors' module actions:
the remaining noncommuting laws and Cartan pinning still require that work.
The five-dimensional identity form uses exactly the given involution;
its Hermitian parameter group is the same as for the given three-form.

Source: Fong--Seitz I (5C), (6A)(c); II (8C), pp.202--210.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
open scoped MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
open RootCoordinates HexagonStructure QuadrangleStructure

variable {K E : Type*} [Field K] [Finite K] [CharP K 2]
  [Field E] [Finite E] [CharP E 2]

/-- Initial field labels; compatibility with the two actions is a later obligation. -/
def fieldLabels (hcard : Nat.card E = Nat.card K) : E ≃+* K := by
  letI := Fintype.ofFinite E
  letI := Fintype.ofFinite K
  exact FiniteField.ringEquivOfCardEq (by simpa only [Nat.card_eq_fintype_card] using hcard)

/-- The presentation form retains the literal source field involution. -/
abbrev fiveForm (J : HermitianForm 3 E) : HermitianForm 5 E :=
  Theory.SpecificGroups.UnitaryFive.identityForm J.conj J.conj_involutive

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
  (hK : Nat.card K = (2^n)^2) (hE : Nat.card E = (2^n)^2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (i : Fin 2)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split (1-i) ≤ localKernel Q (1-i))
  (μ : localGroup Q split i ≃* PSL(2,K))
  (ν : localGroup Q split (1-i) ≃* ProjectiveSpecialUnitaryMatrixGroup J)

/-- The linear simple root, on the common matrix field. -/
def linearChart : Multiplicative E ≃* simpleRoot Q split i :=
  (AddEquiv.toMultiplicative (fieldLabels (hE.trans hK.symm)).toAddEquiv).trans
    (GTwoSource.simpleRootFieldEquiv Q split i hVi μ)

/-- Full Hermitian coordinates on the actual simple root, also at q=2. -/
def hermitianChart : FivePositive.Parameter (fiveForm J) ≃* simpleRoot Q split (1-i) :=
  (simpleRootUnitaryEquiv J Q split hn hE hfixed hJ (1-i) hVj ν).symm

variable (s t : Q.tits.N)

/-- Four actual homomorphisms, using right conjugation by the source lifts. -/
def rootCharts : PositiveMaps (X ⧸ Q.D) (Multiplicative E)
    (FivePositive.Parameter (fiveForm J)) (Multiplicative E)
    (FivePositive.Parameter (fiveForm J)) :=
  let a := (simpleRoot Q split i).subtype.comp
    (linearChart Q split hK hE i hVi μ).toMonoidHom
  let b := (simpleRoot Q split (1-i)).subtype.comp
    (hermitianChart Q split J hn hE hfixed hJ i hVj ν).toMonoidHom
  ⟨a,(MulAut.conj (s : X ⧸ Q.D)⁻¹).toMonoidHom.comp b,
    (MulAut.conj (t : X ⧸ Q.D)⁻¹).toMonoidHom.comp a,b⟩

local notation "r" => rootCharts Q split J hn hK hE hfixed hJ i hVi hVj μ ν s t

omit [CharP E 2]

theorem rootCharts_injective : Function.Injective (r).A ∧ Function.Injective (r).D ∧
    Function.Injective (r).C ∧ Function.Injective (r).B := by
  have ha := Subtype.val_injective.comp (linearChart Q split hK hE i hVi μ).injective
  have hb := Subtype.val_injective.comp
    (hermitianChart Q split J hn hE hfixed hJ i hVj ν).injective
  exact ⟨ha,(MulAut.conj (s : X ⧸ Q.D)⁻¹).injective.comp hb,
    (MulAut.conj (t : X ⧸ Q.D)⁻¹).injective.comp ha,hb⟩

theorem rootCharts_simple_ranges : (r).A.range = simpleRoot Q split i ∧
    (r).B.range = simpleRoot Q split (1-i) := by
  constructor
  · change ((simpleRoot Q split i).subtype.comp
      (linearChart Q split hK hE i hVi μ).toMonoidHom).range = _
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr
      (linearChart Q split hK hE i hVi μ).surjective,←MonoidHom.range_eq_map,range_subtype]
  · change ((simpleRoot Q split (1-i)).subtype.comp
      (hermitianChart Q split J hn hE hfixed hJ i hVj ν).toMonoidHom).range = _
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr
      (hermitianChart Q split J hn hE hfixed hJ i hVj ν).surjective,
      ←MonoidHom.range_eq_map,range_subtype]

private theorem commute_of_roots {A B : Subgroup (X ⧸ Q.D)}
    (hc : ⁅A,B⁆ = ⊥) {a b : X ⧸ Q.D} (ha : a ∈ A) (hb : b ∈ B) : Commute a b :=
  (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc ha) b hb).symm

variable (hs : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) s = Q.simple i)
  (ht : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) t = Q.simple (1-i))

include hs ht

/-- Both crossed root ranges are literal source Weyl conjugates. -/
theorem rootCharts_cross_ranges : (r).D.range = rootAt Q split (1-i) (Q.simple i) ∧
    (r).C.range = rootAt Q split i (Q.simple (1-i)) := by
  obtain ⟨ha,hb⟩ := rootCharts_simple_ranges Q split J hn hK hE hfixed hJ i hVi hVj μ ν s t
  constructor
  · change ((MulAut.conj (s : X ⧸ Q.D)⁻¹).toMonoidHom.comp (r).B).range = _
    rw [MonoidHom.range_comp,hb,rootAt_eq Q split (1-i) (Q.simple i) s hs,
      rightConjugate,comap_equiv_eq_map_symm',map_inv]
    rfl
  · change ((MulAut.conj (t : X ⧸ Q.D)⁻¹).toMonoidHom.comp (r).A).range = _
    rw [MonoidHom.range_comp,ha,rootAt_eq Q split i (Q.simple (1-i)) t ht,
      rightConjugate,comap_equiv_eq_map_symm',map_inv]
    rfl

variable (hm : rotationOrder Q = 4)
include hm

/-- The four constructed charts fill the ordered source roots. -/
theorem rootCharts_ordered : orderedRoots Q split (decide (i=1)) (rotationOrder Q) =
    [(r).A.range,(r).D.range,(r).C.range,(r).B.range] := by
  obtain ⟨ha,hb⟩ := rootCharts_simple_ranges Q split J hn hK hE hfixed hJ i hVi hVj μ ν s t
  obtain ⟨hd,hc⟩ := rootCharts_cross_ranges Q split J hn hK hE hfixed hJ i hVi hVj μ ν s t hs ht
  rw [ha,hb,hc,hd]
  exact ordered_four Q split hm i

/-- A,D,C,B coordinates cover U uniquely without assuming any mixed equation. -/
theorem rootCharts_coordinates :
    Function.Injective (chartWord Q r) ∧ Set.range (chartWord Q r) =
      (split.U : Set (X ⧸ Q.D)) ∧ (r).generated = split.U := by
  have ho := rootCharts_ordered Q split J hn hK hE hfixed hJ i hVi hVj μ ν s t hs ht hm
  obtain ⟨ha,hd,hc,hb⟩ := rootCharts_injective Q split J hn hK hE hfixed hJ i hVi hVj μ ν s t
  exact ⟨chartWord_injective Q split r _ ho ha hd hc hb,
    chartWord_range Q split r _ ho,charts_generated Q split r _ ho⟩

/-- Three positive crossing laws follow from the source radical containments. -/
theorem rootCharts_commuting :
    (∀ a d, Commute ((r).A a) ((r).D d)) ∧
    (∀ c d, Commute ((r).C c) ((r).D d)) ∧
    (∀ b c, Commute ((r).B b) ((r).C c)) := by
  obtain ⟨ha,hb⟩ := rootCharts_simple_ranges Q split J hn hK hE hfixed hJ i hVi hVj μ ν s t
  obtain ⟨hd,hc⟩ := rootCharts_cross_ranges Q split J hn hK hE hfixed hJ i hVi hVj μ ν s t hs ht
  have hij : i ≠ 1-i := by fin_cases i <;> decide
  refine ⟨?_,?_,?_⟩
  · intro a d
    exact commute_of_roots Q (adjacent_roots_commute Q split hm i (1-i) hij hVi hVj)
      (ha ▸ (show (r).A a ∈ (r).A.range from ⟨a,rfl⟩))
      (hd ▸ (show (r).D d ∈ (r).D.range from ⟨d,rfl⟩))
  · intro c d
    exact commute_of_roots Q (middle_roots_commute Q split hm i (1-i) hij hVi hVj)
      (hc ▸ (show (r).C c ∈ (r).C.range from ⟨c,rfl⟩))
      (hd ▸ (show (r).D d ∈ (r).D.range from ⟨d,rfl⟩))
  · intro b c
    exact commute_of_roots Q (adjacent_roots_commute Q split hm (1-i) i hij.symm hVj hVi)
      (hb ▸ (show (r).B b ∈ (r).B.range from ⟨b,rfl⟩))
      (hc ▸ (show (r).C c ∈ (r).C.range from ⟨c,rfl⟩))

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
