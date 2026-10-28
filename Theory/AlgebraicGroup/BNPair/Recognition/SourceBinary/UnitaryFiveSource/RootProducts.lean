module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.RootCommutators
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.Collection

/-!+# Four-root coordinates in the actual quadrangle

The ordered roots in a quadrangle are A, D, C, B, where C and D are
the crossed copies of the two simple roots. Thus any faithful full charts
on these four subgroups give unique coordinates on the entire source U.
The radical containments also give the three commuting crossing laws.
No polynomial formula for the other crossings is inferred from collection.

Source: Fong--Seitz I (3G), (6A)(c); II (8C), pp.202--210;
Carter 2.5.10--2.5.17 for ordered positive products.
-/

public noncomputable section
open Subgroup
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
open RootCoordinates HexagonStructure QuadrangleStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem ordered_three (hm : rotationOrder Q = 4) (b : Bool) :
    orderedRoots Q split b 3 =
      [simpleRoot Q split (if b then 1 else 0),
       rootAt Q split (if b then 0 else 1) (Q.simple (if b then 1 else 0)),
       rootAt Q split (if b then 1 else 0) (Q.simple (if b then 0 else 1))] := by
  cases b <;> simp only [orderedRoots, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    ite_false, ite_true, List.map_cons, List.map_nil]
  · change [simpleRoot Q split 0, rootAt Q split 1 (Q.simple 0),
      rightConjugate (rootAt Q split 0 (Q.simple 1)) (representative (Q.simple 0) : X ⧸ Q.D)] = _
    rw [cross_root_reflection_fixed Q split hm 0 1 (by decide) _ (representative_spec _)]
  · change [simpleRoot Q split 1, rootAt Q split 0 (Q.simple 1),
      rightConjugate (rootAt Q split 1 (Q.simple 0)) (representative (Q.simple 1) : X ⧸ Q.D)] = _
    rw [cross_root_reflection_fixed Q split hm 1 0 (by decide) _ (representative_spec _)]

/-- The actual longest-word ordering, in either endpoint orientation. -/
theorem ordered_four (hm : rotationOrder Q = 4) (i : Fin 2) :
    orderedRoots Q split (decide (i = 1)) (rotationOrder Q) =
      [simpleRoot Q split i, rootAt Q split (1-i) (Q.simple i),
       rootAt Q split i (Q.simple (1-i)), simpleRoot Q split (1-i)] := by
  rw [hm]
  have hsq (j : Fin 2) : Q.simple j * Q.simple j = 1 := by
    simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem j)).2
  fin_cases i
  · change simpleRoot Q split 0 ::
      (orderedRoots Q split true 3).map
        (fun A => rightConjugate A (representative (Q.simple 0) : X ⧸ Q.D)) = _
    rw [ordered_three Q split hm true]
    simp only [ite_true, List.map_cons, List.map_nil]
    change [simpleRoot Q split 0, rootAt Q split 1 (Q.simple 0),
      rightConjugate (rootAt Q split 0 (Q.simple 1)) (representative (Q.simple 0) : X ⧸ Q.D),
      rightConjugate (rootAt Q split 1 (Q.simple 0)) (representative (Q.simple 0) : X ⧸ Q.D)] = _
    rw [cross_root_reflection_fixed Q split hm 0 1 (by decide) _ (representative_spec _),
      rootAt_right Q split 1 (Q.simple 0) (Q.simple 0) _ (representative_spec _), hsq,
      rootAt_one]
    rfl
  · change simpleRoot Q split 1 ::
      (orderedRoots Q split false 3).map
        (fun A => rightConjugate A (representative (Q.simple 1) : X ⧸ Q.D)) = _
    rw [ordered_three Q split hm false]
    simp only [Bool.false_eq_true, ite_false, List.map_cons, List.map_nil]
    change [simpleRoot Q split 1, rootAt Q split 0 (Q.simple 1),
      rightConjugate (rootAt Q split 1 (Q.simple 0)) (representative (Q.simple 1) : X ⧸ Q.D),
      rightConjugate (rootAt Q split 0 (Q.simple 1)) (representative (Q.simple 1) : X ⧸ Q.D)] = _
    rw [cross_root_reflection_fixed Q split hm 1 0 (by decide) _ (representative_spec _),
      rootAt_right Q split 0 (Q.simple 1) (Q.simple 1) _ (representative_spec _), hsq,
      rootAt_one]
    rfl

section Products
variable {RA RD RC RB : Type*} [Group RA] [Group RD] [Group RC] [Group RB]
  (r : PositiveMaps (X ⧸ Q.D) RA RD RC RB)

/-- A single tuple records the ordered A,D,C,B word. -/
@[expose] def chartWord (p : RA × RD × RC × RB) : X ⧸ Q.D :=
  r.word p.1 p.2.1 p.2.2.1 p.2.2.2

private def chartTuple (p : RA × RD × RC × RB) :
    RootTuple [r.A.range,r.D.range,r.C.range,r.B.range] :=
  (r.A.rangeRestrict p.1,r.D.rangeRestrict p.2.1,
    r.C.rangeRestrict p.2.2.1,r.B.rangeRestrict p.2.2.2,PUnit.unit)

private theorem chartTuple_product (p : RA × RD × RC × RB) :
    rootProduct [r.A.range,r.D.range,r.C.range,r.B.range] (chartTuple Q r p) =
      chartWord Q r p := by
  simp only [chartTuple, rootProduct, chartWord, PositiveMaps.word,
    MonoidHom.coe_rangeRestrict, mul_one, mul_assoc]

private theorem chartTuple_surjective : Function.Surjective (chartTuple Q r) := by
  rintro ⟨a,d,c,b,u⟩
  obtain ⟨a',ha⟩ := r.A.rangeRestrict_surjective a
  obtain ⟨d',hd⟩ := r.D.rangeRestrict_surjective d
  obtain ⟨c',hc⟩ := r.C.rangeRestrict_surjective c
  obtain ⟨b',hb⟩ := r.B.rangeRestrict_surjective b
  cases u
  exact ⟨(a',d',c',b'),by simp only [chartTuple,ha,hd,hc,hb]; rfl⟩

variable (b : Bool)
  (hroots : orderedRoots Q split b (rotationOrder Q) =
    [r.A.range,r.D.range,r.C.range,r.B.range])

include hroots

/-- Existence of source coordinates uses the actual ordered-root factorization. -/
theorem chartWord_range : Set.range (chartWord Q r) = (split.U : Set (X ⧸ Q.D)) := by
  have ht : Set.range (chartWord Q r) =
      Set.range (rootProduct [r.A.range,r.D.range,r.C.range,r.B.range]) := by
    ext x
    constructor
    · rintro ⟨p,rfl⟩
      exact ⟨chartTuple Q r p,chartTuple_product Q r p⟩
    · rintro ⟨p,rfl⟩
      obtain ⟨q,rfl⟩ := chartTuple_surjective Q r p
      exact ⟨q,(chartTuple_product Q r q).symm⟩
  rw [ht,←hroots,rootProduct_range,unipotent_ordered_product]

/-- Unique source coordinates require faithfulness of each full root chart. -/
theorem chartWord_injective
    (hA : Function.Injective r.A) (hD : Function.Injective r.D)
    (hC : Function.Injective r.C) (hB : Function.Injective r.B) :
    Function.Injective (chartWord Q r) := by
  have hi : Function.Injective (rootProduct (orderedRoots Q split b (rotationOrder Q))) := by
    intro p q hpq
    apply (unipotentOrderedCoordinates Q split b).injective
    apply Subtype.ext
    simpa only [unipotentOrderedCoordinates_apply] using hpq
  rw [hroots] at hi
  intro p q hpq
  have ht : chartTuple Q r p = chartTuple Q r q := hi (by
    simpa only [chartTuple_product] using hpq)
  apply Prod.ext
  · exact hA (congrArg (fun z : RootTuple [r.A.range,r.D.range,r.C.range,r.B.range] =>
      (z.1 : X ⧸ Q.D)) ht)
  · apply Prod.ext
    · exact hD (congrArg (fun z : RootTuple [r.A.range,r.D.range,r.C.range,r.B.range] =>
        (z.2.1 : X ⧸ Q.D)) ht)
    · apply Prod.ext
      · exact hC (congrArg (fun z : RootTuple [r.A.range,r.D.range,r.C.range,r.B.range] =>
          (z.2.2.1 : X ⧸ Q.D)) ht)
      · exact hB (congrArg (fun z : RootTuple [r.A.range,r.D.range,r.C.range,r.B.range] =>
          (z.2.2.2.1 : X ⧸ Q.D)) ht)

/-- The constructed chart ranges generate exactly the source unipotent subgroup. -/
theorem charts_generated : r.generated = split.U := by
  apply le_antisymm
  · apply (closure_le _).2
    have hle (A : Subgroup (X ⧸ Q.D)) (hA : A ∈
        [r.A.range,r.D.range,r.C.range,r.B.range]) : A ≤ split.U := by
      rw [←hroots] at hA
      have he := orderedRoots_le Q split b _ le_rfl A hA
      simpa only [alternatingWord_longest,longest_inv,rootIntersection_longest] using he
    rintro z (((ha | hd) | hc) | hb)
    · exact hle r.A.range (by simp) ha
    · exact hle r.D.range (by simp) hd
    · exact hle r.C.range (by simp) hc
    · exact hle r.B.range (by simp) hb
  · intro z hz
    have hz' : z ∈ Set.range (chartWord Q r) := by
      rw [chartWord_range Q split r b hroots]
      exact hz
    obtain ⟨p,rfl⟩ := hz'
    exact r.word_mem _ _ _ _

end Products
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
