module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.SimpleCoordinates
public import Theory.SpecificGroups.G2.RootPresentationRecognition.Positive

/-!
# The six actual source G₂ root carriers and positive generation

Starting with the canonical simple roots in the same marked quotient,
transport their additive field coordinates along the specified source
reflections. In the presentation order the carriers are
A = U_long^(s r), B = U_long^s, C = U_short^(r s),
D = U_short^r, E = U_long, F = U_short, using right conjugation.
The existing five-root radical factorization proves that any full
parametrizations of these six carriers generate the specified U.

Every constructed root map is injective, so A(1) is nontrivial, including
for q=2. The same chosen source reflections lie in the specified endpoints;
both orientations are retained. No mixed relation, compatible SL₂ pinning,
or polynomial table is assumed or concluded. The initial field labelings
still require the coupled module alignment of Fong--Seitz II (9.9)--(9.15).

Source: Fong--Seitz I (3G), (5C), (6E)(a), printed pp.14--16, 25--28, 43;
II (9.12)--(9.16), printed pp.215--216, for the literal root ordering.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open RootCoordinates HexagonStructure Atlas.G2.RootPresentationRecognition
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The six source subgroups, in the presentation's A,B,C,D,E,F order. -/
def positiveCarrier (short : Fin 2) : Fin 6 → Subgroup (X ⧸ Q.D) :=
  let long := 1 - short
  ![rootAt Q split long (Q.simple short * Q.simple long),
    rootAt Q split long (Q.simple short),
    rootAt Q split short (Q.simple long * Q.simple short),
    rootAt Q split short (Q.simple long),
    simpleRoot Q split long, simpleRoot Q split short]

private theorem short_ne_long (short : Fin 2) : short ≠ 1-short := by
  fin_cases short <;> decide

/-- Every root in this A--F list lies in the specified U. -/
theorem positiveCarrier_le (hm : rotationOrder Q = 6) (short : Fin 2) (k : Fin 6) :
    positiveCarrier Q split short k ≤ split.U := by
  have h := (middleRoots_le_remainder Q split hm short (1-short) (short_ne_long short)).trans
    (show simpleRemainder Q split (1-short) ≤ split.U from inf_le_left)
  have h' := (middleRoots_le_remainder Q split hm (1-short) short (short_ne_long short).symm).trans
    (show simpleRemainder Q split short ≤ split.U from inf_le_left)
  fin_cases k
  · exact (show _ ≤ middleRoots Q split short (1-short) from le_sup_right).trans h
  · exact (show _ ≤ middleRoots Q split short (1-short) from le_sup_left.trans le_sup_left).trans h
  · exact (show _ ≤ middleRoots Q split short (1-short) from le_sup_right.trans le_sup_left).trans h
  · exact (show _ ≤ middleRoots Q split (1-short) short from le_sup_left.trans le_sup_left).trans h'
  · exact simpleRoot_le Q split _
  · exact simpleRoot_le Q split _

omit [Finite F] [CharP F 2] in
/-- Any full parametrizations of these actual six roots generate exactly U.
No commutator relation or compatibility of their field labels is needed. -/
theorem positive_generated_of_ranges (hm : rotationOrder Q = 6) (short : Fin 2)
    (roots : PositiveRoots F (X ⧸ Q.D))
    (hr : ∀ k, (roots.root k).range = positiveCarrier Q split short k) :
    roots.generated = split.U := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨⟨k,a⟩,rfl⟩
    exact positiveCarrier_le Q split hm short k ((hr k) ▸ ⟨Multiplicative.ofAdd a,rfl⟩)
  · have hgen (k : Fin 6) : positiveCarrier Q split short k ≤ roots.generated := by
      rw [← hr k]
      rintro x ⟨a,rfl⟩
      exact roots.root_mem_generated k a.toAdd
    intro x hx
    have hu : x ∈ (simpleRoot Q split (1-short) : Set (X ⧸ Q.D)) *
        (simpleRemainder Q split (1-short) : Set (X ⧸ Q.D)) := by
      rw [simpleRoot_mul_remainder]
      exact hx
    obtain ⟨e,he,v,hv,rfl⟩ := hu
    rw [radical_five_product Q split hm short (1-short) (short_ne_long short)] at hv
    obtain ⟨fbca,⟨fbc,⟨fb,⟨f,hf,b,hb,rfl⟩,c,hc,rfl⟩,a,ha,rfl⟩,d,hd,rfl⟩ := hv
    exact roots.generated.mul_mem (hgen 4 he)
      (roots.generated.mul_mem
        (roots.generated.mul_mem (roots.generated.mul_mem
          (roots.generated.mul_mem (hgen 5 hf) (hgen 1 hb)) (hgen 2 hc)) (hgen 0 ha))
        (hgen 3 hd))

variable (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i) (short : Fin 2)

/-- Initial field coordinates transported along the two specified source lifts.
The two complete rank-one labelings still need alignment for mixed equations. -/
def sourceRoots : PositiveRoots F (X ⧸ Q.D) where
  root :=
    let long := 1-short
    ![conjugateParameter Q split long (hK long) (μ long) ((n short).val * (n long).val),
      conjugateParameter Q split long (hK long) (μ long) (n short).val,
      conjugateParameter Q split short (hK short) (μ short) ((n long).val * (n short).val),
      conjugateParameter Q split short (hK short) (μ short) (n long).val,
      simpleParameter Q split long (hK long) (μ long),
      simpleParameter Q split short (hK short) (μ short)]

theorem sourceRoots_range (k : Fin 6) :
    ((sourceRoots Q split hK μ n short).root k).range = positiveCarrier Q split short k := by
  have hprod (i j : Fin 2) :
      QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N)
        ((n i).val*(n j).val) = Q.simple i*Q.simple j := by
    rw [map_mul, (n i).class_eq, (n j).class_eq]
  fin_cases k
  · exact conjugateParameter_range Q split _ _ _ _ _ (hprod _ _)
  · exact conjugateParameter_range Q split _ _ _ _ _ (n short).class_eq
  · exact conjugateParameter_range Q split _ _ _ _ _ (hprod _ _)
  · exact conjugateParameter_range Q split _ _ _ _ _ (n (1-short)).class_eq
  · exact simpleParameter_range Q split _ _ _
  · exact simpleParameter_range Q split _ _ _

theorem sourceRoots_injective (k : Fin 6) :
    Function.Injective ((sourceRoots Q split hK μ n short).root k) := by
  fin_cases k
  · exact conjugateParameter_injective Q split _ _ _ _
  · exact conjugateParameter_injective Q split _ _ _ _
  · exact conjugateParameter_injective Q split _ _ _ _
  · exact conjugateParameter_injective Q split _ _ _ _
  · exact simpleParameter_injective Q split _ _ _
  · exact simpleParameter_injective Q split _ _ _

theorem sourceRoots_generated (hm : rotationOrder Q = 6) :
    (sourceRoots Q split hK μ n short).generated = split.U :=
  positive_generated_of_ranges Q split hm short _ (sourceRoots_range Q split hK μ n short)

/-- The highest root is nontrivial over every characteristic-two field. -/
theorem sourceRoots_highest_nontrivial :
    (sourceRoots Q split hK μ n short).x 0 1 ≠ 1 := by
  intro h
  have he : (sourceRoots Q split hK μ n short).root 0 (Multiplicative.ofAdd 1) =
      (sourceRoots Q split hK μ n short).root 0 (Multiplicative.ofAdd 0) := by
    simpa only [PositiveRoots.x_zero] using h
  have hs : (1 : F) = 0 := Multiplicative.ofAdd.injective
    (sourceRoots_injective Q split hK μ n short 0 he)
  exact one_ne_zero hs

/-- The same source lifts lie in the two specified endpoints. -/
theorem sourceReflection_placements :
    ((n short).val : X ⧸ Q.D) ∈ Q.tits.standardParabolic {Q.simple short} ∧
    ((n (1-short)).val : X ⧸ Q.D) ∈ Q.tits.standardParabolic {Q.simple (1-short)} :=
  ⟨rankOne_le_parabolic Q split short (n short).mem_rankOne,
    rankOne_le_parabolic Q split (1-short) (n (1-short)).mem_rankOne⟩

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
