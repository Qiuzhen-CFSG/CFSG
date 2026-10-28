module

public import Theory.Mathieu.M12.ExceptionalParabolics.SecondCore
public import CFSG.Quasithin.ChapterF.Section01.SourceDefs
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.M12.Aut

/-!
# The concrete M₁₂ alternative in F.1.12

The marked local groups are the actual involution centralizer and natural-four
normalizer in the Witt-design M₁₂. Their Sylow normalizers identify the source
Borel B₁B₂S with their whole intersection S, giving the full inclusion amalgam.
Both quotients are PSL₂(2), the first two-core is Q₈ * Q₈, and the second
two-core has order 32. Thus the first denominator and first core in the
printed case (12) refer to L₁, not L₂. The second core has center of order
at least four and is not normal in the first parabolic, so both printed
assignments fail for that denominator.

The model predicate below means isomorphism of the three inclusion maps,
including both commuting squares. Local structure is a consequence of that
predicate; no converse or uniqueness is asserted. The imported `M12.Aut`
constructs the full Aut(M₁₂) amalgam and exports its corrected marked core
calculations, with the ambient automorphism identification and coordinate
comparison proved.

Source: Aschbacher--Smith, F.1.12(I)(12)--(13), printed p.263 (PDF p.274),
Notation E.2.16, printed p.228, and 14.2.21, printed p.988.
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.ChapterF.GreenBook.MathieuTwelve
open Theory.GroupTheory Sporadic.Mathieu Sporadic.Mathieu.M12SmallPair
open scoped Pointwise

/-- The source L₁,L₂, with L₁ centralizing the distinguished involution. -/
def L : Fin 2 → Subgroup M12 := ![firstParabolic, secondParabolic]

/-- The actual common Sylow two-subgroup. -/
def S : Sylow 2 M12 := commonSylow

/-- The source's entire B₁B₂S, prior to simplifying either local normalizer. -/
def B : Subgroup M12 := Source.commonBorel L (S : Subgroup M12)

/-- The full source parabolic LᵢB. -/
def P (i : Fin 2) : Subgroup M12 := L i ⊔ B

theorem S_le_L (i : Fin 2) : (S : Subgroup M12) ≤ L i := by
  fin_cases i
  · exact inf_le_left
  · exact inf_le_right

theorem local_borel (i : Fin 2) : Source.borel (L i) (S : Subgroup M12) = S := by
  rw [Source.borel, inf_eq_left.mpr (S_le_L i)]
  fin_cases i
  · exact ExceptionalParabolics.first_sylow_normalizer
  · exact ExceptionalParabolics.second_sylow_normalizer

theorem B_eq_S : B = (S : Subgroup M12) := by
  rw [B, Source.commonBorel, local_borel, local_borel, sup_idem, sup_idem]

theorem B_le_L (i : Fin 2) : B ≤ L i := B_eq_S ▸ S_le_L i

theorem P_eq_L (i : Fin 2) : P i = L i := sup_eq_left.mpr (B_le_L i)

theorem borel_normalizes (i : Fin 2) : B ≤ Subgroup.normalizer (L i : Set M12) :=
  (B_le_L i).trans (L i).le_normalizer

theorem P_coe_eq_product (i : Fin 2) :
    (P i : Set M12) = (L i : Set M12) * (B : Set M12) :=
  Subgroup.coe_mul_of_right_le_normalizer_left _ _ (borel_normalizes i)

theorem overlap : P 0 ⊓ P 1 = B := by
  rw [P_eq_L, P_eq_L, B_eq_S]
  rfl

theorem generated : L 0 ⊔ L 1 ⊔ (S : Subgroup M12) = ⊤ := by
  change firstParabolic ⊔ secondParabolic ⊔ (S : Subgroup M12) = ⊤
  rw [ValueBoundParabolics.parabolic_sup_eq_top, top_sup_eq]

theorem P_generate : P 0 ⊔ P 1 = ⊤ := by
  rw [P_eq_L, P_eq_L]
  exact ValueBoundParabolics.parabolic_sup_eq_top

/-- The full source inclusion amalgam, with the literal B₁B₂S as middle group. -/
def amalgam : RankTwoAmalgam (P 0) B (P 1) :=
  RankTwoAmalgam.ofSubgroups _ _ _ le_sup_right le_sup_right

/-- Its identification with the checked intrinsic pair preserves both inclusions. -/
def concreteIso : RankTwoAmalgam.Iso amalgam ExceptionalParabolics.amalgam :=
  RankTwoAmalgam.ofSubgroupsIso (MulEquiv.refl M12)
    le_sup_right le_sup_right inf_le_left inf_le_right
    (by simpa [P, L] using P_eq_L 0)
    (by simpa [S, sylowCandidate] using B_eq_S)
    (by simpa [P, L] using P_eq_L 1)

theorem left_injective : Function.Injective amalgam.left :=
  Subgroup.inclusion_injective le_sup_right

theorem right_injective : Function.Injective amalgam.right :=
  Subgroup.inclusion_injective le_sup_right

/-- The corrected four local assertions on the actual marked M₁₂ subgroups. -/
theorem local_calculations :
    ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 2 ∧
    Nonempty (Subgroup.QuaternionCentralProductData (pCore 2 (L 0))) ∧
    ClassicalGroup.IsPSL (L 1 ⧸ pCore 2 (L 1)) 2 2 ∧
    Nat.card (pCore 2 (L 1)) = 32 := by
  refine ⟨?_, ⟨ExceptionalParabolics.firstCoreQuaternionData⟩, ?_,
    ExceptionalParabolics.secondCore_card⟩
  · exact ⟨ZMod 2, inferInstance, inferInstance, by simp,
      ⟨ExceptionalParabolics.firstPSLQuotient⟩⟩
  · exact ⟨ZMod 2, inferInstance, inferInstance, by simp,
      ⟨ExceptionalParabolics.secondPSLQuotient⟩⟩

variable {G₁ D G₂ : Type*} [Group G₁] [Group D] [Group G₂]

/-- A model-indexed predicate for the separate amalgam recognition theorem. -/
def IsM12Amalgam (α : RankTwoAmalgam G₁ D G₂) : Prop :=
  Nonempty (RankTwoAmalgam.Iso α amalgam)

/-- Local invariants alone are not an assertion of amalgam uniqueness. -/
def M12LocalStructure (_α : RankTwoAmalgam G₁ D G₂) : Prop :=
  ClassicalGroup.IsPSL (G₁ ⧸ pCore 2 G₁) 2 2 ∧
  Nonempty (Subgroup.QuaternionCentralProductData (pCore 2 G₁)) ∧
  ClassicalGroup.IsPSL (G₂ ⧸ pCore 2 G₂) 2 2 ∧
  Nat.card (pCore 2 G₂) = 32

/-- Transport the calculated invariants through an actual amalgam isomorphism. -/
theorem localStructure_of_isM12Amalgam {α : RankTwoAmalgam G₁ D G₂}
    (h : IsM12Amalgam α) : M12LocalStructure α := by
  obtain ⟨e⟩ := h
  let f := e.trans concreteIso
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨ZMod 2, inferInstance, inferInstance, by simp,
      ⟨(LocalCoreTransport.quotientEquiv 2 f.left).trans
        ExceptionalParabolics.firstPSLQuotient⟩⟩
  · exact ⟨ExceptionalParabolics.firstCoreQuaternionData.map
      (LocalCoreTransport.coreEquiv 2 f.left).symm⟩
  · exact ⟨ZMod 2, inferInstance, inferInstance, by simp,
      ⟨(LocalCoreTransport.quotientEquiv 2 f.right).trans
        ExceptionalParabolics.secondPSLQuotient⟩⟩
  · rw [LocalCoreTransport.core_card 2 f.right, ExceptionalParabolics.secondCore_card]

end CFSG.Quasithin.ChapterF.GreenBook.MathieuTwelve
