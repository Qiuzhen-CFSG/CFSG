module

public import CFSG.Quasithin.ChapterF.Section01.SourceDefs
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Mathlib.Algebra.Group.Pointwise.Set.Finite

/-!
# Elementary consequences of the corrected F.1.1 hypotheses

Source: Aschbacher–Smith, printed pp.259–262, F.1.1 and F.1.10(1).
The finite local quotient and the finite Sylow subgroup make each local factor
finite; the normalization hypotheses then make the parabolics finite. The
normality criterion in F.1.10(1) follows because the Borel preserves both
factors in the displayed decomposition of S.

No maximality, solvability or intersection conclusion of F.1.3 is assumed.
-/

@[expose] public section

open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source
variable {H : Type*} [Group H]
/-- Every concrete rank-one model is finite. -/
theorem IsRankOneModel.finite (h : IsRankOneModel H) : Finite H := by
  cases h with
  | linear n hn h =>
    rcases h with ⟨F, _, _, _, ⟨e⟩⟩
    exact Finite.of_injective e e.injective
  | suzuki m h =>
    rcases h with ⟨e⟩
    exact Finite.of_injective e e.injective
  | projective_unitary n hn h =>
    rcases h with ⟨F, _, _, J, _, _, ⟨e⟩⟩
    let f : J.specialSubgroup → BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J :=
      fun x => ⟨Matrix.ProjGenLinGroup.mk x, ⟨x, x.property, rfl⟩⟩
    have : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective f (by rintro ⟨x, y, hy, rfl⟩; exact ⟨⟨y, hy⟩, rfl⟩)
    exact Finite.of_injective e e.injective
  | special_unitary n hn h =>
    rcases h with ⟨F, _, _, J, _, _, ⟨e⟩⟩
    exact Finite.of_injective e e.injective
  | dihedral h =>
    rcases h with ⟨e⟩
    exact Finite.of_injective e e.injective
variable {G : Type*} [Group G]
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- F.1.1 implies finiteness of Lᵢ even when the ambient group is infinite. -/
theorem HypothesisF11.finite_local (h : HypothesisF11 L S) (i : Fin 2) : Finite (L i) := by
  let _ := h.finite_S
  obtain ⟨T, hT⟩ := h.sylow i
  have hcoreT : pCore 2 (L i) ≤ T := pCore_isPGroup.le_sylow_of_normal T
  let f : pCore 2 (L i) → S := fun x =>
    ⟨x, (hT ▸ (show ((x : L i) : G) ∈ (T : Subgroup (L i)).map (L i).subtype from
      ⟨x, hcoreT x.property, rfl⟩)).1⟩
  have : Finite (pCore 2 (L i)) := Finite.of_injective f (by
    intro x y he; apply Subtype.ext; apply Subtype.ext; exact congrArg (fun z : S => (z : G)) he)
  have : Finite ((L i) ⧸ pCore 2 (L i)) := (h.quotient i).finite
  exact (Subgroup.finite_iff_finite_and_finiteIndex (pCore 2 (L i))).mpr
    ⟨inferInstance, Subgroup.finiteIndex_of_finite_quotient⟩

@[simp] theorem other_other (i : Fin 2) : other (other i) = i := by
  fin_cases i <;> rfl

theorem borel_le (A S : Subgroup G) : borel A S ≤ A := inf_le_left

theorem localSylow_le_borel (A S : Subgroup G) : S ⊓ A ≤ borel A S :=
  le_inf inf_le_right (S ⊓ A).le_normalizer

/-- The source expression Lᵢ S Bⱼ equals Lᵢ B. This is independent of
any yet-to-be-proved intersection statement. -/
theorem parabolic_eq_sup_commonBorel (L : Fin 2 → Subgroup G) (S : Subgroup G)
    (i : Fin 2) : parabolic L S i = L i ⊔ commonBorel L S := by
  fin_cases i
  · change L 0 ⊔ S ⊔ borel (L 1) S = L 0 ⊔ (borel (L 0) S ⊔ borel (L 1) S ⊔ S)
    apply le_antisymm
    · exact sup_le (sup_le le_sup_left (le_sup_right.trans le_sup_right))
        ((le_sup_right.trans le_sup_left).trans le_sup_right)
    · exact sup_le (le_sup_left.trans le_sup_left)
        (sup_le (sup_le ((borel_le _ _).trans (le_sup_left.trans le_sup_left)) le_sup_right)
          (le_sup_right.trans le_sup_left))
  · change L 1 ⊔ S ⊔ borel (L 0) S = L 1 ⊔ (borel (L 0) S ⊔ borel (L 1) S ⊔ S)
    apply le_antisymm
    · exact sup_le (sup_le le_sup_left (le_sup_right.trans le_sup_right))
        ((le_sup_left.trans le_sup_left).trans le_sup_right)
    · exact sup_le (le_sup_left.trans le_sup_left)
        (sup_le (sup_le le_sup_right ((borel_le _ _).trans (le_sup_left.trans le_sup_left)))
          (le_sup_right.trans le_sup_left))

/-- The two parabolics generate exactly the source group G₀. -/
theorem parabolics_generate (L : Fin 2 → Subgroup G) (S : Subgroup G) :
    parabolic L S 0 ⊔ parabolic L S 1 = generated L S := by
  rw [parabolic_eq_sup_commonBorel, parabolic_eq_sup_commonBorel]
  have hB : commonBorel L S ≤ generated L S :=
    sup_le (sup_le ((borel_le _ _).trans (le_sup_left.trans le_sup_left))
      ((borel_le _ _).trans (le_sup_right.trans le_sup_left))) le_sup_right
  apply le_antisymm
  · exact sup_le (sup_le (le_sup_left.trans le_sup_left) hB)
      (sup_le (le_sup_right.trans le_sup_left) hB)
  · exact sup_le (sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right))
      ((le_sup_right.trans le_sup_right).trans le_sup_left)

/-- S normalizes Sᵢ by F.1.1(a). -/
theorem HypothesisF11.S_normalizes_localSylow (h : HypothesisF11 L S) (i : Fin 2) :
    S ≤ Subgroup.normalizer ((S ⊓ L i : Subgroup G) : Set G) :=
  (le_inf S.le_normalizer (h.S_normalizes i)).trans
    Subgroup.inf_normalizer_le_normalizer_inf

/-- S normalizes each Bᵢ, using only F.1.1(a). -/
theorem HypothesisF11.S_normalizes_borel (h : HypothesisF11 L S) (i : Fin 2) :
    S ≤ Subgroup.normalizer (borel (L i) S : Set G) :=
  (le_inf (h.S_normalizes i)
    ((h.S_normalizes_localSylow i).trans (Subgroup.normalizer _).le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf

private theorem finite_sup_of_normalizes (A C : Subgroup G) [Finite A] [Finite C]
    (hn : C ≤ Subgroup.normalizer (A : Set G)) : Finite (A ⊔ C : Subgroup G) := by
  have hfin : ((A ⊔ C : Subgroup G) : Set G).Finite := by
    rw [Subgroup.coe_mul_of_right_le_normalizer_left A C hn]
    exact (Set.toFinite (A : Set G)).mul (Set.toFinite (C : Set G))
  exact hfin.to_subtype

/-- The local parabolics are finite; no finiteness of G or G₀ is required. -/
theorem HypothesisF11.finite_parabolic (h : HypothesisF11 L S) (i : Fin 2) :
    Finite (parabolic L S i) := by
  let _ := h.finite_S
  let _ := h.finite_local i
  let _ := h.finite_local (other i)
  have : Finite (borel (L (other i)) S) :=
    Finite.of_injective (Subgroup.inclusion (borel_le _ _)) (Subgroup.inclusion_injective _)
  have : Finite (borel (L (other i)) S ⊔ S : Subgroup G) :=
    finite_sup_of_normalizes _ _ (h.S_normalizes_borel (other i))
  have : Finite (L i ⊔ (borel (L (other i)) S ⊔ S) : Subgroup G) :=
    finite_sup_of_normalizes _ _ (sup_le (h.cross i) (h.S_normalizes i))
  simpa only [parabolic, sup_assoc, sup_comm S] using this

/-- The group-theoretic implication in F.1.10(1), without unused F.1.1 hypotheses. -/
theorem normal_of_core_decomposition (A S : Subgroup G)
    (heq : S = twoCore (A ⊔ S) ⊔ (S ⊓ A)) :
    (S.subgroupOf (S ⊔ borel A S)).Normal := by
  have hBcore : borel A S ≤ Subgroup.normalizer (twoCore (A ⊔ S) : Set G) :=
    (inf_le_left.trans le_sup_left).trans ((A ⊔ S).le_normalizer.trans
      (Subgroup.normalizer_le_normalizer_characteristic_image (A ⊔ S) (pCore 2 (A ⊔ S : Subgroup G))))
  have hBS : borel A S ≤ Subgroup.normalizer (S : Set G) := by
    apply le_trans (le_inf hBcore (show borel A S ≤ Subgroup.normalizer ((S ⊓ A : Subgroup G) : Set G) from
      inf_le_right))
    simpa only [← heq] using
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup (twoCore (A ⊔ S)) (S ⊓ A))
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le S.le_normalizer hBS)

/-- Lemma F.1.10(1), with the actual displayed source decomposition. -/
theorem lemma_F_1_10_1 (L : Fin 2 → Subgroup G) (S : Subgroup G)
    (hdecomp : ∀ i, S = twoCore (L i ⊔ S) ⊔ (S ⊓ L i)) :
    ∀ i, (S.subgroupOf (S ⊔ borel (L i) S)).Normal :=
  fun i => normal_of_core_decomposition (L i) S (hdecomp i)

/-- F.1.1(a,d) give normality of Lᵢ in its own parabolic, not in G. -/
theorem HypothesisF11.local_normal_in_parabolic (h : HypothesisF11 L S) (i : Fin 2) :
    ((L i).subgroupOf (parabolic L S i)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    (show L i ≤ parabolic L S i from le_sup_left.trans le_sup_left)).mpr
  exact sup_le (sup_le (L i).le_normalizer (h.S_normalizes i)) (h.cross i)

/-- The normality step in F.1.10(2a) follows from generation of B.
This does not yet assert that S is the two-core: the Sylow assertion in B
must also be proved before drawing that conclusion. -/
theorem normal_commonBorel_iff (L : Fin 2 → Subgroup G) (S : Subgroup G) :
    (S.subgroupOf (commonBorel L S)).Normal ↔
      ∀ i, (S.subgroupOf (S ⊔ borel (L i) S)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer
    (show S ≤ commonBorel L S from le_sup_right)]
  simp only [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
  constructor
  · intro h i
    apply sup_le S.le_normalizer
    apply le_trans _ h
    fin_cases i
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
  · intro h
    exact sup_le (sup_le (le_sup_right.trans (h 0)) (le_sup_right.trans (h 1)))
      S.le_normalizer

end CFSG.Quasithin.ChapterF.Source
