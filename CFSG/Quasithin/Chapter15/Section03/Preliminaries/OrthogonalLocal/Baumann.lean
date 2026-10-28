module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.LocalControl
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import Stellmacher.BaumannNormalizer
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.TwoLocalUniquenessControl

/-!
# Baumann normalizers and the centralizing Thompson alternative

The characteristic subgroup `C₂` of 14.1.11 and its centralizer supplement
make `N_M(C₂)` a uniqueness subgroup by A.5.7. Its ambient normalizer is
therefore contained in `M`, giving all of 15.3.3 and `N_G(T) ≤ M`.

When `J(T)` centralizes `V`, the elementary Thompson lemma puts `V` in
`Ω₁(Z(J(T)))`. Baumann heredity and Frattini in the relatively normal
centralizer `C_M(V)` give a second uniqueness subgroup, `N_M(Baum(T))`.
This controls the entire characteristic-normalizer closure `C(G,Baum(T))`.
Thus the first alternative of 15.3.5 is proved, without replacing that
closure by a centralizer. The noncentral alternative remains separate.

Finally, the local Sylow indices and `Baum(T) ≤ S` imply all four clauses
of 15.3.6, with Sylow subgroups mapped back to the actual ambient `S`.
The minimal-parabolic predicate is also proved for the actual `H*` family;
the further B.6.8 and E.2.2 descriptions remain required in final assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1121–1122, Lemmas 15.3.2(6), 15.3.3, 15.3.5(1), and 15.3.6.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03
open Subgroup Stellmacher
open ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The elementary rank in 15.3.2(1), computed from the genuine coordinates. -/
theorem NaturalOrthogonalAction.twoRank_vector {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) : ChapterB.twoRank V = 4 := by
  have hmax : V ∈ elementaryAbelianMaxSubgroups V :=
    ⟨le_rfl, d.elementary, fun _ hle _ => card_le_of_le hle⟩
  rw [ChapterB.twoRank, ← elementaryAbelianMaxSubgroups_card_eq V V hmax, d.card_vector]
  decide

/-- All of 15.3.3 from the specific characteristic subgroup and factorization
of 14.1.11, together with 14.1.12's ordering-maximality. -/
theorem lemma_15_3_3_of_chapter14
    (T : Sylow 2 G) (M : Subgroup G) (hM : IsOrderingMaximal T M)
    (C₂ : Subgroup (ChapterB.baumann (T : Subgroup G))) [C₂.Characteristic]
    (hne : C₂ ≠ ⊥)
    (hcover : OrderingLE T M (M ⊓ normalizer
      (C₂.map (ChapterB.baumann (T : Subgroup G)).subtype : Set G))) :
    Chapter4.UniqueMaximalOvergroup (M ⊓ normalizer
        (C₂.map (ChapterB.baumann (T : Subgroup G)).subtype : Set G)) M ∧
      normalizer (T : Set G) ≤ M ∧
      ∀ S : Subgroup G, ChapterB.baumann (T : Subgroup G) ≤ S → S ≤ (T : Subgroup G) →
        ChapterB.baumann (T : Subgroup G) = ChapterB.baumann S ∧
        normalizer (S : Set G) ≤ normalizer (ChapterB.baumann S : Set G) ∧
        normalizer (ChapterB.baumann S : Set G) ≤ M := by
  let B := ChapterB.baumann (T : Subgroup G)
  let C := C₂.map B.subtype
  have hNB : normalizer (T : Set G) ≤ normalizer (B : Set G) :=
    normalizer_le_normalizer_baumann _
  have hNC : normalizer (B : Set G) ≤ normalizer (C : Set G) :=
    normalizer_le_normalizer_characteristic_image B C₂
  have hTC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (T : Subgroup G).le_normalizer.trans (hNB.trans hNC)
  have hu : Chapter4.UniqueMaximalOvergroup (M ⊓ normalizer (C : Set G)) M := by
    refine ⟨hM.1.1, inf_le_left, ?_⟩
    intro N hN hle
    exact (lemma_A_5_7_1 hM (le_inf hM.1.2 hTC) inf_le_left hcover N hN).mp hle
  have hCp : IsPGroup 2 C :=
    ((T.isPGroup'.to_le (show B ≤ (T : Subgroup G) from inf_le_left)).to_subgroup C₂).map B.subtype
  have hCne : C ≠ ⊥ := fun h =>
    hne ((C₂.map_eq_bot_iff_of_injective B.subtype_injective).mp h)
  have hCM : normalizer (C : Set G) ≤ M :=
    normalizer_le_of_unique_maximalTwoLocal hu.2.2 hCp hCne inf_le_right
  refine ⟨hu, (hNB.trans hNC).trans hCM, ?_⟩
  intro S hBS hST
  have he := ChapterB.lemma_B_2_3_4 (T : Subgroup G) S hBS hST
  refine ⟨he, normalizer_le_normalizer_baumann S, ?_⟩
  rw [← he]
  exact hNC.trans hCM

private theorem orderingLE_baumann_of_centralizing
    (T : Sylow 2 G) {M : Subgroup G}
    (d : NaturalOrthogonalAction M (localModule T M)) (hTM : (T : Subgroup G) ≤ M)
    (hB : ChapterB.baumann (T : Subgroup G) =
      ChapterB.baumann ((T : Subgroup G) ⊓ centralizer (localModule T M : Set G))) :
    OrderingLE T M (M ⊓ normalizer (ChapterB.baumann (T : Subgroup G) : Set G)) := by
  let C := (centralizer (localModule T M : Set G)).subgroupOf M
  let _ : C.Normal := normal_subgroupOf_of_le_normalizer
    (d.normalizes.trans (normalizer_le_normalizer_centralizer _))
  obtain ⟨P, hP⟩ := (T.subtype hTM).exists_subgroupOf_eq_of_normal C
  let R := (P : Subgroup C).map C.subtype
  have hR : R.map M.subtype = (T : Subgroup G) ⊓ centralizer (localModule T M : Set G) := by
    rw [show R = (P : Subgroup C).map C.subtype from rfl, hP, map_map]
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨hc, c.property⟩
    · intro hx
      exact ⟨⟨⟨x, hTM hx.1⟩, hx.2⟩, hx.1, rfl⟩
  have hfr : normalizer (R : Set M) ⊔ C = ⊤ := P.normalizer_sup_eq_top
  intro m hm
  have hm' : (⟨m, hm⟩ : M) ∈ normalizer (R : Set M) ⊔ C := hfr ▸ mem_top _
  obtain ⟨n, hn, c, hc, he⟩ := mem_sup_of_normal_right.mp hm'
  have hnR : (n : G) ∈ normalizer (R.map M.subtype : Set G) :=
    R.le_normalizer_map M.subtype (mem_map_of_mem M.subtype hn)
  rw [hR] at hnR
  have hnB : (n : G) ∈ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) := by
    rw [hB]
    exact normalizer_le_normalizer_baumann _ hnR
  exact ⟨n, ⟨n.property, n.property, hnB⟩, c, ⟨c.property, hc⟩, congrArg Subtype.val he⟩

/-- The entire centralizing alternative of 15.3.5. The characteristic-normalizer
closure is the source `C(G,B)`, not a centralizer. -/
theorem lemma_15_3_5_centralizing
    (T : Sylow 2 G) {M : Subgroup G}
    (d : NaturalOrthogonalAction M (localModule T M)) (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    ⁅localModule T M, elementaryAbelianMaxJ (T : Subgroup G)⁆ = ⊥ ∧
      ChapterB.baumann (T : Subgroup G) =
        ChapterB.baumann ((T : Subgroup G) ⊓ centralizer (localModule T M : Set G)) ∧
      localModule T M ≤ ChapterB.thompsonAlpha (T : Subgroup G) ∧
      (ChapterB.baumann (T : Subgroup G)).characteristicNormalizerClosure ≤ M := by
  let _ := d.elementary
  have hVT := d.le_sylow T hM.1.2 (localModule_le T hM.1.2)
  have hVJ := Subgroup.le_centralizer_iff.mp hJ
  have hB := ChapterB.lemma_B_2_3_5 (T : Subgroup G) (localModule T M) hVT hJ
  refine ⟨commutator_eq_bot_iff_le_centralizer.mpr hVJ, hB,
    elementary_centralizer_maxJ_le_omegaCenter _ _ hVT hVJ, ?_⟩
  let B := ChapterB.baumann (T : Subgroup G)
  have hTN : (T : Subgroup G) ≤ normalizer (B : Set G) :=
    (T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _)
  have hcover := orderingLE_baumann_of_centralizing T d hM.1.2 hB
  have hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M ⊓ normalizer (B : Set G) ≤ N → N = M :=
    fun N hN hle => (lemma_A_5_7_1 hM (le_inf hM.1.2 hTN) inf_le_left hcover N hN).mp hle
  exact characteristicNormalizerClosure_le_of_unique_maximalTwoLocal hu
    (T.isPGroup'.to_le (show B ≤ (T : Subgroup G) from inf_le_left)) inf_le_right

omit [Finite G] in
/-- The minimal-parabolic part of 15.3.2(6), retaining the actual `H*` family.
The further B.6.8 and nonsolvable E.2.2 structure must be supplied in assembly. -/
theorem minimalParabolics_of_sylow_normalizer_control
    (T : Sylow 2 G) {M : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (hN : normalizer (T : Set G) ≤ M) :
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) M, ChapterB.IsMinimalParabolicOver T H :=
  fun _ hH => Chapter3.HStar.minimalParabolic T hTM hH (Or.inl hN)

/-- Both Baumann conclusions of 15.3.6 once the natural-action Thompson
calculation supplies `Baum(T) ≤ S`. -/
theorem lemma_15_3_6_baumann_of_containment
    (T : Sylow 2 G) (V₁ M : Subgroup G)
    (hB : ChapterB.baumann (T : Subgroup G) ≤ planeStabilizer T V₁)
    (hN : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ M) :
    ChapterB.baumann (T : Subgroup G) = ChapterB.baumann (planeStabilizer T V₁) ∧
      normalizer (planeStabilizer T V₁ : Set G) ≤
        normalizer (ChapterB.baumann (planeStabilizer T V₁) : Set G) ∧
      normalizer (ChapterB.baumann (planeStabilizer T V₁) : Set G) ≤ M := by
  have he := ChapterB.lemma_B_2_3_4 (T : Subgroup G) (planeStabilizer T V₁) hB inf_le_left
  refine ⟨he, normalizer_le_normalizer_baumann _, ?_⟩
  rwa [← he]

/-- The centralizing case also puts the Baumann subgroup in either plane stabilizer. -/
theorem baumann_le_planeStabilizer_of_centralizing
    (T : Sylow 2 G) {M : Subgroup G}
    (d : NaturalOrthogonalAction M (localModule T M)) (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (i : OrthogonalPlaneIndex) :
    ChapterB.baumann (T : Subgroup G) ≤ planeStabilizer T (d.plane i) := by
  have hE := (lemma_15_3_5_centralizing T d hM hJ).2.2.1
  have hCV : ChapterB.baumann (T : Subgroup G) ≤ centralizer (localModule T M : Set G) :=
    inf_le_right.trans (centralizer_le hE)
  exact le_inf inf_le_left (hCV.trans
    ((centralizer_le (d.plane_le i)).trans (Subgroup.centralizer_le_normalizer _)))

/-- All four conclusions of 15.3.6, once the particular plane calculation
supplies the two local Sylow indices and the Thompson calculation supplies
`Baum(T) ≤ S`. -/
theorem lemma_15_3_6_of_local_indices
    (T : Sylow 2 G) (V₁ M : Subgroup G)
    (hB : ChapterB.baumann (T : Subgroup G) ≤ planeStabilizer T V₁)
    (hN : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ M)
    (hcentral : ¬ 2 ∣ (planeStabilizer T V₁).relIndex
      (M ⊓ centralizer (fixedPlane V₁ (planeStabilizer T V₁) : Set G)))
    (hplane : ¬ 2 ∣ (planeStabilizer T V₁).relIndex
      (M ⊓ normalizer (V₁ : Set G))) :
    ChapterB.baumann (T : Subgroup G) = ChapterB.baumann (planeStabilizer T V₁) ∧
      (normalizer (planeStabilizer T V₁ : Set G) ≤
        normalizer (ChapterB.baumann (planeStabilizer T V₁) : Set G) ∧
      normalizer (ChapterB.baumann (planeStabilizer T V₁) : Set G) ≤ M) ∧
      (∃ P : Sylow 2 (centralizer (fixedPlane V₁ (planeStabilizer T V₁) : Set G)),
        (P : Subgroup _).map (centralizer (fixedPlane V₁ (planeStabilizer T V₁) : Set G)).subtype =
          planeStabilizer T V₁) ∧
      (∃ P : Sylow 2 (normalizer (V₁ : Set G)),
        (P : Subgroup _).map (normalizer (V₁ : Set G)).subtype = planeStabilizer T V₁) := by
  obtain ⟨hBaum, hnorm, hcontrol⟩ := lemma_15_3_6_baumann_of_containment T V₁ M hB hN
  refine ⟨hBaum, ⟨hnorm, hcontrol⟩, ?_, ?_⟩
  · exact exists_sylow_of_local_normalizer_control T _ M _ inf_le_left
      (Subgroup.le_centralizer_iff.mp (show fixedPlane V₁ (planeStabilizer T V₁) ≤
        centralizer (planeStabilizer T V₁ : Set G) from inf_le_right)) hcentral
      (hnorm.trans hcontrol)
  · exact exists_sylow_of_local_normalizer_control T _ M _ inf_le_left inf_le_right hplane
      (hnorm.trans hcontrol)

end CFSG.Quasithin.Chapter15.Section03
end
