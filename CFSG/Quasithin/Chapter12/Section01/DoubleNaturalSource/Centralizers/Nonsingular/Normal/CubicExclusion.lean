module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Normal.CubicSource
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Family.Source
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.BlockDisplacement
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.CubicCentralizer
public import Theory.GroupTheory.ConjugateSpanCentralizer
public import Theory.GroupTheory.PerfectSmallNormalizerAction
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# The C.5.7 cubic exclusion from maximality of the original point join

A cubic block normalized by the original perfect component L is centralized
by L: its module has order four, and the short-block displacement theorem
and perfect commutator identity remove the remaining action. Consequently
an escaping cubic block cannot have an index-two normalizer in LT.

The actual normal cubic setup also supplies a noncommuting LT-conjugate of
its module. Otherwise the module's conjugate span is normalized by both LT
and the block, contradicting the proved no-common-normal condition. C.5.7
now excludes the cubic whenever its normalizer is maximal. Maximality of
the literal point join L_w C_T(w) identifies that block normalizer and gives
the complete degree-four normal-residual implication.

The final theorem applies this implication to the nonsingular centralizer
and degree-five closure consumer. Maximality of the degree-four point join,
ordinary-component exclusion and the nonnormal-parabolic argument remain
source obligations of qt-d-double-natural-centralizers. This module does
not assert their unconditional assembly. The independent pure-fusion and
corrected MS obligations remain with their producers and final
qt-d-1222-double-natural assembly.

Source: Aschbacher--Smith, 12.1.1 and C.5.5--7, printed pp.788--789,155--160.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter4 ChapterC
open Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem local_perfect (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    Group.IsPerfect L := by
  let := h.maximal_faithful.1.1.1.perfect
  exact Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective

private theorem cubic_centralizes_of_perfect_normalizer
    (A K : Subgroup G) [Group.IsPerfect A] {R : Subgroup G}
    (C : RankOne.Setup R K (ZMod 2)) (ha : IsAlternatingBlock K 3)
    (hn : A ≤ normalizer (K : Set G)) : K ≤ centralizer (A : Set G) := by
  have hAU : A ≤ centralizer (RankOne.U K : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (commutator_eq_bot_of_perfect_normalizer_card_le_four A (RankOne.U K)
        (hn.trans (normalizer_le_normalizer_characteristic_image K (blockU K)))
        (C.cubic_module_card ha).le)
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply commutator_eq_bot_of_iterated_eq_bot
  exact commutator_eq_bot_iff_le_centralizer.mpr
    ((RankOne.block_fixer_displacement C.short hn hAU).trans (le_centralizer_iff.mp hAU))

/-- Normalization by the original perfect component puts an A₃ block in M. -/
theorem doubleNatural_cubic_block_le_of_component_normalizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) (K : Subgroup G) {R : Subgroup G}
    (C : RankOne.Setup R K (ZMod 2)) (ha : IsAlternatingBlock K 3)
    (hn : L ≤ normalizer (K : Set G)) : K ≤ normalizer (L : Set G) := by
  let := local_perfect h
  have hKL := cubic_centralizes_of_perfect_normalizer L K C ha hn
  have hWL : componentOrbit V (T : Subgroup G) ≤ L :=
    iSup_conjugates_le_of_le_normalizer V (T : Subgroup G) L D.le_component
      D.sylow_normalizes_component
  exact ((hKL.trans (centralizer_le hWL)).trans (Subgroup.centralizer_le_normalizer _)).trans_eq
    (D.doubledOrbit_normalizer_eq h B.orbit_eq)

/-- An escaping A₃ block cannot have an index-two normalizer in LT. -/
theorem doubleNatural_cubic_outside_normalizer_index_ne_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) (K : Subgroup G) {R : Subgroup G}
    (C : RankOne.Setup R K (ZMod 2)) (ha : IsAlternatingBlock K 3)
    (hout : ¬ K ≤ normalizer (L : Set G)) :
    (normalizer (K : Set G)).relIndex (L ⊔ (T : Subgroup G)) ≠ 2 := by
  let := local_perfect h
  intro hi
  let M := L ⊔ (T : Subgroup G)
  let e := subgroupOfEquivOfLe (show L ≤ M from le_sup_left)
  let : Group.IsPerfect (L.subgroupOf M) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hn := le_of_isPerfect_of_index_eq_two (L.subgroupOf M)
    ((normalizer (K : Set G)).subgroupOf M) hi
  exact hout (D.doubleNatural_cubic_block_le_of_component_normalizes h B K C ha
    (fun l hl => hn (show (⟨l,mem_sup_left hl⟩ : M) ∈ L.subgroupOf M from hl)))

omit [Finite G] in
private theorem normalized_short_noncommuting
    (M K R : Subgroup G) (hK : IsShort K) (hUR : RankOne.U K ≤ R)
    (hMR : M ≤ normalizer (R : Set G)) (hRK : R ≤ normalizer (K : Set G))
    (hno : ∀ A : Subgroup G, A ≤ R → M ≤ normalizer (A : Set G) →
      K ≤ normalizer (A : Set G) → A = ⊥) :
    ∃ x ∈ M, ¬ (RankOne.U K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (RankOne.U K : Set G) := by
  by_contra! hc
  let A := conjugateSpanBy (RankOne.U K) M
  have hAC : A ≤ centralizer (RankOne.U K : Set G) := by
    dsimp only [A]
    rw [conjugateSpanBy_eq_iSup_conj]
    apply iSup_le
    intro x
    simpa only [inv_inv] using hc x.val⁻¹ (M.inv_mem x.property)
  have hAR : A ≤ R := conjugateSpanBy_le hUR hMR
  have hKA : K ≤ normalizer (A : Set G) :=
    le_normalizer_iff_commutator_le_right.mpr
      ((RankOne.block_fixer_displacement hK (hAR.trans hRK) hAC).trans
        (le_conjugateSpanBy _ _))
  have hAbot := hno A hAR (le_normalizer_conjugateSpanBy _ _) hKA
  apply hK.blockU_ne_bot
  apply (map_eq_bot_iff_of_injective _ K.subtype_injective).mp
  exact bot_unique ((le_conjugateSpanBy (RankOne.U K) M).trans hAbot.le)

/-- The actual normal cubic branch supplies the noncommuting conjugator required by C.5.7. -/
theorem doubleNatural_four_normal_cubic_noncommuting
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4)
    (w : componentOrbit V (T : Subgroup G)) (K : Subgroup G)
    (hHK : B.pointCentralizer w ≤ normalizer (K : Set G))
    (C : RankOne.Setup ((L ⊔ (T : Subgroup G)).pCoreIn 2) K (ZMod 2))
    (hout : ¬ K ≤ normalizer (L : Set G)) :
    ∃ x ∈ L ⊔ (T : Subgroup G),
      ¬ (RankOne.U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (RankOne.U K : Set G) := by
  let M := L ⊔ (T : Subgroup G)
  let Q := M.pCoreIn 2
  have hMQ : M ≤ normalizer (Q : Set G) := M.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  apply normalized_short_noncommuting M K Q C.short (C.module_le.trans inf_le_left) hMQ
    ((D.doubleNatural_core_le_pointCentralizer h B w).trans hHK)
  intro A hAQ hMA hKA
  exact D.doubleNatural_outside_no_common_normal h K (B.pointSylow w) A hout hAQ
    (normal_subgroupOf_of_le_normalizer (sup_le hMA
      (sup_le hKA ((inf_le_left.trans le_sup_right).trans hMA))))

/-- The C.5.7 block-normalizer maximality excludes the actual escaping cubic. -/
theorem doubleNatural_four_normal_cubic_le_of_normalizer_maximal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4)
    (w : componentOrbit V (T : Subgroup G)) (K : Subgroup G)
    (hHK : B.pointCentralizer w ≤ normalizer (K : Set G))
    (C : RankOne.Setup ((L ⊔ (T : Subgroup G)).pCoreIn 2) K (ZMod 2))
    (ha : IsAlternatingBlock K 3)
    (hmax : IsCoatom ((normalizer (K : Set G)).subgroupOf (L ⊔ (T : Subgroup G)))) :
    K ≤ normalizer (L : Set G) := by
  by_contra hout
  let M := L ⊔ (T : Subgroup G)
  let Q := M.pCoreIn 2
  have hMQ : M ≤ normalizer (Q : Set G) := M.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  obtain ⟨x,hx,hnc⟩ := D.doubleNatural_four_normal_cubic_noncommuting h B w K hHK C hout
  have hC57 := C.source_C57 (K ⊔ B.pointSylow w) M (B.pointSylow w)
    (inf_le_left.trans le_sup_right) hMQ (inf_le_right.trans hHK) rfl
    (fun A hAQ hHA hMA => D.doubleNatural_outside_no_common_normal h K
      (B.pointSylow w) A hout hAQ (normal_subgroupOf_of_le_normalizer (sup_le hMA hHA)))
    hmax x hx hnc
  exact D.doubleNatural_cubic_outside_normalizer_index_ne_two h B K C ha hout hC57.2.1

/-- The source maximal point join identifies the actual block normalizer in LT. -/
theorem doubleNatural_cubic_normalizer_eq_pointJoin_of_maximal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n)
    (w : componentOrbit V (T : Subgroup G)) (K : Subgroup G) {R : Subgroup G}
    (hHK : B.pointCentralizer w ≤ normalizer (K : Set G))
    (C : RankOne.Setup R K (ZMod 2)) (ha : IsAlternatingBlock K 3)
    (hout : ¬ K ≤ normalizer (L : Set G))
    (hmax : IsCoatom ((B.pointResidual w ⊔ B.pointSylow w).subgroupOf
      (L ⊔ (T : Subgroup G)))) :
    (normalizer (K : Set G)).subgroupOf (L ⊔ (T : Subgroup G)) =
      (B.pointResidual w ⊔ B.pointSylow w).subgroupOf (L ⊔ (T : Subgroup G)) := by
  let M := L ⊔ (T : Subgroup G)
  let J := B.pointResidual w ⊔ B.pointSylow w
  let N := (normalizer (K : Set G)).subgroupOf M
  have hJN : J ≤ normalizer (K : Set G) :=
    (sup_le ((B.pointResidual_le w).trans inf_le_right) inf_le_right).trans hHK
  have hle : J.subgroupOf M ≤ N := fun _ hx => hJN hx
  by_contra he
  have htop : N = ⊤ := hmax.lt_iff.mp (lt_of_le_of_ne hle (Ne.symm he))
  have hLK : L ≤ normalizer (K : Set G) := by
    intro l hl
    exact (show (⟨l,mem_sup_left hl⟩ : M) ∈ N from htop ▸ mem_top _)
  exact hout (D.doubleNatural_cubic_block_le_of_component_normalizes h B K C ha hLK)

/-- The entire degree-four normal-residual branch needs only the original maximal-point-join geometry. -/
theorem doubleNatural_four_adapted_normal_centralizer_le_of_pointJoin_maximal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
      ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      IsCoatom ((B.pointResidual w ⊔ B.pointSylow w).subgroupOf (L ⊔ (T : Subgroup G))) →
      B.pointCentralizer w ≤ normalizer (L : Set G) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hc hn hmax
  by_contra hout
  obtain ⟨K,hKY,hK,_,ha,houtK,hmove,_⟩ :=
    D.doubleNatural_adapted_normal_outside_alternatingThree h B S w hw hc hn hout
  obtain ⟨C⟩ := D.doubleNatural_four_normal_cubic_setup h B S w hw hc hn K hKY hK ha hmove
  have ht : IsChiBlock (K.subgroupOf
      (sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w))) :=
    Or.inr ⟨3,by decide,ha.of_mulEquiv (subgroupOfEquivOfLe hKY).symm⟩
  have hHK := D.doubleNatural_four_normal_chi_block_normalized h B S w hw.nonsingular
    hc hn K hKY ⟨hK,ht⟩
  have he := D.doubleNatural_cubic_normalizer_eq_pointJoin_of_maximal h B w K hHK C ha houtK hmax
  exact houtK (D.doubleNatural_four_normal_cubic_le_of_normalizer_maximal h B w K hHK C ha
    (he.symm ▸ hmax))

/-- Actual nonsingular and degree-five closure assembly with the cubic source reduced
only to maximality of the original degree-four point join. -/
theorem doubleNatural_nonsingular_controls_of_pointJoin_maximal_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    (∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w)) →
    (n = 4 → ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      IsCoatom ((B.pointResidual w ⊔ B.pointSylow w).subgroupOf (L ⊔ (T : Subgroup G)))) →
    (∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
      ¬ ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      ¬ B.pointCentralizer w ≤ normalizer (L : Set G) →
      B.pointResidual w ≤ centralizer (B.fixedLine : Set G)) →
    B.NonsingularCentralizers ∧
      (n : ℕ∞) ≤ ChapterE.globalR (componentOrbit V (T : Subgroup G)) ∧
      (n = 5 → 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) := by
  let := D.doubledOrbit_elementary h
  intro hchar hmax hparabolic
  apply D.doubleNatural_nonsingular_controls_of_four_cubic_of_many h hmany B hchar _ hparabolic
  intro hn S w hw hc hnormal K hKY _ _ _ _ _ _ _
  subst n
  exact (hKY.trans inf_le_left).trans
    (D.doubleNatural_four_adapted_normal_centralizer_le_of_pointJoin_maximal
      h B S w hw hc hnormal (hmax rfl S w hw))

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
