module
public import CFSG.Quasithin.Chapter13.Section06.SourceAbelian.KnownSimple
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.OmegaSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.SymmetricSix.Inputs
public import CFSG.Quasithin.Chapter13.Section02.A5Local.Fusion
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Geometry.Family
public import CFSG.Quasithin.Chapter5.A5Source.Complete
public import CFSG.Quasithin.Chapter5.A5Source.BaumannAction
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.MarkedPlane

/-!
# Original context inputs to the nonsingular centralizer argument

The chosen A₅ module supplies the structural and relative normality data.
Uniqueness and the actual multiple-overgroup guard give an outside local
subgroup. Original 13.2.7 then gives singular escape and omega-centralizer
vanishing. The proved 13.5.10–12 results supply the abelian-span inputs.

The literal five-point action proves the Baumann alternatives. Outside
centralization and the point-centralizer form of 5.1.7 give the Baumann
normalizer bound, which promotes C_T(v) to a Sylow subgroup of C_G(v).
Comparing its order with T separates the
singular and nonsingular classes and supplies both fusion inputs, before
the desired centralizer containment is proved.

Source: Aschbacher–Smith 13.2.4–7, 13.5.10–12 and 13.6.2–5,
printed pp.879–880,918–925,926. Original 13.2.7 remains explicit. In
particular, the Baumann normalizer bound proved here uses 13.2.7 and
cannot replace the independent earlier Baumann argument in its proof.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open A5Module ComponentSelection ComponentReduction InitialSieve
open ComponentElimination.SourceContainment.RankTwo.LocalApplication
open Section05.A5Source TerminalContradiction.Ratio
open BinaryPermutation BinaryPermutation.FiveCentralizerGeometry
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

/-- The original context and counterexample give exactly the standing source
hypothesis used at every selected component. -/
theorem standing (hc : IsA5Counterexample G) : SourceHypothesis T L where
  qtke := d.hypothesis.qtke
  local_component := d.hypothesis.local_component
  no_larger_field := fun f hf h => d.hypothesis.no_larger_field ⟨f,hf,h⟩
  no_linear := d.hypothesis.no_linear
  no_alternating_nine := d.hypothesis.no_alternating_nine
  no_sporadic := d.hypothesis.no_sporadic
  five_minimal := d.hypothesis.five_minimal
  a5 := ⟨d.quotient⟩
  counterexample := hc

/-- Every module premise of the characteristic-two sieve is supplied on the
same aligned flag, including containment in the original component's core. -/
theorem moduleData : SymmetricSix.ModuleData d.flag.flag.module where
  twoPerfect := d.twoPerfect
  fitting := d.characteristic_L
  action_kernel := d.flag.flag.action_kernel
  V_le_core := d.chosen.le_componentCore
  V_central_core := le_centralizer_iff.mp <|
    (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le L.le_normalizer d.normalizes_L)).trans d.chosen.core_centralizes
  residual_quotient_card := d.flag.flag.residualQuotient_card

/-- The original maximal local really is N_G(L). -/
theorem maximal_normalizer : IsMaximalTwoLocal (normalizer (L : Set G)) := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    d.hypothesis.qtke T d.maximal_local
  have horbit : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L _ L le_rfl d.normalizes_L)
      (le_componentOrbit L _)
  simpa only [horbit] using hu.normalizer_maximal

/-- Construct original 13.6.3(1), independently of nonsingular containment. -/
theorem singular_escape
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h1327 : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    ¬ Gv (markedZ d.flag.flag.module) ≤ normalizer (L : Set G) := by
  obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside
    (Chapter3.hasMaximalOutside_of_many T hmany _ (maximal_normalizer d) d.normalizes_L)
  intro hc
  apply hH.1.2
  apply le_trans _ hc
  intro h hh
  exact mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp (h1327 H hH hh) _ d.flag.flag.z_central).symm

/-- Assemble the earlier local interface from the genuine Context. Only
13.2.4, the Baumann normalizer bound, and 13.2.7 remain as source inputs. -/
theorem earlierLocal
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h1327 : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (h1324 : ChapterB.baumann (T : Subgroup G) ≤
        (T : Subgroup G) ⊓ centralizer (V : Set G) ∨
      V ⊓ centralizer (ChapterB.baumann (T : Subgroup G) : Set G) = V₂)
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G)) :
    EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.flag.module) := by
  let := d.elementary
  have hout := singular_escape d hmany h1327
  have hpoint : centralizer (V₁ : Set G) = Gv (markedZ d.flag.flag.module) := by
    conv_lhs => rw [←d.flag.flag.line_eq]
    rw [zpowers_eq_closure, centralizer_closure]
    rfl
  have hH : Gv (markedZ d.flag.flag.module) ∈ Section08.Source.Hz
      (residualCentralizer L V₁) (T : Subgroup G)
      (centralizer (V₁ : Set G)) (normalizer (L : Set G)) := by
    rw [←hpoint]
    exact SourceAbelian.point_centralizer_mem_family d (hpoint.symm ▸ hout)
  refine {
    maximal_overgroups := ?_
    other_local := ?_
    T_normalizes_L := d.normalizes_L
    outside_centralizes := h1327
    span_equivalence := ?_
    nonabelian_classification := ?_
    baumann_alternatives := h1324
    baumann_normalizer := hB
    trivial_intersections := d.trivial_intersections
    module_normalizer := d.module_normalizer }
  · ext N
    constructor
    · intro hN
      exact d.unique_maximal_overgroup N hN.1 hN.2
    · rintro (rfl : N = normalizer (L : Set G))
      exact ⟨maximal_normalizer d, sup_le L.le_normalizer d.normalizes_L⟩
  · obtain ⟨A,hA,B,hB,hne⟩ := (Set.one_lt_ncard_iff_nontrivial_and_finite.mp hmany).1
    by_cases he : A = normalizer (L : Set G)
    · exact ⟨B,hB.1,hB.2,fun h => hne (he.trans h.symm)⟩
    · exact ⟨A,hA.1,hA.2,he⟩
  · exact (source13_5_10_knownSimple d hH).1.1
  · exact SourceAbelian.source_nonabelian_classification_knownSimple d hH

/-- Baumann promotion proves separation of the two actual marked classes;
the nonsingular centralizer bound is not an input to this proof. -/
theorem marked_not_conjugate
    (hS : ChapterB.baumann (T : Subgroup G) ≤ Tv (T : Subgroup G) (markedV d.flag.flag.module))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G)) :
    ¬ IsConj (markedV d.flag.flag.module) (markedZ d.flag.flag.module) := by
  have hMV : Mv (normalizer (L : Set G)) (markedV d.flag.flag.module) ≤ normalizer (V : Set G) :=
    inf_elementCentralizer_le_normalizer_of_trivial_intersections
      d.trivial_intersections (map_mem d.flag.flag.module _) (markedV_ne_one d.flag.flag.module)
  have hlocal := d.flag.flag_localIndex
  have he : normalizer (L : Set G) ⊓ Gv (markedV d.flag.flag.module) =
      normalizer (V : Set G) ⊓ Gv (markedV d.flag.flag.module) :=
    le_antisymm (le_inf hMV inf_le_right) (inf_le_inf_right _ d.module_normalizer)
  rw [←he] at hlocal
  let B : Subgroup (Tv (T : Subgroup G) (markedV d.flag.flag.module)) := ChapterB.baumann ⊤
  have hmap : B.map (Tv (T : Subgroup G) (markedV d.flag.flag.module)).subtype =
      ChapterB.baumann (T : Subgroup G) := by
    rw [(baumann_and_thompson_centralizer (T : Subgroup G) _ hS).1]
    simpa only [B, ChapterB.baumann, ChapterB.thompsonAlpha,
      ← MonoidHom.range_eq_map, range_subtype] using
      baumann_map_injective (Tv (T : Subgroup G) (markedV d.flag.flag.module)).subtype
        (Tv (T : Subgroup G) (markedV d.flag.flag.module)).subtype_injective ⊤
  apply @Sylow.not_isConj_of_characteristic_centralizer_normalizer
    G _ _ 2 ⟨Nat.prime_two⟩ T
    (normalizer (L : Set G)) (markedV d.flag.flag.module) (markedZ d.flag.flag.module)
    B (show B.Characteristic from ChapterB.baumann_characteristic)
    hlocal (hmap.symm ▸ hB)
  · intro heq
    have hc : (T : Subgroup G) ≤ Gv (markedV d.flag.flag.module) := heq ▸ inf_le_right
    obtain ⟨g,hg⟩ := d.flag.flag_relabel
    rw [hg] at hc
    apply d.flag.not_centralizes_nonsingular (FlagCoordinates.rho g v) _ hc
    rw [FlagCoordinates.SylowCalculation.form_invariant]
    decide
  · intro t ht
    exact mem_centralizer_singleton_iff.mpr
      (((mem_omegaOneCenterAmbient_iff (T : Subgroup G) _).mp d.flag.flag.z_central).2.2 t ht)

/-- Both fusion inputs to the component argument follow from the earlier
Baumann control, on the same flag used by the terminal consumer. -/
theorem fusion
    (hS : ChapterB.baumann (T : Subgroup G) ≤ Tv (T : Subgroup G) (markedV d.flag.flag.module))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G)) :
    ControlsFusionOfZ d.flag.flag.module ∧ FusionPreservesForm d.flag.flag.module := by
  have hf := d.flag.flag.module.controls_fusion_of_nonconjugate (marked_not_conjugate d hS hB)
  constructor
  · intro x hx ⟨g,hg⟩
    obtain ⟨l,hl⟩ := hf _ (map_mem d.flag.flag.module _) (markedZ_ne_one d.flag.flag.module)
      g (hg.symm ▸ hx)
    exact ⟨l,hl.trans hg⟩
  · intro g u w he
    by_cases hu : u = 0
    · subst u
      have hw : w = 0 := by
        apply Multiplicative.ofAdd.injective
        apply d.flag.flag.module.injective
        simpa only [ofAdd_zero, map_one] using he.symm
      rw [hw]
    · have hu1 : d.flag.flag.module.map (Multiplicative.ofAdd u) ≠ 1 := by
        intro h
        exact hu (d.flag.flag.module.injective (h.trans (map_one _).symm))
      obtain ⟨l,hl⟩ := hf _ (map_mem d.flag.flag.module _) hu1 g
        (he.symm ▸ map_mem d.flag.flag.module _)
      have hh := (d.flag.flag.module.equivariant l u).symm.trans (hl.trans he)
      have hw := d.flag.flag.module.injective hh
      change coreRepresentation (Fin 5) (d.flag.flag.module.action l).val u = w at hw
      rw [←hw, FlagCoordinates.SylowCalculation.form_invariant]

open Representation Representation.BinaryOffender

private theorem baumann_fixed_card
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G)) :
    Nat.card (V ⊓ centralizer (ChapterB.baumann (T : Subgroup G) : Set G) : Subgroup G) = 4 := by
  let K := L ⊔ (T : Subgroup G)
  let U := V.subgroupOf K
  let B := (ChapterB.baumann (T : Subgroup G)).subgroupOf K
  let := d.reduced.normal
  let := d.reduced.elementary
  have hq := d.localActor_surjective_of_thompson_moves hJ
  let ρ := NormalElementaryQuotient.representation U d.localActor hq d.localActor_kernel
  let σ := coreRepresentation (Fin 5)
  obtain ⟨a,ha⟩ := Chapter5.A5Source.local_baumann_four_group d hJ
  have hcod : fixedCodim σ (B.map d.localActor) = 2 := by
    rw [ha, fixedCodim_map_conj]
    exact ChapterB.Offenders.Odd.fixedCodim_core_disjointTranspositions (Or.inl rfl) le_rfl
  have hdim : Module.finrank (ZMod 2) (fixedSpace σ (B.map d.localActor)) = 2 := by
    have hh := fixedCodim_add_finrank σ (B.map d.localActor)
    rw [FiveGeometry.finrank_core] at hh
    omega
  have hdimρ : Module.finrank (ZMod 2) (fixedSpace ρ (B.map d.localActor)) = 2 := by
    have he := fixedSpace_map_equivariant ρ σ (MonoidHom.id _) d.localModuleCoordinates.symm
      (Chapter5.A5Source.local_full_equivariant d hq) (B.map d.localActor)
    rw [Subgroup.map_id] at he
    rw [←he, LinearEquiv.finrank_map_eq] at hdim
    exact hdim
  have hc : Nat.card (U ⊓ centralizer (B : Set K) : Subgroup K) = 4 := by
    rw [← Nat.card_congr (NormalElementaryQuotient.fixedSpaceEquiv U d.localActor
      hq d.localActor_kernel B), Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod, hdimρ]
    rfl
  have hmap : (U ⊓ centralizer (B : Set K)).map K.subtype =
      V ⊓ centralizer (ChapterB.baumann (T : Subgroup G) : Set G) := by
    rw [← map_inf_centralizer_of_injective K.subtype K.subtype_injective,
      map_subgroupOf_eq_of_le (show ChapterB.baumann (T : Subgroup G) ≤ K from
        inf_le_left.trans le_sup_right),
      map_subgroupOf_eq_of_le (d.chosen.le_sylow.trans le_sup_right)]
  rw [←hmap, card_map_of_injective K.subtype_injective]
  exact hc

/-- The actual original Baumann alternatives of 13.2.4(2), obtained from
the marked Thompson action and uniqueness of the invariant plane. -/
theorem baumann_alternatives :
    ChapterB.baumann (T : Subgroup G) ≤ (T : Subgroup G) ⊓ centralizer (V : Set G) ∨
      V ⊓ centralizer (ChapterB.baumann (T : Subgroup G) : Set G) = V₂ := by
  by_cases hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G)
  · left
    let := d.elementary
    rw [ChapterB.lemma_B_2_3_5 (T : Subgroup G) V d.chosen.le_sylow hJ]
    exact inf_le_left
  · right
    apply d.invariant_plane_unique (d.localActor_surjective_of_thompson_moves hJ)
      _ _ inf_le_left d.flag.two_le_V (baumann_fixed_card d hJ) d.flag.two_card _
      d.flag.two_invariant
    apply (le_inf d.flag.T_normalizes _).trans inf_normalizer_le_normalizer_inf
    exact ((T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _)).trans
      (normalizer_le_normalizer_centralizer _)

/-- In the original counterexample, 13.2.7 and uniqueness make C_T(L)
trivial. The proved point-centralizer version of 5.1.7 then supplies the
Baumann normalizer bound without a separate uniqueness-over-L callback. -/
theorem baumann_normalizer
    (hc : IsA5Counterexample G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h1327 : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) := by
  have hCT := sylow_centralizer_of_original_outside_source T L (standing d hc)
    d.normalizes_L hmany h1327
  apply Chapter5.A5Source.baumann_normalizer_of_point_centralizers d
  intro x hx hne
  exact (hne (mem_bot.mp (hCT ▸ (show x ∈ (T : Subgroup G) ⊓ centralizer (L : Set G)
    from ⟨hx.1.1,hx.2⟩)))).elim

/-- The actual C_T(v) normalizes the literal residual O²(C_L(v)). -/
theorem normalizes_residual : Tv (T : Subgroup G) (markedV d.flag.flag.module) ≤
    normalizer (Lv L (markedV d.flag.flag.module) : Set G) := by
  have hn := (inf_le_inf d.normalizes_L (Gv (markedV d.flag.flag.module)).le_normalizer).trans
    inf_normalizer_le_normalizer_inf
  exact hn.trans (normalizer_le_normalizer_characteristic_image
    (L ⊓ Gv (markedV d.flag.flag.module)) (pResidual 2 ↥(L ⊓ Gv (markedV d.flag.flag.module))))

/-- The same residual Sylow subgroup fixes the original singular mark. -/
theorem centralizes_singular : Tv (T : Subgroup G) (markedV d.flag.flag.module) ≤
    centralizer ({markedZ d.flag.flag.module} : Set G) := by
  intro t ht
  exact mem_centralizer_singleton_iff.mpr
    (((mem_omegaOneCenterAmbient_iff (T : Subgroup G) _).mp d.flag.flag.z_central).2.2 t ht.1)

/-- Every local and fusion input is now constructed from the original
Context and the genuine outside-centralization theorem 13.2.7. -/
theorem configuration_of_outside_source
    (hc : IsA5Counterexample G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h1327 : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    Nonempty (LocalConfiguration (normalizer (L : Set G)) d.flag.flag) ∧
      ControlsFusionOfZ d.flag.flag.module ∧ FusionPreservesForm d.flag.flag.module := by
  have hB := baumann_normalizer d hc hmany h1327
  have hS := baumann_le_Tv_of_alternatives T V V₂ _ (map_mem d.flag.flag.module _)
    d.flag.flag.vector_mem (baumann_alternatives d)
  have hf := fusion d hS hB
  exact ⟨localConfiguration_of_earlier_source d.flag (normalizer (L : Set G)) V₃
    (earlierLocal d hmany h1327 (baumann_alternatives d) hB) hc hf.1,hf⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
