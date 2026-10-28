module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.Setup
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.Placement
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingSevenFixed

/-!
# The terminal ordinary-A₇ contradiction

The chosen six-support vector is fixed by the first residual, excluding
Tᵢ=T₀. Preferred centralization then fixes u. Central correction of that
vector and its escaping component centralizer put u in the actual full
block module. The ordinary seven-letter block has zero fixed layer, giving
a contradiction to the original movement hypothesis.

Only the concrete partition geometry is explicit. In particular the proof
does not assume that the six-support vector is fixed by the whole group.
Source: Aschbacher--Smith, original14.6.10(5), pp.1029--1030.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.Seven
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))


omit [Finite G] in
/-- The full ordinary A₇ module has no nonidentity component-fixed element. -/
theorem ordinary_module_inf_centralizer (C : Subgroup G)
    (hb : ChapterC.IsAlternatingBlock C 7) :
    (ChapterC.blockU C).map C.subtype ⊓ centralizer (C : Set G) = ⊥ := by
  apply bot_unique
  rintro x ⟨⟨c,hc,rfl⟩,hz⟩
  have hcz : c ∈ center C := by
    apply mem_center_iff.mpr
    intro z
    exact Subtype.ext (hz z z.property)
  have he : ChapterC.blockU C ⊓ center C = ⊥ := by
    rw [←ChapterC.blockFixed_map,hb.seven_fixed_eq_bot,Subgroup.map_bot]
  exact congrArg C.subtype (mem_bot.mp (he ▸
    (show c ∈ ChapterC.blockU C ⊓ center C from ⟨hc,hcz⟩)))

/-- The source ordinary-A₇ row is impossible once its actual partition
geometry is supplied. All placement and preferred-choice steps are proved. -/
theorem ordinary_false_of_geometry
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceSecondParabolicData
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) Mc M)
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({d.u} : Set G)) Mc M))
    (hpreferred : (T : Subgroup G) ⊓ I = (T : Subgroup G) ⊓ centralizer ({d.u} : Set G) →
      I ≤ centralizer ({d.u} : Set G))
    (hb : ChapterC.IsAlternatingBlock (sourceGeneratedComponent T M Mc I d.H2) 7)
    (g : OrdinaryGeometry T M Mc I d.H2) : False := by
  let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  let I0 := sourceGeneratedParabolic T M Mc I d.H2
  let C := sourceGeneratedComponent T M Mc I d.H2
  let W := (ChapterC.blockU C).map C.subtype
  have hCI : C ≤ I0 := map_subtype_le _
  obtain ⟨hI0,hS,hout0,hI2H,hpreferred0⟩ :=
    generated_choice hG T hempty hM hunique hmany hcard e hab H hH d I hI hpreferred
  have ha : g.vector ∈ conjugateSpanBy (localModule T M) H :=
    conjugateSpanBy_mono le_rfl hI2H g.mem_span
  have haW : g.vector ∈ W :=
    generated_span_le_module hG T hempty hM hunique hmany hcard e hab H hH d I hI
      (conjugateSpanBy_mono le_rfl le_sup_right g.mem_span)
  have hlocal := source_suitable_local_sylow hG T hempty hM hunique hmany hcard e hab
    H hH d.u d.mem_span d.local_normalizer
  obtain ⟨hTI,hIu⟩ := source_sylow_eq_of_first_fixed_vector
    hG T hempty hM hunique hmany hcard e hab H hH d.u d.mem_span d.index
    d.moves_core d.product_moves_core d.local_normalizer hlocal I0 hI0 hout0 hpreferred0
    g.vector ha g.ne_one g.first_fixed
  have hi := source_lemma_14_6_3_1 hG T hempty hM hunique hmany hcard e hab H hH
    d.u d.mem_span d.index d.moves_core d.product_moves_core
  have hmove : ¬ H.pCoreIn 2 ≤ centralizer ({d.u} : Set G) := by
    intro hh
    have h0Tu : suitableQuotientCentralizer h d.u ≤ ((T : Subgroup G) ⊓ centralizer ({d.u} : Set G)) := by
      rw [hi.2.2.2.1]
      exact sup_le (le_inf h.QH_le_T hh) le_rfl
    have hz := relIndex_eq_one.mpr h0Tu
    have ht : (((T : Subgroup G) ⊓ centralizer ({d.u} : Set G))).relIndex
        (suitableQuotientCentralizer h d.u) = 2 := hi.1
    omega
  have hTa : (T : Subgroup G) ⊓ centralizer ({d.u} : Set G) ≤
      centralizer ({g.vector} : Set G) := by
    rw [←hTI]
    exact g.sylow_fixed
  have huW := involution_mem_of_escaping_vector_centralizer h d.u g.vector
    d.mem_span ha g.ne_one W I0 C M Mc haW hCI hI0 hTI hTa
    hIu g.escapes_Mc g.escapes_M hi.1 hi.2.2.2.1 hmove
  have huc : d.u ∈ centralizer (C : Set G) := by
    intro c hc
    exact mem_centralizer_singleton_iff.mp (hIu (hCI hc))
  have hu1 : d.u = 1 := show d.u ∈ (⊥ : Subgroup G) from
    ordinary_module_inf_centralizer C hb ▸ ⟨huW,huc⟩
  exact d.moves_core (by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (by simp [hu1]))

end CFSG.Quasithin.Chapter14.Section06.Seven
