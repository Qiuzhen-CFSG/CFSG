module

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Marking
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSource
public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource.Hypothesis1311
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import Theory.GroupTheory.InvolutionCentralizerControl
public import CFSG.Quasithin.Chapter13.Section04.SolvableCentralizerC3

/-!
# The actual fixed-line centralizer and chamber core in13.4

The earlier structural theorem normalizes the chosen module in N(L), since
its fixed subgroup is nontrivial. The marked fixed line has order two, so
its normalizer centralizes it. Uniqueness over LT then identifies its full
centralizer with N(L)=N(V). This also supplies the distinguished involution
centralizer in13.4.9 and proves D4 for the literal generated subgroup.

Structural1222 and the earlier maximal/quasisimple applicability remain
explicit inputs from the Chapter12 and13.3.2 producers. No maximality among
all proper subgroups is assumed. Source: Aschbacher–Smith13.4.2(1) and the
D4 step of13.4.9, printed pp.897 and906.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
  (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
  (D : ChosenModule T L V) (m : CoreMarking D)
include h structural D m

/-- The module-normalizer alternative of12.2.2 is forced by the fixed line. -/
theorem normalizer_component_le_module :
    normalizer (L : Set G) ≤ normalizer (V : Set G) :=
  (((structural G T L h).2.2 V D).2.2.2).resolve_right m.fixed_ne_bot

/-- Both normalizers in13.4.2(1) are the original full ambient normalizers. -/
theorem normalizer_component_eq_module :
    normalizer (L : Set G) = normalizer (V : Set G) :=
  le_antisymm (normalizer_component_le_module h structural D m)
    (h.source_chosen_normalizer_le structural
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) D)

theorem normalizer_component_le_fixed_centralizer :
    normalizer (L : Set G) ≤ centralizer (V ⊓ centralizer (L : Set G) : Set G) := by
  apply le_trans ?_ (normalizer_le_centralizer_of_card_two _ m.card_fixed)
  exact (le_inf (normalizer_component_le_module h structural D m)
    (normalizer_le_normalizer_centralizer L)).trans inf_normalizer_le_normalizer_inf

/-- The full fixed-line centralizer equals M, using maximal two-local uniqueness. -/
theorem fixed_centralizer_eq_normalizer :
    centralizer (V ⊓ centralizer (L : Set G) : Set G) = normalizer (L : Set G) := by
  apply le_antisymm ?_ (normalizer_component_le_fixed_centralizer h structural D m)
  apply (Subgroup.centralizer_le_normalizer _).trans
  apply normalizer_le_of_unique_maximalTwoLocal
    (h.source_normalizer_maximal_unique structural
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).2
    ((T.isPGroup'.to_le D.le_sylow).to_le inf_le_left) m.fixed_ne_bot
  exact ((sup_le L.le_normalizer (h.source_sylow_normalizes structural)).trans
    (normalizer_component_le_fixed_centralizer h structural D m)).trans
      (Subgroup.centralizer_le_normalizer _)

/-- Every nonidentity element of the actual fixed line has full centralizer M. -/
theorem fixed_generator_centralizer {d : G}
    (hd : d ∈ V ⊓ centralizer (L : Set G)) (hd1 : d ≠ 1) :
    centralizer ({d} : Set G) = normalizer (L : Set G) := by
  have hgen : zpowers d = V ⊓ centralizer (L : Set G) := by
    have he := congrArg (fun A : Subgroup ↥(V ⊓ centralizer (L : Set G)) =>
      A.map (V ⊓ centralizer (L : Set G)).subtype)
      (zpowers_eq_top_of_prime_card (p := 2) m.card_fixed
        (show (⟨d, hd⟩ : ↥(V ⊓ centralizer (L : Set G))) ≠ 1 from
          fun he => hd1 (congrArg Subtype.val he)))
    simpa only [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,
      range_subtype, subtype_apply] using he
  calc
    centralizer ({d} : Set G) = centralizer (V ⊓ centralizer (L : Set G) : Set G) := by
      rw [← centralizer_closure, ← zpowers_eq_closure, hgen]
      rfl
    _ = normalizer (L : Set G) := fixed_centralizer_eq_normalizer h structural D m

/-- D5 holds because the actual fixed line lies in the center of M. -/
theorem normalizer_center_ne_bot : center (normalizer (L : Set G)) ≠ ⊥ := by
  obtain ⟨d, hd1⟩ := ne_bot_iff_exists_ne_one.mp m.fixed_ne_bot
  have hd : (d : G) ≠ 1 := fun he => hd1 (Subtype.ext he)
  let x : normalizer (L : Set G) :=
    ⟨d.val, D.sylow_normalizes_component (D.le_sylow d.property.1)⟩
  have hx : x ∈ center (normalizer (L : Set G)) := by
    rw [mem_center_iff]
    intro y
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp
      ((fixed_generator_centralizer h structural D m d.property hd).symm ▸ y.property)
  intro he
  have hx1 := mem_bot.mp (he ▸ hx)
  exact hd (congrArg Subtype.val hx1)

/-- The actual original module supplies the32-element first-vertex core bound. -/
theorem normalizer_twoCore_card : 32 ≤ Nat.card (pCore 2 (normalizer (L : Set G))) :=
  SolvableCentralizerC3.original_five_module_core_bound _ V
    (T.isPGroup'.to_le D.le_sylow)
    (D.le_sylow.trans D.sylow_normalizes_component)
    (normalizer_component_le_module h structural D m) m.card_module

omit D m in
/-- D4 is discharged from the same maximal two-local uniqueness as13.4.2. -/
theorem original_chamber_core_eq_bot (z : G) (H₀ : Subgroup G)
    (hout : ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G)) :
    ((T : Subgroup G).subgroupOf
      (SolvableCentralizerC3.generated (normalizer (L : Set G)) z H₀)).normalCore = ⊥ := by
  apply SolvableCentralizerC3.original_chamber_core_free _ H₀ T z T.isPGroup' hout
  intro N hN hne _ hn
  apply normalizer_le_of_unique_maximalTwoLocal
    (h.source_normalizer_maximal_unique structural
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).2 hN hne
  exact (sup_le L.le_normalizer (h.source_sylow_normalizes structural)).trans hn

/-- The earlier escaping vector lies outside the actual fixed line. Its later
placement in V∩Ω₁Z(T) is a separate13.3.5/13.4 geometric step. -/
theorem exists_nonfixed_escape (h₀ : Hypothesis1331 T L)
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u}) :
    ∃ z ∈ V, z ≠ 1 ∧ z ∉ centralizer (L : Set G) ∧
      ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨z, hz, hz1, hout⟩ := h₀.hypothesis1311.centralizer_escape earlier
    h.maximal_faithful h.quasisimple D
  refine ⟨z, hz, hz1, ?_, hout⟩
  intro hf
  exact hout (fixed_generator_centralizer h structural D m ⟨hz, hf⟩ hz1).le

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource
