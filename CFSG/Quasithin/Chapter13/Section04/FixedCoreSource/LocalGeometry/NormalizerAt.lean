module

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Marking
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource.Hypothesis1311
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import Theory.GroupTheory.InvolutionCentralizerControl
public import CFSG.Quasithin.Chapter13.Section04.SolvableCentralizerC3

/-!
# Fixed-line normalizers from the structural theorem at the same G,T

The nonzero fixed line forces the normalizer alternative of 12.2.2.
Uniqueness over LT then identifies the full fixed-line centralizer with
both N_G(L) and N_G(V). The ambient exclusions in Hypothesis 13.1.1
eliminate the three recognition alternatives of 12.2.13 at this L,V,
producing an escaping vector outside the fixed line.

Every invocation of the earlier structural and recognition inputs is at
the original G,T and retains Hypothesis 12.2.3. No universal record is
constructed. OmegaSourceAt applies these results to the actual omega
point; the existing universal normalizer APIs are preserved.
Source: Aschbacher--Smith 13.1.2(2), 13.4.2(1), pp.866,897.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
  (structural : Structural1222At KnownSimple.IsKnownSimple T)
  (D : ChosenModule T L V) (m : CoreMarking D)
include h structural D m

set_option linter.unusedSectionVars false in
/-- The module-normalizer alternative of12.2.2 is forced by the fixed line. -/
theorem normalizer_component_le_module_at :
    normalizer (L : Set G) ≤ normalizer (V : Set G) :=
  (((structural L h).2.2 V D).2.2.2).resolve_right m.fixed_ne_bot

/-- Both normalizers in13.4.2(1) are the original full ambient normalizers. -/
theorem normalizer_component_eq_module_at :
    normalizer (L : Set G) = normalizer (V : Set G) :=
  le_antisymm (normalizer_component_le_module_at h structural D m)
    (h.source_chosen_normalizer_le_at structural
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) D)

theorem normalizer_component_le_fixed_centralizer_at :
    normalizer (L : Set G) ≤ centralizer (V ⊓ centralizer (L : Set G) : Set G) := by
  apply le_trans ?_ (normalizer_le_centralizer_of_card_two _ m.card_fixed)
  exact (le_inf (normalizer_component_le_module_at h structural D m)
    (normalizer_le_normalizer_centralizer L)).trans inf_normalizer_le_normalizer_inf

/-- The full fixed-line centralizer equals M, using maximal two-local uniqueness. -/
theorem fixed_centralizer_eq_normalizer_at :
    centralizer (V ⊓ centralizer (L : Set G) : Set G) = normalizer (L : Set G) := by
  apply le_antisymm ?_ (normalizer_component_le_fixed_centralizer_at h structural D m)
  apply (Subgroup.centralizer_le_normalizer _).trans
  apply normalizer_le_of_unique_maximalTwoLocal
    (h.source_normalizer_maximal_unique_at structural
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).2
    ((T.isPGroup'.to_le D.le_sylow).to_le inf_le_left) m.fixed_ne_bot
  exact ((sup_le L.le_normalizer (h.source_sylow_normalizes_at structural)).trans
    (normalizer_component_le_fixed_centralizer_at h structural D m)).trans
      (Subgroup.centralizer_le_normalizer _)

/-- Every nonidentity element of the actual fixed line has full centralizer M. -/
theorem fixed_generator_centralizer_at {d : G}
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
    _ = normalizer (L : Set G) := fixed_centralizer_eq_normalizer_at h structural D m

/-- D5 holds because the actual fixed line lies in the center of M. -/
theorem normalizer_center_ne_bot_at : center (normalizer (L : Set G)) ≠ ⊥ := by
  obtain ⟨d, hd1⟩ := ne_bot_iff_exists_ne_one.mp m.fixed_ne_bot
  have hd : (d : G) ≠ 1 := fun he => hd1 (Subtype.ext he)
  let x : normalizer (L : Set G) :=
    ⟨d.val, D.sylow_normalizes_component (D.le_sylow d.property.1)⟩
  have hx : x ∈ center (normalizer (L : Set G)) := by
    rw [mem_center_iff]
    intro y
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp
      ((fixed_generator_centralizer_at h structural D m d.property hd).symm ▸ y.property)
  intro he
  have hx1 := mem_bot.mp (he ▸ hx)
  exact hd (congrArg Subtype.val hx1)

/-- The actual original module supplies the32-element first-vertex core bound. -/
theorem normalizer_twoCore_card_at : 32 ≤ Nat.card (pCore 2 (normalizer (L : Set G))) :=
  SolvableCentralizerC3.original_five_module_core_bound _ V
    (T.isPGroup'.to_le D.le_sylow)
    (D.le_sylow.trans D.sylow_normalizes_component)
    (normalizer_component_le_module_at h structural D m) m.card_module

omit D m in
/-- D4 is discharged from the same maximal two-local uniqueness as13.4.2. -/
theorem original_chamber_core_eq_bot_at (z : G) (H₀ : Subgroup G)
    (hout : ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G)) :
    ((T : Subgroup G).subgroupOf
      (SolvableCentralizerC3.generated (normalizer (L : Set G)) z H₀)).normalCore = ⊥ := by
  apply SolvableCentralizerC3.original_chamber_core_free _ H₀ T z T.isPGroup' hout
  intro N hN hne _ hn
  apply normalizer_le_of_unique_maximalTwoLocal
    (h.source_normalizer_maximal_unique_at structural
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).2 hN hne
  exact (sup_le L.le_normalizer (h.source_sylow_normalizes_at structural)).trans hn

/-- The earlier escaping vector lies outside the actual fixed line. Its later
placement in V∩Ω₁Z(T) is a separate13.3.5/13.4 geometric step. -/
theorem exists_nonfixed_escape_at (h₀ : Hypothesis1331 T L)
    (earlier : Theorem12213At KnownSimple.IsKnownSimple T) :
    ∃ z ∈ V, z ≠ 1 ∧ z ∉ centralizer (L : Set G) ∧
      ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G) := by
  have hescape : ∃ z ∈ V, z ≠ 1 ∧
      ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G) := by
    rcases earlier L V h D with
      hv | ⟨d, hd, _, he⟩ | ⟨_, he⟩ | ⟨_, he⟩
    · exact hv
    · exact (h₀.hypothesis1311.no_linear (d + 1)
        (by rcases hd with rfl | rfl <;> omega) he).elim
    · exact (h₀.hypothesis1311.no_A9 he).elim
    · exact (h₀.hypothesis1311.no_M24 he).elim
  obtain ⟨z, hz, hz1, hout⟩ := hescape
  refine ⟨z, hz, hz1, ?_, hout⟩
  intro hf
  exact hout (fixed_generator_centralizer_at h structural D m ⟨hz, hf⟩ hz1).le

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource
