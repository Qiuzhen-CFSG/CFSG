module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.Inputs
public import Stellmacher.BaumannMap
public import Theory.GroupTheory.TINormalizerControl
public import Mathlib.Order.Minimal

/-!
# Local reductions from the earlier A₅ source statements

The second maximal two-local over T supplies a member of H_*(T,M) by
finite descent. Earlier 13.3.5 makes it centralize Z; uniqueness from
13.3.2 then forces C_Z(L) = C_T(L) = 1 and gives C_G(z) outside M.
The 13.5.10/12 implications give all required abelian conjugate spans.
Both alternatives of 13.2.4 imply Baum(T) ≤ C_T(v). Transporting its
characteristic Baumann subgroup promotes the local Sylow index to an
actual Sylow subgroup of C_G(v). The TI statement 12.2.6 and 13.2.5 give
normalizer control. The constructed geometry supplies N_G(Vᵥ) ≤ C_G(v).

This is the local-group portion of the configuration. Its construction
still takes a flag marking and the local module index explicitly. The
alignment, residual natural module, and central image of a require the
separate configuration constructions before the full source-only result
can be asserted. No characteristic-two conclusion is claimed here.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed
pp.926–928, with the earlier statements enumerated in `Inputs`.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open Subgroup Stellmacher ChapterB A5Module
variable {G : Type*} [Group G] [Finite G]

/-- The local-group portion of the configuration, on its literal subgroups. -/
structure LocalReductions (T : Sylow 2 G) (L M V : Subgroup G) (z v : G) where
  outsideLocal : Subgroup G
  outside_mem : outsideLocal ∈ Chapter3.HStar (T : Subgroup G) M
  outside_le : outsideLocal ≤ Gv z
  centralizer_outside : ¬ Gv z ≤ M
  abelian_span : IsMulCommutative (conjugateSpanBy V (Gv z))
  abelian_local_spans : ∀ H : Subgroup G, H ≤ Gv z → IsMulCommutative (conjugateSpanBy V H)
  omega_centralizer : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥
  sylow_centralizer : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥
  centralizerSylow : Sylow 2 (Gv v)
  sylow_image : (centralizerSylow : Subgroup (Gv v)).map (Gv v).subtype = Tv (T : Subgroup G) v
  checked_sylow_image : (centralizerSylow : Subgroup (Gv v)).map
    (QuotientGroup.mk' (vLine v)) = (checkedSylowMap (T : Subgroup G) v).range
  baumann_eq : baumann (T : Subgroup G) = baumann (Tv (T : Subgroup G) v)
  thompson_eq : elementaryAbelianMaxJ (T : Subgroup G) = elementaryAbelianMaxJ (Tv (T : Subgroup G) v)
  normalizer_baumann : Gv v ⊓ normalizer (baumann (T : Subgroup G) : Set G) ≤ Mv M v
  local_centralizer : Mv M v = normalizer (V : Set G) ⊓ Gv v
  normalizer_span : normalizer (Vv L z v : Set G) ≤ Gv v

omit [Finite G] in
/-- 13.2.4(2) supplies the Baumann containment in both of its source alternatives. -/
theorem baumann_le_Tv_of_alternatives (T : Sylow 2 G) (V V₂ : Subgroup G)
    (v : G) (hv : v ∈ V) (hv₂ : v ∈ V₂)
    (halt : baumann (T : Subgroup G) ≤ (T : Subgroup G) ⊓ centralizer (V : Set G) ∨
      V ⊓ centralizer (baumann (T : Subgroup G) : Set G) = V₂) :
    baumann (T : Subgroup G) ≤ Tv (T : Subgroup G) v := by
  refine le_inf inf_le_left ?_
  intro t ht
  apply mem_centralizer_singleton_iff.mpr
  rcases halt with ha | hb
  · exact (mem_centralizer_iff.mp (ha ht).2 v hv).symm
  · have hvc : v ∈ V ⊓ centralizer (baumann (T : Subgroup G) : Set G) := hb.symm ▸ hv₂
    exact mem_centralizer_iff.mp hvc.2 t ht

/-- Earlier 3.3.2(2) supplies another maximal two-local over T. Finite descent gives
an actual member of H_*(T,M), using its nontrivial two-core. -/
theorem exists_outside_local (T : Sylow 2 G) (M : Subgroup G)
    (hM : IsMaximalTwoLocal M)
    (hother : ∃ N : Subgroup G, IsMaximalTwoLocal N ∧ (T : Subgroup G) ≤ N ∧ N ≠ M) :
    ∃ H, H ∈ Chapter3.HStar (T : Subgroup G) M := by
  obtain ⟨N, hN, hTN, hNM⟩ := hother
  have hout : ¬ N ≤ M := fun h => hNM (le_antisymm h (hN.2 hM.1 h))
  obtain ⟨Q, hQ, hpQ, hNQ⟩ := hN.1
  have hQN : Q ≤ N := hNQ ▸ Q.le_normalizer
  have hcore : Q ≤ N.pCoreIn 2 := le_pCoreIn_of_normalizes hpQ hQN hNQ.le
  have hne : N.pCoreIn 2 ≠ ⊥ := fun he => hQ (le_bot_iff.mp (he ▸ hcore))
  obtain ⟨H, _, hH⟩ := exists_minimal_le_of_wellFoundedLT
    (fun H : Subgroup G => H ∈ Chapter1.HOver G (T : Set G) ∧ ¬ H ≤ M)
    N ⟨⟨hne, hTN⟩, hout⟩
  exact ⟨H, hH⟩

/-- Construct all local reductions once the separate flag calculation supplies
the local Sylow index. The full Sylow witness is constructed here by the
characteristic Baumann normalizer argument. -/
theorem localReductions_of_flag
    (T : Sylow 2 G) (L M V V₁ V₂ V₃ : Subgroup G)
    (f : FlagMarking T L V V₁ V₂)
    (e : EarlierLocal T L M V V₂ V₃ (markedZ f.module))
    (hcounter : IsA5Counterexample G)
    (hlocal : ¬ 2 ∣ (Tv (T : Subgroup G) (markedV f.module)).relIndex
      (normalizer (V : Set G) ⊓ Gv (markedV f.module)))
    (hfusion : ControlsFusionOfZ f.module) :
    Nonempty (LocalReductions T L M V (markedZ f.module) (markedV f.module)) := by
  have hMmem : M ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N} := by
    rw [e.maximal_overgroups]
    exact Set.mem_singleton M
  have hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N → N = M := by
    intro N hN hle
    have hm : N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N} := ⟨hN, hle⟩
    rw [e.maximal_overgroups] at hm
    exact hm
  obtain ⟨H, hH⟩ := exists_outside_local T M hMmem.1 e.other_local
  have hmin : Minimal (fun Y => Y ∈ Chapter1.HOver G (T : Set G) ∧ ¬ Y ≤ M) H := hH
  have hout : ¬ H ≤ M := hmin.prop.2
  have hHZ : H ≤ Gv (markedZ f.module) := by
    intro h hh
    exact mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_iff.mp (e.outside_centralizes H hH hh)
        (markedZ f.module) f.z_central).symm)
  have hZ := centralizer_omega_eq_bot_of_earlier_source (T : Subgroup G) L M H
    T.isPGroup' hunique hout (e.outside_centralizes H hH)
  have hCT := centralizer_T_eq_bot_of_omega (T : Subgroup G) L T.isPGroup'
    e.T_normalizes_L hZ
  have habel := abelian_spans_of_earlier_source V V₃ (markedZ f.module)
    hcounter e.nonabelian_classification e.span_equivalence
  have hv : markedV f.module ∈ V := map_mem f.module _
  have hS := baumann_le_Tv_of_alternatives T V V₂ (markedV f.module) hv
    f.vector_mem e.baumann_alternatives
  have hSJ := baumann_and_thompson_centralizer (T : Subgroup G) (markedV f.module) hS
  have hMV : Mv M (markedV f.module) ≤ normalizer (V : Set G) :=
    inf_elementCentralizer_le_normalizer_of_trivial_intersections
      e.trivial_intersections hv (markedV_ne_one f.module)
  have hcontrol := baumann_normalizer_control (T : Subgroup G) M V
    (markedV f.module) e.baumann_normalizer hMV e.module_normalizer
  let B : Subgroup (Tv (T : Subgroup G) (markedV f.module)) := baumann ⊤
  let : B.Characteristic := baumann_characteristic
  have hB : B.map (Tv (T : Subgroup G) (markedV f.module)).subtype =
      baumann (Tv (T : Subgroup G) (markedV f.module)) := by
    simpa only [B, baumann, thompsonAlpha, ← MonoidHom.range_eq_map, range_subtype] using
      baumann_map_injective (Tv (T : Subgroup G) (markedV f.module)).subtype
        (Tv (T : Subgroup G) (markedV f.module)).subtype_injective ⊤
  have hBN : normalizer (B.map (Tv (T : Subgroup G) (markedV f.module)).subtype : Set G) ≤ M := by
    rw [hB, ← hSJ.1]
    exact e.baumann_normalizer
  have hlocal' : ¬ 2 ∣ (Tv (T : Subgroup G) (markedV f.module)).relIndex
      (Mv M (markedV f.module)) := by
    rw [hcontrol.2]
    exact hlocal
  obtain ⟨P, hP⟩ := exists_sylow_centralizer T M (markedV f.module) B hlocal' hBN
  exact ⟨{
    outsideLocal := H
    outside_mem := hH
    outside_le := hHZ
    centralizer_outside := fun h => hout (hHZ.trans h)
    abelian_span := habel.1
    abelian_local_spans := habel.2
    omega_centralizer := hZ
    sylow_centralizer := hCT
    centralizerSylow := P
    sylow_image := hP
    checked_sylow_image := checkedSylowMap_range (T : Subgroup G) (markedV f.module) P hP
    baumann_eq := hSJ.1
    thompson_eq := hSJ.2
    normalizer_baumann := hcontrol.1
    local_centralizer := hcontrol.2
    normalizer_span := normalizer_Vv_le_Gv_of_fusion f.module hfusion }⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
