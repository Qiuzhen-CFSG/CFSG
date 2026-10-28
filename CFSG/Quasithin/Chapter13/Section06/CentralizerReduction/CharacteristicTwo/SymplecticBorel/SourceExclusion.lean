module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.SourceEvenDegree
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.LocalInverter
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration

/-!
# The source symplectic contradiction in 13.6.6

The marked A₅ residual is cubic and lies in the actual component Borel,
forcing even field degree. The completed field descent and Sylow-center
kernel therefore give the Baumann decomposition and Borel containment.
The marked module then constructs the index-three centralizer and the same
Sylow element that centralizes its two-residual quotient while inverting a
cubic element of the Borel quotient. The full rank-two torus obstruction
gives the contradiction.

All maps are the existing literal component action, specified Sylow, Borel
embedding and quotient maps. The residual B_C remains O²(C_B(V)). Neither
Borel containment nor an index, inverter or cocycle conclusion is an input.
The source convention M = N_H(L) is retained in the 13.6.5 hypotheses.

This completes the symplectic exclusion from the earlier marked 13.6.2–5
configuration, whole-component identification and residual Borel placement.
Constructing those earlier source inputs, including I.1.3 when the available
model is initially only K/Z(K), remains with the existing component-reduction
and characteristic-two assembly owners. No assertion of the whole 13.6.6 is
made here. Source: Aschbacher–Smith, proof of 13.6.6, printed pp.927–928.

-/

public section
open Subgroup Theory.SpecificGroups.SymplecticFour BinaryPermutation
open BinaryPermutation.FiveCentralizerGeometry
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel.SourceExclusion
open A5Module LocalInverter
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {L V : Subgroup H}

/-- The actual normalized symplectic component is impossible in the marked
A₅ source configuration. Every local conclusion of the Borel argument is
constructed from the earlier source hypotheses. -/
theorem false_of_marked_symplectic_configuration
    (K : Subgroup H) (e : K ≃* Sp F)
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 (Sp F)) (s : Marking L V) (T : Subgroup H)
    (hk : s.action.ker = pCore 2 L)
    (ρ : normalizer (V : Set H) →* Equiv.Perm (Fin 5))
    (hρ : ∀ (u : normalizer (V : Set H)) (w : Space),
      MulAut.conj (u : H) (s.map (Multiplicative.ofAdd w)) =
        s.map (Multiplicative.ofAdd (coreRepresentation (Fin 5) (ρ u) w)))
    (hagree : ∀ (l : L) (hl : (l : H) ∈ normalizer (V : Set H)),
      ρ ⟨l, hl⟩ = (s.action l).val)
    (hTL : T ≤ normalizer (L : Set H))
    (P : Sylow 2 (Gv (markedV s)))
    (hP : (P : Subgroup (Gv (markedV s))).map (Gv (markedV s)).subtype =
      Tv T (markedV s))
    (hK : K ≤ Gv (markedV s))
    (hTK : Tv T (markedV s) ≤ normalizer (K : Set H))
    (hSylow : (localSylow K e S : Subgroup K).map K.subtype =
      Tv T (markedV s) ⊓ K)
    (hD : Lv L (markedV s) ≤ borelIn K e S)
    (h1364 : CFSG.Quasithin.ChapterB.baumann T =
      CFSG.Quasithin.ChapterB.baumann (Tv T (markedV s)))
    (h1365 : Gv (markedV s) ⊓
        normalizer (CFSG.Quasithin.ChapterB.baumann T : Set H) ≤
      Mv (normalizer (L : Set H)) (markedV s))
    (hlocal : Mv (normalizer (L : Set H)) (markedV s) =
      normalizer (V : Set H) ⊓ Gv (markedV s)) : False := by
  have hB := SourceEvenDegree.source_borel_containment_of_marked_residual
    K e hF hn s T (normalizer (L : Set H)) P hP hK hTK S hSylow hD
    h1364 h1365 hlocal
  obtain ⟨_, hindex, _, _, hA, x, _, _, hfix, b, horder, hinv⟩ :=
    local_index_and_inverter K e hF hn S s T hk ρ hρ hagree hTL P hP hTK hSylow
      hD hlocal hB.2
  exact no_inverter_of_centralizer_index K e hF hn S
    (localActors K T (markedV s)) hA
    (localActors_stabilize K e S T (markedV s) hTK hSylow)
    V x hindex hfix b horder hinv

/-- Application to the actual producer of the marked 13.6.2–5 configuration.
The flag's relabelling also transports the full normalizer action; the local
Sylow, Baumann identity and normalizer control are constructed by the existing
source theorem. Only the component model, its specified Sylow and residual
Borel placement remain for the normalized-component owner. -/
theorem false_of_earlier_local_source
    {T : Sylow 2 H} {V₁ V₂ : Subgroup H}
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup H)
    (earlier : EarlierLocal T L (normalizer (L : Set H)) V V₂ V₃
      (markedZ d.flag.module))
    (hcounter : IsA5Counterexample H)
    (hfusion : ControlsFusionOfZ d.flag.module)
    (K : Subgroup H) (e : K ≃* Sp F)
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 (Sp F))
    (hK : K ≤ Gv (markedV d.flag.module))
    (hTK : Tv (T : Subgroup H) (markedV d.flag.module) ≤ normalizer (K : Set H))
    (hSylow : (localSylow K e S : Subgroup K).map K.subtype =
      Tv (T : Subgroup H) (markedV d.flag.module) ⊓ K)
    (hD : Lv L (markedV d.flag.module) ≤ borelIn K e S) : False := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set H)) V₃
    earlier hcounter hfusion
  obtain ⟨g, hg⟩ := d.flag_relabel
  refine false_of_marked_symplectic_configuration K e hF hn S d.flag.module
    (T : Subgroup H) d.flag.action_kernel (d.relabel g).normalizerAction ?_ ?_
    earlier.T_normalizes_L c.reductions.centralizerSylow c.reductions.sylow_image
    hK hTK hSylow hD c.reductions.baumann_eq c.reductions.normalizer_baumann
    c.reductions.local_centralizer
  · intro u w
    rw [hg]
    exact (d.relabel g).normalizer_equivariant u w
  · intro l hl
    rw [hg]
    exact (d.relabel g).action_agrees l hl

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel.SourceExclusion
