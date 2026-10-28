module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.Setup
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.Preliminaries
public import Stellmacher.BaumannNormalizer
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# From the paired Borel geometry to the residual commutator bound

B.2.3(5) transfers the Baumann subgroup to C_{Tᵥ}(Ω₁(T₀)). Thus a
normalizer calculation for this centralizer puts the Borel in N_G(Baum(Tᵥ)).
The proved 13.6.4–5 deductions then place it in C_{M_V}(v).

The action on the actual subgroup V retains its centralizer kernel. Its
{2,3}-group image kills O^{2,3}(C_{M_V}(v)). Since the paired central
Suzuki cover is three-free, O²(B) lies in that residual and hence in C_M(V).
Mutual normalization puts [Lᵥ,O²(B)] in Lᵥ ∩ C_M(V), where the earlier
local module kernel bound puts it in O₂(Lᵥ).

The required intrinsic omega/normalizer geometry is explicitly conditional
here; neither its conclusion nor the subsequent cubic-action contradiction
is claimed as a source theorem. All residuals in the displayed chain are
superscript residuals, verified against printed p.927 / PDF p.944.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair
open Subgroup ChapterB Stellmacher
variable {G : Type*} [Group G]

/-- The source C_{M_V}(v), with M_V = N_G(V). -/
def localNormalizer (V : Subgroup G) (v : G) : Subgroup G :=
  normalizer (V : Set G) ⊓ Gv v

/-- Its literal conjugation action on V. -/
def localAction (V : Subgroup G) (v : G) : localNormalizer V v →* MulAut V :=
  V.normalizerMonoidHom.comp (inclusion inf_le_left)

theorem localAction_kernel (V : Subgroup G) (v : G) :
    (localAction V v).ker = (centralizer (V : Set G)).subgroupOf (localNormalizer V v) := by
  ext x
  change V.normalizerMonoidHom (inclusion inf_le_left x) = 1 ↔ _
  change inclusion inf_le_left x ∈ V.normalizerMonoidHom.ker ↔ _
  rw [normalizerMonoidHom_ker]
  rfl

variable [Finite G]

/-- B.2.3(5) needs normalization of the centralizer inside Tᵥ. It does
not license replacing Ω₁(T₀) by Ω₁(Z(T₀)) in a central cover. -/
theorem normalizes_baumann_of_omega (T K B : Subgroup G) (v : G)
    [IsElementaryAbelian 2 (omega T K v)]
    (hJ : elementaryAbelianMaxJ (Tv T v) ≤ centralizer (omega T K v : Set G))
    (hB : B ≤ normalizer
      ((Tv T v ⊓ centralizer (omega T K v : Set G) : Subgroup G) : Set G)) :
    B ≤ normalizer (baumann (Tv T v) : Set G) := by
  rw [lemma_B_2_3_5 (Tv T v) (omega T K v)
    ((omegaOneAmbient_le _).trans inf_le_left) hJ]
  exact hB.trans (by
    simpa only [baumann, thompsonAlpha, coe_inf] using
      normalizer_le_normalizer_baumann (Tv T v ⊓ centralizer (omega T K v : Set G)))

/-- Apply the established 13.6.4 and 13.6.5 implications to this Borel.
The hypotheses are the genuine earlier 13.2.4, 13.2.5 and 12.2.6 inputs. -/
theorem borel_le_localNormalizer {T K M V : Subgroup G} {v : G}
    (d : Marking T K v) (hKG : K ≤ Gv v)
    (hS : baumann T ≤ Tv T v)
    (h1325 : normalizer (baumann T : Set G) ≤ M)
    (h1226 : Mv M v ≤ normalizer (V : Set G))
    (hMV : normalizer (V : Set G) ≤ M)
    (hB : d.borel ≤ normalizer (baumann (Tv T v) : Set G)) :
    d.borel ≤ localNormalizer V v := by
  have ho : orbit T K v ≤ Gv v :=
    conjugateSpanBy_le hKG (inf_le_right.trans (Gv v).le_normalizer)
  have hBaum := (baumann_and_thompson_centralizer T v hS).1
  have hBN : d.borel ≤ normalizer (baumann T : Set G) := by rwa [hBaum]
  obtain ⟨hcontrol, he⟩ := baumann_normalizer_control T M V v h1325 h1226 hMV
  have hc := (le_inf (d.borel_le_orbit.trans ho) hBN).trans hcontrol
  rwa [he] at hc

/-- The actual action kernel supplies the second residual containment. -/
theorem local_piResidual_le_centralizer (M V : Subgroup G) (v : G)
    (hMV : normalizer (V : Set G) ≤ M)
    (haction : IsPiGroup twoThreePrimes (localAction V v).range) :
    (piResidual twoThreePrimes (localNormalizer V v)).map (localNormalizer V v).subtype ≤
      M ⊓ centralizer (V : Set G) := by
  have hk := piResidual_le_ker_of_range twoThreePrimes (localAction V v) haction
  rw [localAction_kernel] at hk
  rintro x ⟨y, hy, rfl⟩
  exact ⟨hMV y.property.1, hk hy⟩

/-- The exact superscript residual chain on printed p.927. Three-freeness
is proved from the genuine central quotient, retaining its two-group center. -/
theorem residual_chain {T K M V : Subgroup G} {v : G}
    (d : Marking T K v) (hZ : IsPGroup 2 (center (orbit T K v)))
    (hB : d.borel ≤ localNormalizer V v)
    (hMV : normalizer (V : Set G) ≤ M)
    (haction : IsPiGroup twoThreePrimes (localAction V v).range) :
    (pResidual 2 d.borel).map d.borel.subtype ≤
        (piResidual twoThreePrimes (localNormalizer V v)).map (localNormalizer V v).subtype ∧
      (piResidual twoThreePrimes (localNormalizer V v)).map (localNormalizer V v).subtype ≤
        M ⊓ centralizer (V : Set G) := by
  refine ⟨?_, local_piResidual_le_centralizer M V v hMV haction⟩
  have hh := map_mono (f := (localNormalizer V v).subtype)
    (map_twoResidual_le_piResidual (inclusion hB) (d.borel_three_free hZ))
  simpa only [map_map, subtype_comp_inclusion] using hh

/-- The commutator deduction from the earlier normalization and module
kernel facts. No commutator bound is assumed. -/
theorem commutator_le_twoCore {T K L M V : Subgroup G} {v : G}
    (d : Marking T K v) (hZ : IsPGroup 2 (center (orbit T K v)))
    (hB : d.borel ≤ localNormalizer V v)
    (hMV : normalizer (V : Set G) ≤ M)
    (haction : IsPiGroup twoThreePrimes (localAction V v).range)
    (hLC : Lv L v ≤ normalizer (M ⊓ centralizer (V : Set G) : Set G))
    (hCL : M ⊓ centralizer (V : Set G) ≤ normalizer (Lv L v : Set G))
    (hkernel : Lv L v ⊓ (M ⊓ centralizer (V : Set G)) ≤
      (pCore 2 (Lv L v)).map (Lv L v).subtype) :
    ⁅Lv L v, (pResidual 2 d.borel).map d.borel.subtype⁆ ≤
      (pCore 2 (Lv L v)).map (Lv L v).subtype := by
  obtain ⟨hr, hc⟩ := residual_chain d hZ hB hMV haction
  exact (commutator_mono le_rfl (hr.trans hc)).trans ((le_inf
    (le_normalizer_iff_commutator_le_left.mp hCL)
    (le_normalizer_iff_commutator_le_right.mp hLC)).trans hkernel)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair
