module

public import CFSG.Quasithin.Chapter12.Section02.SourceHypotheses
public import CFSG.Quasithin.Chapter12.Section07.Preliminaries.Fusion
public import CFSG.Quasithin.Chapter12.Section07.Preliminaries.WeakClosure
public import CFSG.Quasithin.Chapter12.Section07.Preliminaries.SylowCentralizer

/-!
# Preliminary deductions in the Â₆ six-space case

The source-facing assembly retains the shared Hypothesis 12.2.3, the original
Sylow subgroup and Irr⁺ choice, and the literal normalizer M = N_G(L). It
combines the fusion/incidence arguments, weak-closure argument and Sylow
centralizer contradiction, conditional on the named earlier-source and
intrinsic module inputs. The rank input 12.7.10(2) still needs its independent
proof. No identification of either He or M₂₄ is used.

The component alternative 12.7.5, characteristic/block deductions 12.7.2(6),
12.7.4(3), 12.7.6, and the rank and parabolic results 12.7.10(2,5), 12.7.13
remain with their independent producers. This module does not yet assert all
preliminaries or Theorem 12.7.1.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
§12.7, printed pp.839–843 (PDF pp.856–860).
-/

public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07.Preliminaries
open ChapterE Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- A source-facing assembly of 12.7.9(2,3), 12.7.11 and 12.7.12, and the
literal t-core needed in 12.7.22(5). The shared Hypothesis 12.2.3 and original
Irr⁺ choice are retained. The exact earlier implications 12.2.2, 12.2.9(1),
12.4.1, the intrinsic module facts, and 12.7.10(2) remain explicit inputs.
In particular, M is N_G(L), and only M_t, not all of M, is required to
normalize V. This theorem does not assert either identification branch. -/
theorem source_t_branch_reductions (K : GroupClass.{u}) (T : Sylow 2 G)
    (L V V₂ : Subgroup G) [IsElementaryAbelian 2 V]
    (H : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (h1222 : Structural1222 K)
    (z t : G) (htV : t ∈ V) (htV₂ : t ∈ V₂)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hindex : 2 ∣ (centralizer ({t} : Set G)).relIndex L)
    (hbranch : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hMt : normalizer (L : Set G) ⊓ centralizer ({t} : Set G) ≤
      normalizer (V : Set G))
    (horbits : ∀ v ∈ V, v ≠ 1 → ∃ l ∈ L,
      MulAut.conj l v = z ∨ MulAut.conj l v = t)
    (hr : (2 : ℕ∞) < globalR V) (hs : globalS V = 2)
    (hgeometry : ∀ A : Subgroup G, A ≤ (T : Subgroup G) →
      inducedAutomizer V A ∈ fixedSpaceFamily (automizerRepresentation V) 2 →
        subgroupCorank A (A ⊓ centralizer (V : Set G)) = 2 ∧ ⁅V, A⁆ = V₂)
    (hQ : (T : Subgroup G) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hmax : ∀ J : Subgroup G, J ≠ ⊤ →
      normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) ≤ J →
        J ≤ normalizer (L : Set G))
    (h129 : omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G) ≠ ⊥ →
      centralizer (omegaCenterIn (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (h124 : centralizer (omegaCenterIn (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) →
      (1 : ℕ∞) < globalS V →
        ∃ g : G, ⁅V, V.conjBy g⁆ ≠ ⊥ ∧ ⁅V, V.conjBy g⁆ ≤ V ⊓ V.conjBy g) :
    (∀ v ∈ V, ∀ g : G, v ∈ V.conjBy g →
      ∃ c ∈ centralizer ({v} : Set G), V.conjBy c = V.conjBy g) ∧
    (∀ g : G, t ∈ V.conjBy g → V.conjBy g = V) ∧
    indexedWeakClosure V (T : Subgroup G) 0 ≤
      (T : Subgroup G) ⊓ centralizer (V : Set G) ∧
    0 < globalW V (T : Subgroup G) ∧
    normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤ normalizer (L : Set G) ∧
    (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ ∧
    V ≤ (centralizer ({t} : Set G)).pCoreIn 2 := by
  let : IsSimpleGroup G := H.simpleQTKE.simple
  have hTL := (h1222 G T L H).1
  have hTN := ((h1222 G T L H).2.2 V D).1
  have hzt := not_isConj_of_even_local_orbit T L z t
    hzT hbranch hindex
  have huniq := unique_conjugate_through_t V L (normalizer (L : Set G)) z t
    D.normalizes htV horbits hzt hbranch hMt
  obtain ⟨hW, hw⟩ := weakClosure_zero_centralizes V (T : Subgroup G) V₂ t htV₂
    hTN hr hs hgeometry huniq
  have hnot : ¬ IsPGroup 2 G := by
    intro hp
    have hc := (inferInstance : (center G).Normal).eq_bot_or_eq_top.resolve_left
      hp.bot_lt_center.ne'
    exact H.simpleQTKE.nonabelian (center_eq_top_iff.mp hc)
  refine ⟨?_, huniq, hW, hw, ?_, ?_, le_t_centralizer_core V _ t htV hMt hbranch⟩
  · intro v hv g hg
    exact centralizer_transitive_on_conjugates V L z t D.normalizes horbits hzt hv g hg
  · exact weakClosure_zero_normalizer_le V ((L ⊔ (T : Subgroup G)).pCoreIn 2)
      (normalizer (L : Set G)) T D.ne_bot D.le_sylow (hW.trans_eq hQ)
      (hQ.symm ▸ inf_le_left) hnot hmax
  · exact sylow_centralizer_eq_bot_of_source_witness T L V (normalizer (L : Set G)) hTL hTN
      (by rw [hs]; decide) h129 h124 hW
end CFSG.Quasithin.Chapter12.Section07.Preliminaries
