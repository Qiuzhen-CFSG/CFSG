module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.SourcePair
public import Theory.SpecificGroups.Suzuki.SylowSupplement

/-!
# The Sylow-normality premise for the original A₅–Suzuki pair

The Suzuki quotient has odd outer automorphism group. Therefore the original
ambient Sylow T factors as O₂(AT)(T ∩ A), and its Suzuki Borel normalizes T
by the elementary factorization argument in F.1.10(1). This proves the extra
Sylow-normality hypothesis of F.1.12 on the same groups used in13.6.27.

The final theorem constructs F.1.1 and this additional premise from the
original normal component. Exhaustive F.1.12 recognition, whose only
nonbinary Suzuki row pairs Sz(q) with PSL₂(q), is still an independent
source obligation; it is not asserted here.

Source: Aschbacher–Smith F.1.10–12, printed pp.262–264;5.2.4–6,
printed p.650;13.6.27, printed p.934.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
open ChapterF.Source BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G]

/-- The Suzuki Borel normalizes the original ambient Sylow, discharging
the additional Sylow-normality premise of source F.1.12. -/
theorem suzuki_borel_normalizes_sylow (A : Subgroup G) (T : Sylow 2 G)
    (hTA : (T : Subgroup G) ≤ normalizer (A : Set G))
    {m : ℕ} (hm : 0 < m) (e : (A ⧸ pCore 2 A) ≃* SuzukiMatrixGroup m) :
    ((T : Subgroup G).subgroupOf ((T : Subgroup G) ⊔ borel A (T : Subgroup G))).Normal := by
  apply normal_of_core_decomposition
  exact suzuki_quotient_sylow_factorization A T hTA hm e

/-- The original component supplies all genuine F.1.1 clauses and the
extra F.1.12 normality premise, on the unchanged ambient Sylow subgroup. -/
theorem source_A5_suzuki_pair_F112_inputs
    {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    {z : G} (hz : zpowers z = V₁)
    (D : Subgroup (centralizer ({z} : Set G))) [D.Normal]
    {m : ℕ} (hm : 0 < m)
    (e : (D ⧸ pCore 2 D) ≃* SuzukiMatrixGroup m)
    (hout : ¬ D.map (centralizer ({z} : Set G)).subtype ≤ normalizer (L : Set G))
    (h25 : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J →
      J ≤ normalizer (L : Set G)) :
    let A := D.map (centralizer ({z} : Set G)).subtype
    HypothesisF11 ![L,A] (T : Subgroup G) ∧
      ((T : Subgroup G).subgroupOf ((T : Subgroup G) ⊔ borel A (T : Subgroup G))).Normal := by
  dsimp only
  have hF := source_A5_suzuki_pair_F11 d hz D e hout h25
  refine ⟨hF, ?_⟩
  let eD := D.equivMapOfInjective (centralizer ({z} : Set G)).subtype
    (centralizer ({z} : Set G)).subtype_injective
  let eQ := QuotientGroup.congr _ _ eD (pCore_map_iso 2 eD)
  exact suzuki_borel_normalizes_sylow _ T (hF.S_normalizes 1) hm (eQ.symm.trans e)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
