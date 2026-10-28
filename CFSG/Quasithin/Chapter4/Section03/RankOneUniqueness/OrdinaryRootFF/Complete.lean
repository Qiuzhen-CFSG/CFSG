module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF.OddFieldComparison

/-!
# The conditional ordinary-root failure-of-factorization contradiction

The complete action comparison identifies the secondary and point-local
images inside the original centralizer quotient. The exact action-kernel
calculation then gives U = O₂(J) and K_Z ≤ JQ. Applying these two proved
conclusions to the original root geometry gives the source contradiction.

Only the independently owned core and secondary inputs remain explicit:
qt-d-1222-ordinary-root-core and qt-d-1222-ordinary-root-secondary construct
them, and qt-d-1222-rankone-ordinary-root-ff retains their final discharge.
There is no classification, model-selection or prime-rank parameter.

Source: Aschbacher–Smith 4.3.6, printed p.615, the last two paragraphs.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} (m : OrdinarySymplecticMarking c n)

/-- Both terminal subgroup conclusions, with the original quotient kernel and root marking. -/
theorem module_and_containment (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hseed : conjugateSpanBy c.ordinaryModule m.second = m.second)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hKZ : conjugateSpanBy m.second KZ = KZ)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G)) :
    m.rootSpan = m.second.pCoreIn 2 ∧ KZ ≤ m.second ⊔ m.rootCore := by
  apply module_and_containment_of_image_eq m hn hr hUN hcore hseed hQ KZ
    (hK.trans (Subgroup.centralizer_le_normalizer _)) hKZ hquasi hnormal
  exact secondary_image_eq_second m hn h hr hUN hcore hQ KZ hK
    ((le_conjugateSpanBy _ _).trans_eq hKZ) hcomp hquasi hnormal

/-- The full conditional source contradiction, applying the two established
subgroup conclusions to the literal ordinary-root consumer. -/
theorem false_of_core_and_secondary
    (D : Chapter12.Section02.ChosenModule T L V) (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hT : (T : Subgroup G) ≤ m.rootNormalizer)
    (hseed : conjugateSpanBy c.ordinaryModule m.second = m.second)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hKZ : conjugateSpanBy m.second KZ = KZ)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G)) : False := by
  obtain ⟨hU,hle⟩ := module_and_containment m hn h hr hUN hcore hseed hQ
    KZ hK hcomp hKZ hquasi hnormal
  exact c.ordinary_false_of_root_module D hn m KZ hT hseed hU hQ hKZ hle hnormal

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF
