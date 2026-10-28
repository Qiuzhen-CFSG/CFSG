module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Reduction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.PSLIndex
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.Commutator

/-!
# The actual two-core identity in the prime PSL₂ branch

For the perfect normal component with prime PSL₂ two-core quotient,
the solvable radical of KT is its two-core. The preceding 11.4.1(3)
containment puts R₁ inside that core. The reverse inclusion holds in
every Sylow overgroup L₁T inside KT. Thus R₁=O₂(KT), and the original
weak-closure normalizer bound excludes the branch.

This reuses the proved radical calculation and assumes neither the
core identity nor a new model-specific signalizer condition.
Source: Aschbacher--Smith, 11.5.1, printed p.779.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- The source prime-PSL₂ identity from the preceding radical containment. -/
theorem prime_radical_eq_core (h : Comparison.EarlierGeometry E)
    (hT : (T : Subgroup G) ≤ E.G₁)
    (hR : E.R₁ ≤ (solvableRadical (E.K ⊔ (T : Subgroup G) : Subgroup G)).map
      (E.K ⊔ (T : Subgroup G)).subtype)
    {p : ℕ} (hp : 3 < p) (hm : ClassicalGroup.IsPSL (E.K ⧸ pCore 2 E.K) 2 p) :
    E.R₁ = (E.K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let : Group.IsPerfect E.K := Radical.relative_component_perfect h.line_component
  have he := Radical.join_radical_eq_core_of_psl2 T E.K
    (hT.trans E.G₁_normalizes_K) hp hm
  rw [he] at hR
  exact le_antisymm hR (Radical.join_core_le_local_core T E.L₁ E.K
    (le_conjugateSpanBy _ _))

/-- The prime branch now feeds the literal weak-closure contradiction with
the previously missing model-specific core identity discharged. -/
theorem prime_impossible (h : Comparison.EarlierGeometry E)
    (hT : (T : Subgroup G) ≤ E.G₁)
    (hR : E.R₁ ≤ (solvableRadical (E.K ⊔ (T : Subgroup G) : Subgroup G)).map
      (E.K ⊔ (T : Subgroup G)).subtype)
    {p : ℕ} (hp : 3 < p) (hm : ClassicalGroup.IsPSL (E.K ⧸ pCore 2 E.K) 2 p)
    (hout : ¬ E.K ≤ E.M)
    (hweak : normalizer (ChapterE.indexedWeakClosure V E.R₁ 0 : Set G) ≤ E.M) : False :=
  prime_case_impossible E (prime_radical_eq_core E h hT hR hp hm) hout hweak

/-- The same prime-branch exclusion on the original marked field flag. -/
theorem ofFlag_prime_impossible
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hR : (ofFlag S f X z H).R₁ ≤
      (solvableRadical ((ofFlag S f X z H).K ⊔ (T : Subgroup G) : Subgroup G)).map
        ((ofFlag S f X z H).K ⊔ (T : Subgroup G)).subtype)
    {p : ℕ} (hp : 3 < p)
    (hm : ClassicalGroup.IsPSL ((ofFlag S f X z H).K ⧸ pCore 2 (ofFlag S f X z H).K) 2 p)
    (hout : ¬ (ofFlag S f X z H).K ≤ normalizer (L : Set G))
    (hweak : normalizer (ChapterE.indexedWeakClosure V (f.Ri 0) 0 : Set G) ≤
      normalizer (L : Set G)) : False :=
  prime_impossible _ h (f.invariant 0) hR hp hm hout hweak

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside
