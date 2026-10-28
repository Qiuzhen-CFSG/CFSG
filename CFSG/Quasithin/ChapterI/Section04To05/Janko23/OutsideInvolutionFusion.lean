module
public import Theory.GroupTheory.MinusExtraspecialA5Fusion
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.LocalStructure
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!
# Outside-core involution fusion in the Janko centralizer

Under the literal `HTypeAt z` hypotheses, the local core F*(C_G(z)) is
O₂(C_G(z)), is isomorphic to the concrete minus extraspecial model, and is
self-centralizing by generalized-Fitting self-centralization. The actual
quotient equivalence with A₅ therefore meets every premise of the reusable
extension theorem. Ambient exclusions are transported along the subgroup
inclusion, while the resulting conjugacy remains inside C_G(z).

This is the local theorem 46.11 of Aschbacher, *Sporadic Groups* (1994),
printed p.255. It requires neither global simplicity nor an involution-class
count. The separate two-class source assembly remains with `LocalFusion`.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Janko23.HTypeAt
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Aschbacher 46.11: all involutions outside the core are conjugate within
 the literal centralizer H = C_G(z). -/
public theorem outside_involutions_isConj (h : HTypeAt z)
    (u v : involutionCentralizer z) (hu : orderOf u = 2) (hv : orderOf v = 2)
    (huQ : (u : G) ∉ ambientCore z) (hvQ : (v : G) ∉ ambientCore z) :
    IsConj u v := by
  have huQ' : u ∉ localCore z := fun hu => huQ (mem_map_of_mem _ hu)
  have hvQ' : v ∉ localCore z := fun hv => hvQ (mem_map_of_mem _ hv)
  have he : Nonempty (pCore 2 (involutionCentralizer z) ≃* MinusExtraspecial.Model) := by
    rw [← h.core_eq_pCore]
    exact h.core_equiv
  have hA : Nonempty ((involutionCentralizer z ⧸ pCore 2 (involutionCentralizer z)) ≃*
      alternatingGroup (Fin 5)) := by
    exact ⟨(QuotientGroup.quotientMulEquivOfEq h.core_eq_pCore.symm).trans
      h.quotient_equiv.some⟩
  have hc : centralizer (pCore 2 (involutionCentralizer z) : Set (involutionCentralizer z)) ≤
      pCore 2 (involutionCentralizer z) := by
    rw [← h.core_eq_pCore]
    exact centralizer_generalizedFitting_le _
  apply MinusExtraspecial.pCore_outside_involutions_isConj he hc hA u v hu hv
  · rwa [← h.core_eq_pCore]
  · rwa [← h.core_eq_pCore]
end CFSG.Quasithin.Janko23.HTypeAt
