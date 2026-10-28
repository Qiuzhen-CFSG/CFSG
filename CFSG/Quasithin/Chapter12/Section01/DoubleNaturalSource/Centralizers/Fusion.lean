module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ModelGeometry
public import CFSG.Quasithin.ChapterA.Section01.Elementary

/-!
# From pure-vector fusion to commuting intersecting conjugates

A.1.7 replaces a conjugate containing w by one conjugated by C_G(w).
Both copies of W then lie in the closure under that centralizer. If this
closure is abelian, the copies commute. This proves the implication from
12.1.5(2) and 12.1.6(1) to 12.1.6(2) on the literal doubled orbit.
The fusion and abelian-closure premises remain separate source obligations.

Source: Aschbacher--Smith, combined manuscript, printed p.791.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  (B : DoubledBranch T L V n)

/-- The literal fusion premise of source 12.1.5(2), restricted to pure vectors. -/
def PureFusion : Prop :=
  ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
    (B.coordinates w).toAdd.2 = 0 →
    ChapterA.fusionSet (componentOrbit V (T : Subgroup G)) (w : G) =
      ChapterA.normalizerFusionSet (componentOrbit V (T : Subgroup G)) (w : G)

/-- Source 12.1.6(1), using the closure under the full ambient point centralizer. -/
def PureCentralizerClosureAbelian : Prop :=
  ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
    (B.coordinates w).toAdd.2 = 0 →
    IsMulCommutative (componentOrbit (componentOrbit V (T : Subgroup G))
      (centralizer ({(w : G)} : Set G)))

theorem pureIntersectionCentralizes_of_fusion_of_abelianClosure
    (hf : B.PureFusion) (hc : B.PureCentralizerClosureAbelian) :
    B.PureIntersectionCentralizes := by
  intro g w hw hp hmem
  obtain ⟨c, hcC, he⟩ :=
    (ChapterA.lemma_A_1_7_1 (componentOrbit V (T : Subgroup G)) (w : G) w.property).mp
      (hf w hw hp) _ ⟨⟨g, rfl⟩, hmem⟩
  let U := componentOrbit (componentOrbit V (T : Subgroup G))
    (centralizer ({(w : G)} : Set G))
  let : IsMulCommutative U := hc w hw hp
  have hWU : componentOrbit V (T : Subgroup G) ≤ U := le_componentOrbit _ _
  have hWgU : (componentOrbit V (T : Subgroup G)).map (MulAut.conj g).toMonoidHom ≤ U := by
    rw [he]
    exact le_iSup (fun a : centralizer ({(w : G)} : Set G) =>
      (componentOrbit V (T : Subgroup G)).map (MulAut.conj (a : G)).toMonoidHom) ⟨c, hcC⟩
  exact le_bot_iff.mp ((commutator_mono hWU hWgU).trans
    (commutator_self_eq_bot_iff.mpr (inferInstance : IsMulCommutative U)).le)
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
