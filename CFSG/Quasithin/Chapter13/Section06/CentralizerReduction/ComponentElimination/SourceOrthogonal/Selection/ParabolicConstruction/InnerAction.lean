module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.Marking
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.Replacement
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.InnerAction.Lift
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.InnerAction.Comparison
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.InnerAction.Geometry
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.InnerAction.LocalFamily

/-!
# The geometric-residual contradiction in the inner-action branch

A marked minimal parabolic in the prescribed SL₄(2) or SL₅(2) model is
enlarged by an adjacent node and lifted through the actual plus map. Its
solvable residual lies in K, is normalized by Tᵥ and Lᵥ, and moves z.
Its proved local-family membership and star-quasisimplicity allow universal
13.6.16(3) to give every clause of Y_z. The earlier
R₂ input then makes its own plus image a nontrivial quotient of the geometric
L₃(2) quotient. The explicit restriction map from W_K to W_D identifies that
image with L₃(2), contradicting the genuine universal 13.6.22 exclusion.

The final theorem constructs the geometric parabolic and discharges its
local and star properties, proving that the original actor is outside K⁺.
Only the earlier source inputs remain explicit: the cubic quotient and
movement of Lᵥ, its containment in K, invariance of K, the reduced linear
model, universal 13.6.16(3), the R₂ action consequence, and universal 13.6.22.
No clause of 13.6.23 is an input. The parent parabolic-construction module
retains assembly with `middle_node_of_outside_actor`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.6.23,
printed p.933/PDF p.950, using the minimal-parabolic argument on p.932.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.InnerAction
open ComponentSelection
variable {G : Type*} [Group G] [Finite G]

/-- Apply the earlier source theorems to the actual lifted residual. The model
premise concerns the geometric residual; the replacement's own model is proved. -/
theorem false_of_inner_geometric_parabolic
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hY : K ∈ Yz L T z v)
    (hLK : Lv L v ≤ K) (hK : Tv T v ≤ normalizer (K : Set G))
    (hinner : plusImage K L T z v hL hz (Tv T v) ≤ plusImage K L T z v hL hz K)
    (hmove : ¬ Lv L v ≤ centralizer ({z} : Set G))
    (h16 : ∀ A ∈ Chapter1.LIn (Gv v) (Tv T v),
      Tv T v ≤ normalizer (A : Set G) → ¬ A ≤ centralizer ({z} : Set G) →
      ⁅A, Stellmacher.elementaryAbelianMaxJ (Tv T v)⁆ = A)
    (hR : ∀ A ∈ Yz L T z v, pCore 2 (Gplus A L T z v hL hz) = ⊥)
    (hsmall : ∀ A ∈ Yz L T z v,
      ¬ Nonempty (plusImage A L T z v hL hz A ≃* SL(3, ZMod 2)))
    (P : Subgroup (Gplus K L T z v hL hz))
    (hP : plusImage K L T z v hL hz (sourceParabolic K L T v) ≤ P)
    (hquot : IsPGroup 2 (P ⧸ solvableResidual P))
    (eP : (((solvableResidual P).map P.subtype) ⧸
      pCore 2 ((solvableResidual P).map P.subtype)) ≃* SL(3, ZMod 2))
    (hlocal : liftedResidual K L T z v hL hz P ∈ Chapter1.LIn (Gv v) (Tv T v))
    (hq : Theory.GroupTheory.IsQuasisimple
      (starImage z v (liftedResidual K L T z v hL hz P) ⧸
        pCore 2 (starImage z v (liftedResidual K L T z v hL hz P)))) : False := by
  let D := liftedResidual K L T z v hL hz P
  obtain ⟨hDK, hn, hLN, hm, _⟩ :=
    liftedResidual_source_data K L T z v hL hz hY.1 hLK hK hinner hmove P hP hquot
  have hYD : D ∈ Yz L T z v :=
    mem_Yz_of_invariant_generated D L T z v hlocal hn hLN hq hm
      (h16 D hlocal hn hm)
  have hcore : pCore 2 (plusImage D L T z v hL hz D) = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 (plusImage_K_subnormal D L T z v hL hz hYD), hR D hYD]
    exact (plusImage D L T z v hL hz D).ker_subtype
  let a : plusImage K L T z v hL hz D ≃* ((solvableResidual P).map P.subtype) :=
    MulEquiv.subgroupCongr (liftedResidual_plusImage K L T z v hL hz P)
  let e := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans eP
  exact hsmall D hYD (ownPlus_model_of_old_quotient K D L T z v hL hz hDK hcore hm e)

/-- The inner-action branch of 13.6.23 is impossible. The adjacent-node
parabolic, its moving residual's local and star properties, and its own
SL₃(2) plus model are all constructed from the earlier source inputs. -/
theorem outside_actor_of_source_linear_model
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hY : K ∈ Yz L T z v)
    (hLK : Lv L v ≤ K) (hK : Tv T v ≤ normalizer (K : Set G))
    (hc : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    (hmove : ¬ Lv L v ≤ centralizer ({z} : Set G))
    (h16 : ∀ A ∈ Chapter1.LIn (Gv v) (Tv T v),
      Tv T v ≤ normalizer (A : Set G) → ¬ A ≤ centralizer ({z} : Set G) →
      ⁅A, Stellmacher.elementaryAbelianMaxJ (Tv T v)⁆ = A)
    (hR : ∀ A ∈ Yz L T z v, pCore 2 (Gplus A L T z v hL hz) = ⊥)
    (hsmall : ∀ A ∈ Yz L T z v,
      ¬ Nonempty (plusImage A L T z v hL hz A ≃* SL(3, ZMod 2)))
    {m : ℕ} (hm : m = 3 ∨ m = 4)
    (e : plusImage K L T z v hL hz K ≃* SL(m + 1, ZMod 2)) :
    ¬ plusImage K L T z v hL hz (Tv T v) ≤ plusImage K L T z v hL hz K := by
  intro hinner
  obtain ⟨P, hP, _, hquot, ⟨eP⟩⟩ :=
    Geometry.exists_source_geometric_parabolic K L T z v hL hz hY.1 hLK hc hmove hm e
  obtain ⟨hlocal, hstar⟩ :=
    liftedResidual_local_and_star K L T z v hL hz hY hLK hK hinner (hR K hY) P hP eP
  exact false_of_inner_geometric_parabolic K L T z v hL hz hY hLK hK hinner hmove
    h16 hR hsmall P hP hquot eP hlocal hstar

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.InnerAction
