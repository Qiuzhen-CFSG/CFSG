module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.InnerAction.LocalFamily.Star

/-!
# The actual inner-action residual belongs to Y_z

The residual of the full geometric-parabolic preimage is a C-component
relative to D Tᵥ, has a nontrivial local two-core, and has quasisimple
star quotient modulo its two-core. The transport in `InnerAction.Lift`
supplies both normalizers and movement. Applying universal 13.6.16(3)
then proves every clause of the source family Y_z.

The geometric parabolic/model, the original R₂ action consequence and
universal 13.6.16(3) remain explicit earlier inputs. Neither local-family
membership nor star-quasisimplicity of the residual is assumed.

Source: Aschbacher–Smith, proof of 13.6.23, printed p.933/PDF p.950.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.InnerAction
open ComponentSelection
variable {G : Type*} [Group G] [Finite G]

/-- The two local and star inputs to the inner geometric contradiction,
proved for the same full-preimage residual used by that consumer. -/
theorem liftedResidual_local_and_star
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hY : K ∈ Yz L T z v)
    (hLK : Lv L v ≤ K) (hK : Tv T v ≤ normalizer (K : Set G))
    (hinner : plusImage K L T z v hL hz (Tv T v) ≤ plusImage K L T z v hL hz K)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (P : Subgroup (Gplus K L T z v hL hz))
    (hP : plusImage K L T z v hL hz (sourceParabolic K L T v) ≤ P)
    (eP : ((solvableResidual P).map P.subtype ⧸
      pCore 2 ((solvableResidual P).map P.subtype)) ≃* SL(3, ZMod 2)) :
    let D := liftedResidual K L T z v hL hz P
    D ∈ Chapter1.LIn (Gv v) (Tv T v) ∧
      IsQuasisimple (starImage z v D ⧸ pCore 2 (starImage z v D)) :=
  ⟨liftedResidual_mem_LIn K L T z v hL hz hY hLK hK hinner P hP eP,
    liftedResidual_star_quasisimple K L T z v hL hz hY hLK hK hR P eP⟩

/-- Apply universal 13.6.16(3) to the actual lifted residual, completing
its source-family membership without an Lᵥ-containment assumption. -/
theorem liftedResidual_mem_Yz
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hY : K ∈ Yz L T z v)
    (hLK : Lv L v ≤ K) (hK : Tv T v ≤ normalizer (K : Set G))
    (hinner : plusImage K L T z v hL hz (Tv T v) ≤ plusImage K L T z v hL hz K)
    (hmove : ¬ Lv L v ≤ centralizer ({z} : Set G))
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (h16 : ∀ A ∈ Chapter1.LIn (Gv v) (Tv T v),
      Tv T v ≤ normalizer (A : Set G) → ¬ A ≤ centralizer ({z} : Set G) →
      ⁅A, Stellmacher.elementaryAbelianMaxJ (Tv T v)⁆ = A)
    (P : Subgroup (Gplus K L T z v hL hz))
    (hP : plusImage K L T z v hL hz (sourceParabolic K L T v) ≤ P)
    (hquot : IsPGroup 2 (P ⧸ solvableResidual P))
    (eP : ((solvableResidual P).map P.subtype ⧸
      pCore 2 ((solvableResidual P).map P.subtype)) ≃* SL(3, ZMod 2)) :
    liftedResidual K L T z v hL hz P ∈ Yz L T z v := by
  let D := liftedResidual K L T z v hL hz P
  obtain ⟨hlocal, hstar⟩ :=
    liftedResidual_local_and_star K L T z v hL hz hY hLK hK hinner hR P hP eP
  obtain ⟨_, hn, hLN, hm, _⟩ :=
    liftedResidual_source_data K L T z v hL hz hY.1 hLK hK hinner hmove P hP hquot
  exact mem_Yz_of_invariant_generated D L T z v hlocal hn hLN hstar hm
    (h16 D hlocal hn hm)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.InnerAction
