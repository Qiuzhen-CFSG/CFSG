module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointOrdinaryOnlyHeld
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointOrdinaryHeldExclusion
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointOrdinaryAt

/-!
# The original ordinary triple-six point identification

The original ordinary closure has exactly the original field point as center,
and quotient by that unchanged four-group is PSL3Four. The final theorem
obtains the ordinary component from the original escaping configuration.

Source: Aschbacher--Smith 12.7.5, printed p. 840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

theorem original_tripleSix_point_ordinary_identification_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (J : Subgroup (centralizer ({(t : G)} : Set G)))
    (hJ : IsComponent (centralizer ({(t : G)} : Set G)) J) :
    let H := centralizer ({(t : G)} : Set G)
    let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
    let B := conjugateSpanBy Lt H
    let Vt := tripleSixPoint D a t
    centerIn B = Vt ∧ Vt.subgroupOf B = center B ∧
      ∃ hn : (Vt.subgroupOf B).Normal, letI := hn
        Nonempty ((B ⧸ Vt.subgroupOf B) ≃* Matrix.PSL3Four.PSL) := by
  have hs := original_tripleSix_point_ordinary_module_structure_or_held_at
    h structural D a t ht heven J hJ
  dsimp only at hs ⊢
  rcases hs with hs | ⟨e⟩
  · exact hs
  · exact (original_tripleSix_point_ordinary_not_held_at h structural D a t ht heven J hJ e.some).elim

theorem original_tripleSix_point_identification_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hout : ¬ centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G)) :
    let H := centralizer ({(t : G)} : Set G)
    let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
    let B := conjugateSpanBy Lt H
    let Vt := tripleSixPoint D a t
    IsComponent H (B.subgroupOf H) ∧ centerIn B = Vt ∧ Vt.subgroupOf B = center B ∧
      ∃ hn : (Vt.subgroupOf B).Normal, letI := hn
        Nonempty ((B ⧸ Vt.subgroupOf B) ≃* Matrix.PSL3Four.PSL) := by
  let H := centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  let B := conjugateSpanBy Lt H
  have hOrd := original_tripleSix_point_ordinary_at h structural D a t ht heven hout
  exact ⟨hOrd.1,original_tripleSix_point_ordinary_identification_at h structural D a t ht heven
    (B.subgroupOf H) hOrd.1⟩

end CFSG.Quasithin.Chapter12.Section07
