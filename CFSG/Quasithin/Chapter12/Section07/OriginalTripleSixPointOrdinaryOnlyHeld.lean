module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointOrdinaryStructure
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointOrdinaryRu

/-!
# The sole remaining ordinary quotient at the original triple-six point

The original radical argument excludes Rudvalis. Thus the actual closure
has the required field-point center and PSL3Four quotient unless the
selected ordinary component has Held central quotient. That remaining
native Held inspection is stated explicitly.

Source: Aschbacher--Smith 12.7.5, printed p.840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The original closure has the stated center and central quotient, with
only the actual Held component alternative left to exclude. -/
theorem original_tripleSix_point_ordinary_structure_or_held_at
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
    (centerIn B = tripleSixPoint D a t ∧
      Nonempty ((B ⧸ center B) ≃* Matrix.PSL3Four.PSL)) ∨
      Nonempty ((J ⧸ center J) ≃* Held.He) := by
  rcases original_tripleSix_point_ordinary_structure_at h structural D a t ht heven J hJ with
    hc | hrem
  · exact .inl hc
  · rcases hrem with he | ⟨er⟩
    · exact .inr he
    · exact (original_tripleSix_point_ordinary_not_ru_at h structural D a t ht heven J hJ er.some).elim

/-- The quotient in the linear case is by the unchanged original field point. -/
theorem original_tripleSix_point_ordinary_module_structure_or_held_at
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
    (centerIn B = Vt ∧ Vt.subgroupOf B = center B ∧
      ∃ hn : (Vt.subgroupOf B).Normal, letI := hn
        Nonempty ((B ⧸ Vt.subgroupOf B) ≃* Matrix.PSL3Four.PSL)) ∨
      Nonempty ((J ⧸ center J) ≃* Held.He) := by
  rcases original_tripleSix_point_ordinary_module_structure_at h structural D a t ht heven J hJ with
    hc | hrem
  · exact .inl hc
  · rcases hrem with he | ⟨er⟩
    · exact .inr he
    · exact (original_tripleSix_point_ordinary_not_ru_at h structural D a t ht heven J hJ er.some).elim

end CFSG.Quasithin.Chapter12.Section07
