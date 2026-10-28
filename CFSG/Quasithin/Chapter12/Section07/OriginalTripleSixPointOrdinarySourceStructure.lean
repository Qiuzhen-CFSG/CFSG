module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointOrdinaryAt
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointOrdinaryOnlyHeld

/-!
# The original escaping point has the required structure or Held quotient

The literal centralizer-closure is supplied by the original source itself.
Its ordinary inspection identifies the original field point and quotient,
with only the actual Held central quotient left as an explicit alternative.
No selected component or recognition input is added.

Source: Aschbacher--Smith 12.7.5, printed p.840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The original escaping configuration supplies the actual ordinary closure
and its full field-point structure, with only Held still to exclude. -/
theorem original_tripleSix_point_structure_or_held_at
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
    IsComponent H (B.subgroupOf H) ∧
      ((centerIn B = Vt ∧ Vt.subgroupOf B = center B ∧
        ∃ hn : (Vt.subgroupOf B).Normal, letI := hn
          Nonempty ((B ⧸ Vt.subgroupOf B) ≃* Matrix.PSL3Four.PSL)) ∨
        Nonempty ((B ⧸ center B) ≃* Held.He)) := by
  let H := centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  let B := conjugateSpanBy Lt H
  have hOrd := original_tripleSix_point_ordinary_at h structural D a t ht heven hout
  change IsComponent H (B.subgroupOf H) ∧ _ at hOrd
  refine ⟨hOrd.1,?_⟩
  have hs := original_tripleSix_point_ordinary_module_structure_or_held_at
    h structural D a t ht heven (B.subgroupOf H) hOrd.1
  change (_ ∧ _ ∧ _) ∨ Nonempty (((B.subgroupOf H) ⧸ center (B.subgroupOf H)) ≃* Held.He) at hs
  rcases hs with hs | ⟨e⟩
  · exact .inl hs
  · have hBH : B ≤ H := conjugateSpanBy_le_self ((map_subtype_le _).trans inf_le_right)
    let f := subgroupOfEquivOfLe hBH
    have hc : (center (B.subgroupOf H)).map f.toMonoidHom = center B := by
      ext y
      constructor
      · rintro ⟨x,hx,rfl⟩
        exact (centerCongr f ⟨x,hx⟩).property
      · intro hy
        exact ⟨f.symm y,(centerCongr f.symm ⟨y,hy⟩).property,f.apply_symm_apply y⟩
    exact .inr ⟨(QuotientGroup.congr _ _ f hc).symm.trans e.some⟩

end CFSG.Quasithin.Chapter12.Section07
