module
public import Theory.Representation.BinaryOffender.ActionImage
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Faithful action images above a simple quotient

If a representation kills the kernel of a simple quotient and has no global
fixed vectors, its kernel equals that quotient kernel. Mapping the action
kernel to the simple group leaves only the trivial-image alternative; the
full-image alternative would make the original action trivial. The first
isomorphism theorem then identifies the faithful action image with the
specified quotient, preserving every original group element.

This is the kernel step for the residual-moving replacement section in
DGS, Groups and Graphs (1985), 6.4, printed pp.120--121.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
namespace Representation
variable {H D W : Type*} [Group H] [Group D] [IsSimpleGroup D]
  [AddCommGroup W] [Module (ZMod 2) W] [Nontrivial W]

/-- A fixed-point-free nonzero action has the same kernel as its simple quotient. -/
theorem ker_eq_of_simple_quotient (ρ : Representation (ZMod 2) H W)
    (q : H →* D) (hq : Function.Surjective q) (hle : q.ker ≤ ρ.ker)
    (hf : fixedSpace ρ ⊤ = ⊥) : ρ.ker = q.ker := by
  have hnt : ρ.ker ≠ ⊤ := by
    intro ht
    have hall (w : W) : w = 0 := by
      have hw : w ∈ fixedSpace ρ ⊤ := by
        intro g
        have he : ρ g = 1 := by
          change g.val ∈ ρ.ker
          rw [ht]
          exact mem_top _
        change ρ g w = w
        rw [he]
        rfl
      simpa only [hf,Submodule.mem_bot] using hw
    obtain ⟨w,hw⟩ := exists_ne (0 : W)
    exact hw (hall w)
  let : (ρ.ker.map q).Normal := (inferInstance : ρ.ker.Normal).map q hq
  rcases (inferInstance : (ρ.ker.map q).Normal).eq_bot_or_eq_top with hb | ht
  · exact le_antisymm ((map_eq_bot_iff ρ.ker).mp hb) hle
  · have hh := congrArg (Subgroup.comap q) ht
    rw [comap_map_eq,comap_top,sup_eq_left.mpr hle] at hh
    exact (hnt hh).elim

/-- The literal faithful image is the specified simple quotient, with its original map retained. -/
theorem actionImage_equiv_of_simple_quotient (ρ : Representation (ZMod 2) H W)
    (q : H →* D) (hq : Function.Surjective q) (hle : q.ker ≤ ρ.ker)
    (hf : fixedSpace ρ ⊤ = ⊥) :
    ρ.ker = q.ker ∧ ∃ e : actionImage ρ ≃* D, ∀ h, e (actionHom ρ h) = q h := by
  have hk := ker_eq_of_simple_quotient ρ q hq hle hf
  have ha : (actionHom ρ).ker = q.ker := by
    change ρ.asGroupHom.rangeRestrict.ker = q.ker
    rw [MonoidHom.ker_rangeRestrict]
    have he : ρ.asGroupHom.ker = ρ.ker := by
      ext h
      exact ⟨fun hh => congrArg Units.val hh, fun hh => Units.ext hh⟩
    exact he.trans hk
  let e := (QuotientGroup.quotientKerEquivOfSurjective
    (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective).symm |>.trans
      ((QuotientGroup.quotientMulEquivOfEq ha).trans
        (QuotientGroup.quotientKerEquivOfSurjective q hq))
  refine ⟨hk,e,?_⟩
  intro h
  have hh := (QuotientGroup.quotientKerEquivOfSurjective
    (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective).symm_apply_apply
      (QuotientGroup.mk' (actionHom ρ).ker h)
  change e (actionHom ρ h) = q h
  dsimp only [e,MulEquiv.trans_apply]
  rw [show (QuotientGroup.quotientKerEquivOfSurjective (actionHom ρ)
    ρ.asGroupHom.rangeRestrict_surjective).symm (actionHom ρ h) =
    QuotientGroup.mk' (actionHom ρ).ker h from hh]
  rfl
end Representation
