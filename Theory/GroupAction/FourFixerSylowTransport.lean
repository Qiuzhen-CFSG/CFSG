module

public import Theory.GroupAction.AutomorphismFixerTransport
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Transport of four-group fixer containment to actual action images

Full automorphism Sylow containment descends to every actual homomorphism
image: an image of a Sylow subgroup is Sylow in the image, and its
intersection with a containing full Sylow subgroup is therefore unchanged.
The equivalence lemma retains both the specified four-group and its inner
embedding. These are the source maps needed in Aschbacher--Smith 2.5.8(5),
printed p.556.
-/

public section
open Subgroup
namespace Theory.GroupAction

/-- Membership in a containing full Sylow subgroup, together with membership
in the actual image, gives membership in the original Sylow image. -/
theorem mem_sylow_image_of_full_sylow {H A : Type*} [Group H] [Finite H]
    [Group A] [Finite A] (α : H →* A) (S : Sylow 2 H) (a : A)
    (ha : a ∈ α.range)
    (hfull : ∀ Q : Sylow 2 A, (S : Subgroup H).map α ≤ Q → a ∈ Q) :
    a ∈ (S : Subgroup H).map α := by
  obtain ⟨Q, hSQ⟩ := (S.isPGroup'.map α).exists_le_sylow
  let R := S.mapSurjective (f := α.rangeRestrict) α.rangeRestrict_surjective
  let T := (Q : Subgroup A).subgroupOf α.range
  have hRT : (R : Subgroup α.range) ≤ T := by
    rintro _ ⟨s, hs, rfl⟩
    exact hSQ (mem_map_of_mem α hs)
  have he : T = (R : Subgroup α.range) :=
    R.is_maximal' Q.isPGroup'.comap_subtype hRT
  have hat : (⟨a, ha⟩ : α.range) ∈ T := hfull Q hSQ
  rw [he] at hat
  obtain ⟨s, hs, heq⟩ := hat
  exact ⟨s, hs, congrArg Subtype.val heq⟩

/-- Pointwise fixer containment transports through a marked group equivalence. -/
theorem four_fixer_mem_sylow_of_equiv {K L : Type*} [Group K] [Finite K]
    [Group L] [Finite L] (e : K ≃* L)
    (hL : ∀ (P : Sylow 2 (MulAut L)) (F : Subgroup L), IsKleinFour F →
      F.map MulAut.conj ≤ P → ∀ a : MulAut L, (∀ x ∈ F, a x = x) → a ∈ P)
    (P : Sylow 2 (MulAut K)) (F : Subgroup K) [IsKleinFour F]
    (hFP : F.map MulAut.conj ≤ P) (a : MulAut K) (ha : ∀ x ∈ F, a x = x) :
    a ∈ P := by
  let E := F.map e.toMonoidHom
  let eF := F.equivMapOfInjective e.toMonoidHom e.injective
  have hE : IsKleinFour E := {
    card_four := (Nat.card_congr eF.toEquiv).symm.trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eF).symm.trans IsKleinFour.exponent_two }
  let c := MulAut.congr e
  let Q := P.mapSurjective (f := c.toMonoidHom) c.surjective
  have hc (x : K) : c (MulAut.conj x) = MulAut.conj (e x) := by
    ext y
    simp [c, MulAut.congr_apply]
  have hEQ : E.map MulAut.conj ≤ Q := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact hc x ▸ mem_map_of_mem c.toMonoidHom (hFP (mem_map_of_mem MulAut.conj hx))
  have hfix : ∀ x ∈ E, c a x = x := by
    rintro _ ⟨x, hx, rfl⟩
    change e (a (e.symm (e x))) = e x
    rw [e.symm_apply_apply, ha x hx]
  have hh := hL Q E hE hEQ (c a) hfix
  change c a ∈ (P : Subgroup (MulAut K)).map c.toMonoidHom at hh
  exact (mem_map_iff_mem c.injective).mp hh

end Theory.GroupAction
