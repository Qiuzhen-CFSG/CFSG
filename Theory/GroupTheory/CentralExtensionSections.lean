module
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Mathlib.GroupTheory.SchurZassenhaus

/-!
# Sections of prescribed central extensions

The derived subgroup of a central extension of a perfect group is a
perfect central cover. If the base is itself a universal quasisimple
covering group, universality lifts it into this derived cover; uniqueness
of maps out of a perfect group makes the composite the identity.
Schur–Zassenhaus supplies the corresponding section when kernel and base
have coprime orders, without a perfectness hypothesis.

These are the ordinary and small-field splitting steps in Aschbacher–Smith,
*The Classification of Quasithin Groups*, A.2.17, printed p.39.
-/

public section
open Subgroup Theory.GroupTheory
namespace CentralExtension
universe u v w

/-- Restrict a central extension of a perfect group to its derived subgroup. -/
@[expose] def derivedCover {E B : Type*} [Group E] [Group B] [Group.IsPerfect B]
    (f : E →* B) (hf : Function.Surjective f) (hc : f.ker ≤ center E) :
    PerfectCentralCovering.Cover (commutator E) B where
  toMonoidHom := f.comp (commutator E).subtype
  surjective := by
    have hm : (commutator E).map f = ⊤ := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
      exact Group.IsPerfect.commutator_eq_top
    intro b
    obtain ⟨x, hx, hxb⟩ := hm ▸ (show b ∈ (⊤ : Subgroup B) from mem_top b)
    exact ⟨⟨x, hx⟩, hxb⟩
  isPerfect := PerfectCentralCovering.commutator_isPerfect_of_surjective_of_ker_le_center f hf hc
  ker_le_center := fun x hx => mem_center_iff.mpr fun y =>
    Subtype.ext (mem_center_iff.mp (hc hx) y)

/-- A finite central extension of a universal quasisimple covering group splits,
with a section of the given map. -/
theorem exists_section_of_universal_cover
    {E : Type u} {B : Type v} {C : Type w} [Group E] [Finite E] [Group B] [Finite B]
    [IsQuasisimple B] [Group C] [Finite C] [IsQuasisimple C]
    (g : Covering B C) (hg : Covering.IsUniversal.{w, v, u} g)
    (f : E →* B) (hf : Function.Surjective f) (hc : f.ker ≤ center E) :
    ∃ s : B →* E, f.comp s = MonoidHom.id B := by
  let d := derivedCover f hf hc
  let : IsQuasisimple (commutator E) := d.isQuasisimple
  let l := hg.lift (g.comp d.toCovering)
  have he : d.toMonoidHom.comp l.toMonoidHom = MonoidHom.id B := by
    apply PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq
      g.toMonoidHom g.ker_le_center
    have h := congrArg Covering.toMonoidHom (hg.lift_fac (g.comp d.toCovering))
    ext b
    exact DFunLike.congr_fun h b
  exact ⟨(commutator E).subtype.comp l.toMonoidHom, he⟩

/-- Schur–Zassenhaus gives a section of the prescribed surjection when its
kernel order is coprime to the base order. -/
theorem exists_section_of_coprime_kernel
    {E B : Type*} [Group E] [Finite E] [Group B]
    (f : E →* B) (hf : Function.Surjective f)
    (hc : Nat.Coprime (Nat.card f.ker) (Nat.card B)) :
    ∃ s : B →* E, f.comp s = MonoidHom.id B := by
  have hi : f.ker.index = Nat.card B := by
    rw [index_ker, MonoidHom.range_eq_top.mpr hf, card_top]
  obtain ⟨D, hD⟩ := exists_right_complement'_of_coprime (hi.symm ▸ hc)
  let d : D →* B := f.comp D.subtype
  have hdi : Function.Injective d := by
    apply (MonoidHom.ker_eq_bot_iff d).mp
    apply bot_unique
    intro x hx
    exact Subtype.ext (hD.disjoint.le_bot ⟨hx, x.property⟩)
  have hds : Function.Surjective d := by
    intro b
    obtain ⟨x, rfl⟩ := hf b
    obtain ⟨⟨k, y⟩, hxy⟩ := hD.2 x
    refine ⟨y, ?_⟩
    change f y = f x
    rw [← hxy, map_mul, MonoidHom.mem_ker.mp k.property, one_mul]
  let e := MulEquiv.ofBijective d ⟨hdi, hds⟩
  refine ⟨D.subtype.comp e.symm.toMonoidHom, ?_⟩
  ext b
  exact e.apply_symm_apply b

end CentralExtension
