module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Mathlib.Algebra.Group.Pi.Lemmas

/-!
# Subnormal subgroups of powers of a simple group

A nontrivial subnormal subgroup of a direct power of a simple group has a
surjective coordinate projection. Consequently the order of the simple factor
divides the order of that subgroup.

For a quasisimple subnormal subgroup and a centerless simple factor, the
component dichotomy with a normal coordinate factor is stronger. Either the
component lies in that factor, or it centralizes it. The latter contradicts
the surjective projection and the trivial center. The projection is therefore
an isomorphism with the simple factor.

This is the direct-product component calculation used for the local sections
in Aschbacher–Smith, 2.3.9(7), printed p.526. The component dichotomy and its
source are in `GeneralizedFitting.ComponentCalculus`. No finiteness of the
index set or the groups is required for the isomorphism assertion.
-/

public section

open Subgroup Theory.GroupTheory

namespace Subgroup
variable {A ι : Type*} [Group A] [IsSimpleGroup A]

/-- Every nontrivial subnormal subgroup surjects onto a coordinate factor. -/
theorem exists_surjective_coordinate_of_isSubnormal (B : Subgroup (ι → A))
    (hB : B.IsSubnormal) (hne : B ≠ ⊥) :
    ∃ i : ι, Function.Surjective ((Pi.evalMonoidHom (fun _ : ι => A) i).comp B.subtype) := by
  obtain ⟨b, hb, hb1⟩ := B.bot_or_exists_ne_one.resolve_left hne
  obtain ⟨i, hi⟩ : ∃ i, b i ≠ 1 := by
    by_contra! hh
    exact hb1 (funext hh)
  let ev : (ι → A) →* A := Pi.evalMonoidHom (fun _ : ι => A) i
  have hev : Function.Surjective ev := fun x => ⟨fun _ => x, rfl⟩
  have ht : B.map ev = ⊤ := by
    rcases (hB.map hev).eq_bot_or_top_of_isSimpleGroup inferInstance with hbot | htop
    · have hh := mem_map_of_mem ev hb
      rw [hbot, mem_bot] at hh
      exact (hi hh).elim
    · exact htop
  refine ⟨i, ?_⟩
  intro a
  obtain ⟨b, hb, he⟩ := mem_map.mp (show a ∈ B.map ev from ht ▸ mem_top _)
  exact ⟨⟨b, hb⟩, he⟩

/-- The order of the simple factor divides the order of every nontrivial
subnormal subgroup of its direct power. -/
theorem card_dvd_of_isSubnormal_directPower (B : Subgroup (ι → A))
    (hB : B.IsSubnormal) (hne : B ≠ ⊥) : Nat.card A ∣ Nat.card B := by
  obtain ⟨i, hi⟩ := exists_surjective_coordinate_of_isSubnormal B hB hne
  exact card_dvd_of_surjective _ hi

end Subgroup

namespace Theory.GroupTheory
variable {A ι : Type*} [Group A] [IsSimpleGroup A]
/-- A component of a power of a centerless simple group is isomorphic to
one factor, using its actual coordinate projection. -/
theorem IsComponent.equiv_factor_of_directPower (hZ : center A = ⊥)
    {B : Subgroup (ι → A)} (hB : IsComponent (ι → A) B) : Nonempty (B ≃* A) := by
  classical
  let := hB.2
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  have hne : B ≠ ⊥ := by
    intro he
    have : Subsingleton B := he ▸ inferInstanceAs (Subsingleton (⊥ : Subgroup (ι → A)))
    exact not_subsingleton (B ⧸ center B) inferInstance
  obtain ⟨i, hi⟩ := B.exists_surjective_coordinate_of_isSubnormal hB.1 hne
  let ev : (ι → A) →* A := Pi.evalMonoidHom (fun _ : ι => A) i
  let single : A →* (ι → A) := MonoidHom.mulSingle (fun _ : ι => A) i
  have hn : single.range.Normal := by
    constructor
    rintro x ⟨a, rfl⟩ g
    refine ⟨g i * a * (g i)⁻¹, ?_⟩
    ext j
    by_cases hj : j = i
    · subst j
      simp [single]
    · simp [single, Pi.mulSingle_eq_of_ne hj]
  let := hn
  rcases hB.normal_dichotomy single.range with hle | hc
  · refine ⟨MulEquiv.ofBijective (ev.comp B.subtype) ⟨?_, hi⟩⟩
    intro x y hxy
    obtain ⟨a, ha⟩ := hle x.property
    obtain ⟨b, hb⟩ := hle y.property
    apply Subtype.ext
    rw [← ha, ← hb]
    apply congrArg single
    have he := hxy
    change (x : ι → A) i = (y : ι → A) i at he
    simpa [← ha, ← hb, single] using he
  · have hall : ∀ a : A, a ∈ center A := by
      intro a
      obtain ⟨b, hb⟩ := hi a
      apply mem_center_iff.mpr
      intro x
      have hh := mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc b.property)
        (single x) ⟨x, rfl⟩
      have he := congrFun hh i
      change (b : ι → A) i = a at hb
      simpa [single, hb] using he
    have : Subsingleton A := by
      apply subsingleton_of_forall_eq 1
      intro a
      exact mem_bot.mp (hZ ▸ hall a)
    exact (not_subsingleton A this).elim
end Theory.GroupTheory
