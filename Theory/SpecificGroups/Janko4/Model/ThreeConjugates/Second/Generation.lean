module
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates
public import Mathlib.Algebra.Group.Subgroup.Finite
/-!
# Generation by an ambient conjugate of the standard pair

An injective matrix representation lets us compare the finite group with a
subgroup containing an ambient conjugate of its generating pair. Conjugation
embeds the whole group into that subgroup, so finite cardinality forces equality.
The actual pair and invertible change of basis are certified in `Second`.
-/

public section
namespace Janko4.ThreeConjugates.SecondCertificate
attribute [local irreducible] modelGroup matrixA matrixB

theorem eq_top_of_ambient_conjugate_pair {G A : Type*} [Group G] [Group A] [Finite G]
    (ι : G →* A) (hι : Function.Injective ι)
    (a b : G) (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (H : Subgroup G) (t : A) (u v : G) (hu : u ∈ H) (hv : v ∈ H)
    (ha : t⁻¹ * ι a * t = ι u)
    (hb : t⁻¹ * ι b * t = ι v) : H = ⊤ := by
  let f : G →* A := (MulAut.conj t⁻¹).toMonoidHom.comp ι
  have hfa : f a = ι u := by
    simpa only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv] using ha
  have hfb : f b = ι v := by
    simpa only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv] using hb
  have hle : (⊤ : Subgroup G) ≤ (H.map ι).comap f := by
    rw [← hgen]
    apply (Subgroup.closure_le _).mpr
    intro z hz
    rcases Set.mem_insert_iff.mp hz with haz | hz
    · subst z
      change f a ∈ H.map ι
      rw [hfa]
      exact Subgroup.mem_map_of_mem _ hu
    · have hz' : z = b := Set.mem_singleton_iff.mp hz
      subst z
      change f b ∈ H.map ι
      rw [hfb]
      exact Subgroup.mem_map_of_mem _ hv
  let F : G → H.map ι := fun z => ⟨f z, hle (Subgroup.mem_top z)⟩
  have hF : Function.Injective F := by
    intro z w h
    apply hι
    apply (MulAut.conj t⁻¹).injective
    change f z = f w
    exact congrArg (fun q : H.map ι => (q : A)) h
  let : Finite (H.map ι) := Finite.of_equiv H
    (H.equivMapOfInjective ι hι).toEquiv
  have hc : Nat.card G ≤ Nat.card (H.map ι) :=
    Nat.card_le_card_of_injective F hF
  rw [Subgroup.card_map_of_injective hι] at hc
  exact H.eq_top_of_le_card hc
end Janko4.ThreeConjugates.SecondCertificate
