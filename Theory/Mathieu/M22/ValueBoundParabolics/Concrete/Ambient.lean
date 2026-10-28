module

public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.Geometry
public import Theory.Mathieu.M22.Properties.AutomorphismCoverage
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Faithful almost simple extensions of the concrete M₂₂

Conjugation embeds a group with a normal, centralizer-free M₂₂ subgroup
in the full design automorphism group. The embedding takes that normal
subgroup onto the actual even design automorphisms. Their index is two,
so the ambient group is either M₂₂ itself or the full design group.

The full automorphism coverage theorem supplies the model comparison;
no abstract group-family tag or maximal-subgroup list is used. This is the
ambient reduction for Aschbacher–Smith E.4.3(2), printed pp. 241–242.
-/

@[expose] public section
namespace Sporadic.Mathieu.M22ValueBound.Concrete
open Subgroup
variable {X : Type*} [Group X]

noncomputable def designAutEquiv : m22DesignAut ≃* MulAut M22 :=
  MulEquiv.ofBijective m22DesignAutToAut
    ⟨m22DesignAutToAut_injective, m22DesignAutToAut_surjective⟩

theorem designAutEquiv_inclusion (s : M22) :
    designAutEquiv (inclusion s) = MulAut.conj s := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change ((m22DesignAutToAut (inclusion s)) x : Equiv.Perm (Fin 22)) = _
  rw [m22DesignAutToAut_apply_perm]
  rfl

noncomputable def ambientHom (S : Subgroup X) [S.Normal] (e : S ≃* M22) :
    X →* m22DesignAut :=
  designAutEquiv.symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := S)))

theorem ambientHom_injective (S : Subgroup X) [S.Normal] (e : S ≃* M22)
    (hc : centralizer (S : Set X) = ⊥) : Function.Injective (ambientHom S e) :=
  designAutEquiv.symm.injective.comp ((MulAut.congr e).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot S hc))

theorem ambientHom_apply_inner (S : Subgroup X) [S.Normal] (e : S ≃* M22) (s : S) :
    ambientHom S e s = inclusion (e s) := by
  apply designAutEquiv.injective
  change designAutEquiv (designAutEquiv.symm ((MulAut.congr e)
    (MulAut.conjNormal (s : X)))) = _
  rw [MulEquiv.apply_symm_apply, MulAut.conjNormal_val, MulAut.congr_conj,
    designAutEquiv_inclusion]

theorem ambientHom_map_inner (S : Subgroup X) [S.Normal] (e : S ≃* M22) :
    S.map (ambientHom S e) = inner := by
  rw [← inclusion_range]
  ext g
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨e ⟨s, hs⟩, (ambientHom_apply_inner S e ⟨s, hs⟩).symm⟩
  · rintro ⟨s, rfl⟩
    refine ⟨e.symm s, (e.symm s).property, ?_⟩
    rw [ambientHom_apply_inner, e.apply_symm_apply]

theorem inner_index : inner.index = 2 := by
  have he : inner = m22EvenDesignAut := by
    ext g
    change g.val ∈ M22 ↔ g.val ∈ alternatingGroup (Fin 22)
    exact and_iff_right g.property
  rw [he, m22EvenDesignAut_index]

theorem intermediate_eq_inner_or_top (R : Subgroup m22DesignAut) (h : inner ≤ R) :
    R = inner ∨ R = ⊤ := by
  have hd : R.index ∣ 2 := inner_index ▸ index_dvd_of_le h
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hR | hR
  · exact Or.inr (index_eq_one.mp hR)
  · left
    have htower := relIndex_mul_index h
    rw [inner_index, hR] at htower
    have hi : inner.relIndex R = 1 := by omega
    exact (relIndex_eq_one.mp hi).antisymm h

theorem ambient_equiv_alternatives (S : Subgroup X) [S.Normal]
    (hc : centralizer (S : Set X) = ⊥) (e : S ≃* M22) :
    (S = ⊤ ∧ Nonempty (X ≃* M22)) ∨
      ∃ f : X ≃* m22DesignAut, S.map f.toMonoidHom = inner := by
  let f := ambientHom S e
  have hf : Function.Injective f := ambientHom_injective S e hc
  have hs : S.map f = inner := ambientHom_map_inner S e
  have hi : inner ≤ f.range := hs ▸ S.map_le_range f
  rcases intermediate_eq_inner_or_top f.range hi with hr | hr
  · left
    have hS : S = ⊤ := Subgroup.map_injective hf
      (hs.trans (hr.symm.trans (MonoidHom.range_eq_map f)))
    exact ⟨hS, ⟨((Subgroup.topEquiv.symm).trans (MulEquiv.subgroupCongr hS.symm)).trans e⟩⟩
  · have hsur : Function.Surjective f := MonoidHom.range_eq_top.mp hr
    exact Or.inr ⟨MulEquiv.ofBijective f ⟨hf, hsur⟩, hs⟩

end Sporadic.Mathieu.M22ValueBound.Concrete
