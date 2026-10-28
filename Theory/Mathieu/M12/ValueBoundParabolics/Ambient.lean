module

public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.Automorphisms
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Faithful almost simple extensions of M₁₂

Conjugation embeds an ambient group with a self-centralizing normal M₁₂ into
the actual degree-24 full automorphism carrier. The embedding carries the
specified normal subgroup onto the marked inner subgroup. Since that subgroup
has index two, the ambient group is either M₁₂ or the full automorphism group.
No splitting or unproved automorphism-coverage premise is used.

This is the ambient reduction for Aschbacher–Smith E.4.3(1), printed p.241
(PDF p.252). The argument parallels the M₂₂ ambient reduction.
-/

public section
noncomputable section
namespace Sporadic.Mathieu.M12SmallPair.ValueBoundParabolics.Ambient
open Subgroup Sporadic.Mathieu.M12ExceptionalExtension
variable {X : Type*} [Group X]

/-- Conjugation on the specified component, in the actual extension carrier. -/
def ambientHom (S : Subgroup X) [S.Normal] (e : S ≃* M12) :
    X →* Carrier :=
  automorphismEquiv.symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := S)))

/-- Triviality of the relative centralizer makes conjugation faithful. -/
theorem ambientHom_injective (S : Subgroup X) [S.Normal] (e : S ≃* M12)
    (hc : centralizer (S : Set X) = ⊥) : Function.Injective (ambientHom S e) :=
  automorphismEquiv.symm.injective.comp ((MulAut.congr e).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot S hc))

/-- The embedding respects the prescribed identification on each inner element. -/
theorem ambientHom_apply_inner (S : Subgroup X) [S.Normal] (e : S ≃* M12) (s : S) :
    ambientHom S e s = innerModel.embedding (e s) := by
  apply automorphismEquiv.injective
  change automorphismEquiv (automorphismEquiv.symm ((MulAut.congr e)
    (MulAut.conjNormal (s : X)))) = _
  rw [MulEquiv.apply_symm_apply, MulAut.conjNormal_val, MulAut.congr_conj,
    automorphismEquiv_embedding]

/-- The component maps onto the literal marked inner subgroup. -/
theorem ambientHom_map_inner (S : Subgroup X) [S.Normal] (e : S ≃* M12) :
    S.map (ambientHom S e) = inner := by
  rw [← innerModel.embedding_range]
  ext g
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨e ⟨s, hs⟩, (ambientHom_apply_inner S e ⟨s, hs⟩).symm⟩
  · rintro ⟨s, rfl⟩
    refine ⟨e.symm s, (e.symm s).property, ?_⟩
    rw [ambientHom_apply_inner, e.apply_symm_apply]

/-- There is no proper intermediate subgroup above the index-two inner group. -/
theorem intermediate_eq_inner_or_top (R : Subgroup Carrier) (h : inner ≤ R) :
    R = inner ∨ R = ⊤ := by
  have hd : R.index ∣ 2 := inner_index ▸ index_dvd_of_le h
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hR | hR
  · exact Or.inr (index_eq_one.mp hR)
  · left
    have htower := relIndex_mul_index h
    rw [inner_index, hR] at htower
    have hi : inner.relIndex R = 1 := by omega
    exact (relIndex_eq_one.mp hi).antisymm h

/-- An actual ambient equivalence, retaining the marked inner subgroup. -/
theorem ambient_equiv_alternatives (S : Subgroup X) [S.Normal]
    (hc : centralizer (S : Set X) = ⊥) (e : S ≃* M12) :
    (S = ⊤ ∧ Nonempty (X ≃* M12)) ∨
      ∃ f : X ≃* Carrier, S.map f.toMonoidHom = inner := by
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

end Sporadic.Mathieu.M12SmallPair.ValueBoundParabolics.Ambient
