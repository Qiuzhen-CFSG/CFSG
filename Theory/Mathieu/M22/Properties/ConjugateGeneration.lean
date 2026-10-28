module

public import Theory.Mathieu.M22.Properties.ConjugateGeneration.Generation
public import Theory.Mathieu.M22.Properties.AutomorphismCoverage

/-!
# Three inner and four ambient conjugates for M₂₂

Three conjugates of every involution in the concrete M₂₂ generate the group.
For every involutory automorphism, four conjugates by actual M₂₂ elements
generate a subgroup containing all inner automorphisms. The finite word
certificates are exhaustive on a proved Sylow subgroup of the design group;
the faithful, surjective design action then covers abstract automorphisms.

Source: Guralnick–Malle, Classification of 2F-modules I, Proposition 5.1,
manuscript pp.15–16. The four-conjugate assertion includes both outer classes;
no three-conjugate claim is made for those classes.
-/

public section
namespace Sporadic.Mathieu.M22ConjugateGeneration
open Subgroup M22ValueBound.Concrete

/-- Mapping retains the literal list of conjugate generators. -/
theorem map_conjugate_closure {A B : Type*} [Group A] [Group B]
    (f : A →* B) (t : A) {n : ℕ} (c : Fin n → A) :
    (closure (Set.range fun i => c i * t * (c i)⁻¹)).map f =
      closure (Set.range fun i => f (c i) * f t * (f (c i))⁻¹) := by
  rw [MonoidHom.map_closure, ← Set.range_comp]
  congr 2
  funext i
  simp only [Function.comp_apply, map_mul, map_inv]

/-- Faithful maps reflect the required subgroup containment. -/
theorem le_conjugate_closure_of_map {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Injective f) (L : Subgroup A)
    (t : A) {n : ℕ} (c : Fin n → A)
    (h : L.map f ≤ closure (Set.range fun i => f (c i) * f t * (f (c i))⁻¹)) :
    L ≤ closure (Set.range fun i => c i * t * (c i)⁻¹) := by
  apply (Subgroup.map_le_map_iff_of_injective hf).mp
  rwa [map_conjugate_closure]

theorem inclusion_automorphism (x : M22) :
    m22DesignAutToAut (inclusion x) = MulAut.conj x := by
  apply MulEquiv.ext
  intro y
  apply Subtype.ext
  exact m22DesignAutToAut_apply_perm (inclusion x) y

end M22ConjugateGeneration

open Subgroup M22ValueBound.Concrete M22ConjugateGeneration

/-- Three actual M₂₂-conjugates of any inner involution generate M₂₂. -/
theorem m22_three_conjugates_generate (t : M22) (ht : orderOf t = 2) :
    ∃ c : Fin 3 → M22, closure (Set.range fun i => c i * t * (c i)⁻¹) = ⊤ := by
  obtain ⟨c, hc⟩ := design_three (inclusion t)
    ((orderOf_injective inclusion inclusion_injective t).trans ht) t.property
  refine ⟨c, top_unique ?_⟩
  apply le_conjugate_closure_of_map inclusion inclusion_injective ⊤ t c
  simpa only [← MonoidHom.range_eq_map, M22ValueBound.Concrete.inclusion_range] using hc

/-- Four inner conjugates of an involutory automorphism contain every inner automorphism. -/
theorem m22_four_conjugates_automorphisms (a : MulAut M22) (ha : orderOf a = 2) :
    ∃ c : Fin 4 → M22, (MulAut.conj : M22 →* MulAut M22).range ≤
      closure (Set.range fun i => MulAut.conj (c i) * a * (MulAut.conj (c i))⁻¹) := by
  obtain ⟨s, rfl⟩ := m22DesignAutToAut_surjective a
  obtain ⟨c, hc⟩ := design_four s (by
    rwa [orderOf_injective m22DesignAutToAut m22DesignAutToAut_injective] at ha)
  refine ⟨c, ?_⟩
  have hmap := Subgroup.map_mono (f := m22DesignAutToAut) hc
  have hr : M22ValueBound.Concrete.inner.map m22DesignAutToAut = (MulAut.conj : M22 →* MulAut M22).range := by
    rw [← M22ValueBound.Concrete.inclusion_range, MonoidHom.map_range]
    congr 1
    apply MonoidHom.ext
    exact inclusion_automorphism
  rw [hr, map_conjugate_closure] at hmap
  simpa only [inclusion_automorphism] using hmap

end Sporadic.Mathieu
