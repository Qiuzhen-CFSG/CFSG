module

public import Theory.GroupTheory.CommutingPerfectRank
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.CComponentCommutation.FromStructure

/-!
# The orbit part of A.3.8 from C-component commutation

A.3.7 makes distinct C-components commute. Three conjugates of one
nontrivial perfect component would consequently give odd prime rank at
least three. Thus its normalizer has index one or two. This argument does
not identify the component or use any ordinary-cover multiplier row.

The genuine noncentral structural input is retained, with final discharge
belonging to `qt-a03-noncentral-fitting-structure`. The complete model
conclusions of A.3.8 remain with `qt-a03-sqtk-structure`.

Source: Aschbacher--Smith A.3.7 and A.3.8(3), printed pp.45--46.
-/

public section
namespace CFSG.Quasithin.ChapterA.Section03.ComponentOrbitBound
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The full normal-or-index-two orbit bound needs only noncentral A.3.6
through the proved A.3.7 implication, with no model-classification input. -/
theorem normal_or_index_two_of_noncentral_structure
    {κ : GroupClass.{u}}
    (h36 : CComponentCommutation.NoncentralStructureInput κ)
    (hG : IsSQTK κ G) (hO : pCore 2 G = ⊥)
    {B : Subgroup G} (hB : B.IsCComponent) :
    B.Normal ∨ (normalizer (B : Set G)).index = 2 := by
  classical
  by_cases hn : B.Normal
  · exact Or.inl hn
  have hex : ∃ g : G, B.map (MulAut.conj g).toMonoidHom ≠ B := by
    by_contra! h
    exact hn (normal_iff_map_conj_eq.mpr h)
  obtain ⟨g, hg⟩ := hex
  let C := B.map (MulAut.conj g).toMonoidHom
  have hC : C.IsCComponent := hB.map_equiv (MulAut.conj g)
  have hBC : B ≠ C := hg.symm
  have hcomm (D E : Subgroup G) (hD : D.IsCComponent) (hE : E.IsCComponent)
      (hne : D ≠ E) : D ≤ centralizer (E : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (CComponentCommutation.commutator_eq_bot_of_noncentral_structure
        h36 hG hO D E hD hE hne)
  have hpair (t : G) :
      B.map (MulAut.conj t).toMonoidHom = B ∨
        B.map (MulAut.conj t).toMonoidHom = C := by
    let D := B.map (MulAut.conj t).toMonoidHom
    by_cases hDB : D = B
    · exact Or.inl hDB
    by_cases hDC : D = C
    · exact Or.inr hDC
    have hD : D.IsCComponent := hB.map_equiv (MulAut.conj t)
    have h₀₁ := hcomm B C hB hC hBC
    have h₀₂ := hcomm B D hB hD (fun he => hDB he.symm)
    have h₁₂ := hcomm C D hC hD (fun he => hDC he.symm)
    have : Group.IsPerfect B := hB.perfect
    have : Nontrivial B := (nontrivial_iff_ne_bot B).mpr hB.ne_bot
    let f₁ : B →* G := (MulAut.conj g).toMonoidHom.comp B.subtype
    let f₂ : B →* G := (MulAut.conj t).toMonoidHom.comp B.subtype
    obtain ⟨p, hp, ho, hr⟩ :=
      CommutingPerfectRank.exists_odd_prime_rank_three_of_commuting_perfect
        B.subtype f₁ f₂ B.subtype_injective
        ((MulAut.conj g).injective.comp B.subtype_injective)
        ((MulAut.conj t).injective.comp B.subtype_injective)
        (fun x y => (h₀₁ x.property (f₁ y)
          (mem_map_of_mem (MulAut.conj g).toMonoidHom y.property)).symm)
        (fun x y => (h₀₂ x.property (f₂ y)
          (mem_map_of_mem (MulAut.conj t).toMonoidHom y.property)).symm)
        (fun x y => (h₁₂ (mem_map_of_mem (MulAut.conj g).toMonoidHom x.property)
          (f₂ y) (mem_map_of_mem (MulAut.conj t).toMonoidHom y.property)).symm)
    have hu := hG.stronglyQuasithin p hp ho
    omega
  have hsub : (Set.range fun g : G => B.map (MulAut.conj g).toMonoidHom) ⊆ {B, C} := by
    rintro _ ⟨t, rfl⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hpair t
  have hi : (normalizer (B : Set G)).index ≤ 2 := by
    rw [← ncard_conjugates_eq_index_normalizer]
    exact (Set.ncard_le_ncard hsub).trans_eq (Set.ncard_pair hBC)
  have hnt : normalizer (B : Set G) ≠ ⊤ :=
    fun h => hn (normalizer_eq_top_iff.mp h)
  have hlo := (normalizer (B : Set G)).one_lt_index_of_ne_top hnt
  exact Or.inr (by omega)

end CFSG.Quasithin.ChapterA.Section03.ComponentOrbitBound
