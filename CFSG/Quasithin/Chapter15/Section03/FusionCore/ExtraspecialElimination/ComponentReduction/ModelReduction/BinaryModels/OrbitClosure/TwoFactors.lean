module

public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# The two factors in a nontrivial component orbit

An index-two normalizer leaves exactly two conjugates. Conjugation permutes
those factors, and distinct quasisimple components commute. When the chosen
component is centerless their intersection is trivial. A moving element of
T then transports the commutator identity with Y to the second factor;
Y lies in their product whenever it lies in the T-conjugate span.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.504 and 1144, Proposition 1.2.1(3) and the proof of 15.3.49(l).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.OrbitClosure
variable {D : Type*} [Group D] [Finite D]

omit [Finite D] in
private theorem map_conj_mul (B : Subgroup D) (g t : D) :
    B.map (MulAut.conj (g * t)).toMonoidHom =
      (B.map (MulAut.conj t).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, mul_inv_rev, mul_assoc]

private theorem two_conjugate_pair (B : Subgroup D)
    (hi : (normalizer (B : Set D)).index = 2)
    (t : D) (ht : B.map (MulAut.conj t).toMonoidHom ≠ B) :
    let C := B.map (MulAut.conj t).toMonoidHom
    ∀ g : D,
      (B.map (MulAut.conj g).toMonoidHom = B ∧ C.map (MulAut.conj g).toMonoidHom = C) ∨
      (B.map (MulAut.conj g).toMonoidHom = C ∧ C.map (MulAut.conj g).toMonoidHom = B) := by
  classical
  dsimp only
  let C := B.map (MulAut.conj t).toMonoidHom
  let O := Set.range (fun g : D => B.map (MulAut.conj g).toMonoidHom)
  have hcard : O.ncard = 2 := (ncard_conjugates_eq_index_normalizer B).trans hi
  have hB : B ∈ O := ⟨1, by
    simp only [map_one]
    exact map_id B⟩
  have hC : C ∈ O := ⟨t, rfl⟩
  have hO : O = {B, C} := (Set.eq_of_subset_of_ncard_le (by
    intro X hX
    rcases hX with rfl | hX
    · exact hB
    · exact Set.mem_singleton_iff.mp hX ▸ hC) (by
      rw [hcard, Set.ncard_pair ht.symm])).symm
  intro g
  have hBg : B.map (MulAut.conj g).toMonoidHom = B ∨
      B.map (MulAut.conj g).toMonoidHom = C := by
    have h : B.map (MulAut.conj g).toMonoidHom ∈ O := ⟨g, rfl⟩
    simpa only [hO, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have hCg : C.map (MulAut.conj g).toMonoidHom = B ∨
      C.map (MulAut.conj g).toMonoidHom = C := by
    have h : C.map (MulAut.conj g).toMonoidHom ∈ O := ⟨g * t, map_conj_mul B g t⟩
    simpa only [hO, Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have hne : B.map (MulAut.conj g).toMonoidHom ≠ C.map (MulAut.conj g).toMonoidHom :=
    fun h => ht ((map_injective (MulAut.conj g).injective h).symm)
  rcases hBg with hBg | hBg <;> rcases hCg with hCg | hCg
  · exact (hne (hBg.trans hCg.symm)).elim
  · exact Or.inl ⟨hBg, hCg⟩
  · exact Or.inr ⟨hBg, hCg⟩
  · exact (hne (hBg.trans hCg.symm)).elim

/-- A centerless quasisimple component with two conjugates gives the genuine two-factor data. -/
theorem pair_of_two_orbit (B Y U : Subgroup D)
    (hB : IsComponent D B) (hz : center B = ⊥)
    (hi : (normalizer (B : Set D)).index = 2)
    (hmove : ¬ U ≤ normalizer (B : Set D))
    (hY : Y ≤ conjugateSpanBy B U) (hu : U ≤ normalizer (Y : Set D))
    (hgen : B = ⁅B, Y⁆) :
    ∃ C : Subgroup D, Disjoint B C ∧ B ≤ centralizer (C : Set D) ∧
      Y ≤ B ⊔ C ∧ B ≠ ⊥ ∧ C ≠ ⊥ ∧ C = ⁅C, Y⁆ ∧
      ∀ g : D,
        (B.map (MulAut.conj g).toMonoidHom = B ∧ C.map (MulAut.conj g).toMonoidHom = C) ∨
        (B.map (MulAut.conj g).toMonoidHom = C ∧ C.map (MulAut.conj g).toMonoidHom = B) := by
  classical
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hmove
  have hne : B.map (MulAut.conj t).toMonoidHom ≠ B :=
    fun he => htn (mem_normalizer_iff_map_conj_eq.mpr he)
  let C := B.map (MulAut.conj t).toMonoidHom
  have hC : IsComponent D C := hB.map_conj t
  have hc : ⁅B, C⁆ = ⊥ := hB.commutator_eq_bot_of_ne hC hne.symm
  have hbc := commutator_eq_bot_iff_le_centralizer.mp hc
  have hd : Disjoint B C := by
    apply Subgroup.disjoint_def.mpr
    intro x hxB hxC
    have hxz : (⟨x, hxB⟩ : B) ∈ center B := by
      apply mem_center_iff.mpr
      intro b
      apply Subtype.ext
      exact (hbc b.property x hxC).symm
    have hx1 : (⟨x, hxB⟩ : B) = 1 := mem_bot.mp (hz ▸ hxz)
    exact congrArg Subtype.val hx1
  have hpair := two_conjugate_pair B hi t hne
  have hspan : conjugateSpanBy B U ≤ B ⊔ C := by
    apply (closure_le _).mpr
    rintro x ⟨u, _, b, hb, rfl⟩
    have hm : u * b * u⁻¹ ∈ B.map (MulAut.conj u).toMonoidHom := ⟨b, hb, rfl⟩
    rcases hpair u with ⟨h, _⟩ | ⟨h, _⟩
    · exact mem_sup_left (h ▸ hm)
    · change B.map (MulAut.conj u).toMonoidHom = C at h
      exact mem_sup_right (h ▸ hm)
  have hBne : B ≠ ⊥ := by
    let _ := hB.2
    let _ : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
    have : Nontrivial B := (QuotientGroup.mk'_surjective (center B)).nontrivial
    exact (nontrivial_iff_ne_bot B).mp inferInstance
  have hCne : C ≠ ⊥ := fun he => hBne ((B.map_eq_bot_iff_of_injective (MulAut.conj t).injective).mp he)
  have hgenC : C = ⁅C, Y⁆ := by
    have he := congrArg (Subgroup.map (MulAut.conj t).toMonoidHom) hgen
    rw [map_commutator] at he
    have hy := mem_normalizer_iff_map_conj_eq.mp (hu ht)
    change Y.map (MulAut.conj t).toMonoidHom = Y at hy
    rwa [hy] at he
  exact ⟨C, hd, hbc, hY.trans hspan, hBne, hCne, hgenC, hpair⟩
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.OrbitClosure
