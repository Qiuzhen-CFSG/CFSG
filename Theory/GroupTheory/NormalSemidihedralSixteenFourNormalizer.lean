module

public import Theory.GroupTheory.SemidihedralSixteenFours

/-!
# Four-group normalizers above a normal semidihedral sixteen

Conjugation preserves a normal SD16 subgroup and permutes its two elementary
four-subgroups. Therefore the normalizer of either four-group has index
dividing two in the overgroup. This applies directly to the inner Sylow
intersection in Aut(PSL₃(3)), without prescribing a splitting of its
outer action. Source: Aschbacher--Smith 2.5.8(5), printed p.556.
-/

public section
open Subgroup
namespace Semidihedral
variable {G : Type*} [Group G]

private theorem index_dvd_two_of_two_conjugates (E F : Subgroup G)
    (hcover : ∀ g : G, E.map (MulAut.conj g).toMonoidHom = E ∨
      E.map (MulAut.conj g).toMonoidHom = F) :
    (normalizer (E : Set G)).index ∣ 2 := by
  classical
  by_cases ht : normalizer (E : Set G) = ⊤
  · rw [ht, index_top]; exact one_dvd _
  obtain ⟨g, hg⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr ht)
  have hgN : g ∉ normalizer (E : Set G) := hg.2
  have hgF : E.map (MulAut.conj g).toMonoidHom = F :=
    (hcover g).resolve_left (fun h => hgN (mem_normalizer_iff_map_conj_eq.mpr h))
  apply (normalizer (E : Set G)).index_dvd_two_iff'.mpr
  refine ⟨g⁻¹, fun b => ?_⟩
  by_cases hb : b ∈ normalizer (E : Set G)
  · exact Or.inr hb
  · apply Or.inl
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hbF : E.map (MulAut.conj b).toMonoidHom = F :=
      (hcover b).resolve_left (fun h => hb (mem_normalizer_iff_map_conj_eq.mpr h))
    have hcomp : (MulAut.conj (g⁻¹ * b)).toMonoidHom =
        (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj b).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    change E.map (MulAut.conj (g⁻¹ * b)).toMonoidHom = E
    rw [hcomp, ← map_map, hbF, ← hgF, map_map]
    have hinv : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hinv, map_id]

/-- A normal SD16 contains at most two fours, so either four-normalizer
has index one or two in its whole overgroup. -/
theorem normalizer_index_dvd_two_of_normal_sixteen
    (D E : Subgroup G) [D.Normal] (e : D ≃* StandardModel 4 (by omega))
    [IsKleinFour E] (hED : E ≤ D) :
    (normalizer (E : Set G)).index ∣ 2 := by
  obtain ⟨F₀, F₁, hF⟩ := sixteen_four_cover e
  have hcover (U : Subgroup G) [IsKleinFour U] (hUD : U ≤ D) :
      U = F₀.map D.subtype ∨ U = F₁.map D.subtype := by
    let eU := subgroupOfEquivOfLe hUD
    have hU : IsKleinFour (U.subgroupOf D) := {
      card_four := (Nat.card_congr eU.toEquiv).trans IsKleinFour.card_four
      exponent_two := (Monoid.exponent_eq_of_mulEquiv eU).trans IsKleinFour.exponent_two }
    rcases hF (U.subgroupOf D) hU with h | h
    · exact Or.inl ((map_subgroupOf_eq_of_le hUD).symm.trans (congrArg (Subgroup.map D.subtype) h))
    · exact Or.inr ((map_subgroupOf_eq_of_le hUD).symm.trans (congrArg (Subgroup.map D.subtype) h))
  have hconj (g : G) : E.map (MulAut.conj g).toMonoidHom = F₀.map D.subtype ∨
      E.map (MulAut.conj g).toMonoidHom = F₁.map D.subtype := by
    let eE := E.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    let : IsKleinFour (E.map (MulAut.conj g).toMonoidHom) := {
      card_four := (Nat.card_congr eE.toEquiv).symm.trans IsKleinFour.card_four
      exponent_two := (Monoid.exponent_eq_of_mulEquiv eE).symm.trans IsKleinFour.exponent_two }
    apply hcover
    rintro _ ⟨x, hx, rfl⟩
    exact (inferInstance : D.Normal).conj_mem x (hED hx) g
  rcases hcover E hED with h | h
  · apply index_dvd_two_of_two_conjugates E (F₁.map D.subtype)
    intro g
    simpa only [← h] using hconj g
  · apply index_dvd_two_of_two_conjugates E (F₀.map D.subtype)
    intro g
    simpa only [← h, or_comm] using hconj g

end Semidihedral
