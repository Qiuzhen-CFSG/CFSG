module

public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.MaximalTwoLocalElementary
public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.ElementaryEight.CayleyFrame.LocalFamily
public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.CharacterGeometry.Decomposition

/-!
# Reduction of the ternary maximal-local cover to elementary subgroup geometry

A maximal two-local is the full normalizer of a nontrivial elementary
abelian two-subgroup. The actual octonion character decomposition proves
that its order divides eight, leaving three cases. Order-two subgroups are transported to the torus
involution line. An order-four subgroup must admit an elementary-eight
extension normalized by its WHOLE normalizer. The two conjugacy classes of
eights then give the two remaining representatives in `CayleyEight.localFamily`.

The three geometric hypotheses below are explicit, independent obligations;
this module does not yet discharge them or claim the source converse. The four-group
hypothesis retains normalizer containment, which an arbitrary extension does
not imply. All conjugation maps are actual inner automorphisms of the model.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(4), printed pp.3–4 and 481–482. The configurations on p.417
are recognition hypotheses, not an exhaustive maximal-local classification.
-/

namespace CFSG.Quasithin.MainConverse.ExceptionalLocal.TernaryCover

open Subgroup
open Atlas.G2 Atlas.G2.TernaryLocals

local notation "G" => Model (ZMod 3)

private theorem card_cases {E : Subgroup G} (hne : E ≠ ⊥)
    (hdiv : Nat.card E ∣ 8) : Nat.card E = 2 ∨ Nat.card E = 4 ∨ Nat.card E = 8 := by
  have hpos : 1 < Nat.card E := E.one_lt_card_iff_ne_bot.mpr hne
  have hle : Nat.card E ≤ 8 := Nat.le_of_dvd (by decide) hdiv
  interval_cases h : Nat.card E <;> simp_all

/-- Conjugacy of an actual elementary eight transports its full normalizer
to one of the two eight-normalizers in the enlarged family. -/
public theorem normalizer_cover_of_eight_conjugacy (E : Subgroup G)
    (hconj : ∃ g : G,
      E = elementary.map (MulAut.conj g).toMonoidHom ∨
      E = CayleyEight.elementary.map (MulAut.conj g).toMonoidHom) :
    ∃ (i : Fin 3) (g : G),
      normalizer (E : Set G) ≤ (CayleyEight.localFamily i).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg | hg⟩ := hconj
  · refine ⟨1, g, ?_⟩
    rw [hg, ← map_equiv_normalizer_eq]
    exact le_rfl
  · refine ⟨2, g, ?_⟩
    rw [hg, ← map_equiv_normalizer_eq]
    exact le_rfl

/-- The three independent elementary-subgroup branches suffice for the
complete maximal-two-local cover. The hypotheses still require proof. -/
public theorem maximalTwoLocal_threeFamily_cover_of_elementary_geometry
    (hbound : ∀ E : Subgroup G, IsElementaryAbelian 2 E → Nat.card E ∣ 8)
    (hline : ∀ E : Subgroup G, IsElementaryAbelian 2 E → Nat.card E = 2 →
      ∃ g : G, E = (zpowers involution).map (MulAut.conj g).toMonoidHom)
    (hfour : ∀ E : Subgroup G, IsElementaryAbelian 2 E → Nat.card E = 4 →
      ∃ F : Subgroup G, IsElementaryAbelian 2 F ∧ Nat.card F = 8 ∧
        E ≤ F ∧ normalizer (E : Set G) ≤ normalizer (F : Set G))
    (height : ∀ E : Subgroup G, IsElementaryAbelian 2 E → Nat.card E = 8 →
      ∃ g : G, E = elementary.map (MulAut.conj g).toMonoidHom ∨
        E = CayleyEight.elementary.map (MulAut.conj g).toMonoidHom)
    {M : Subgroup G} (hM : IsMaximalTwoLocal M) :
    ∃ (i : Fin 3) (g : G),
      M ≤ (CayleyEight.localFamily i).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨E, hne, hE, rfl⟩ :=
    Theory.GroupTheory.exists_elementary_normalizer_of_isMaximalTwoLocal hM
  rcases card_cases hne (hbound E hE) with h2 | h4 | h8
  · obtain ⟨g, hg⟩ := hline E hE h2
    refine ⟨0, g, ?_⟩
    rw [hg, ← map_equiv_normalizer_eq]
    exact le_rfl
  · obtain ⟨F, hF, hcF, _, hEF⟩ := hfour E hE h4
    obtain ⟨i, g, hg⟩ := normalizer_cover_of_eight_conjugacy F (height F hF hcF)
    exact ⟨i, g, hEF.trans hg⟩
  · exact normalizer_cover_of_eight_conjugacy E (height E hE h8)

/-- The octonion dimension theorem discharges the rank bound. Only the
three conjugacy and normalizer-extension branches remain for complete coverage. -/
public theorem maximalTwoLocal_threeFamily_cover_of_conjugacy_and_extension
    (hline : ∀ E : Subgroup G, IsElementaryAbelian 2 E → Nat.card E = 2 →
      ∃ g : G, E = (zpowers involution).map (MulAut.conj g).toMonoidHom)
    (hfour : ∀ E : Subgroup G, IsElementaryAbelian 2 E → Nat.card E = 4 →
      ∃ F : Subgroup G, IsElementaryAbelian 2 F ∧ Nat.card F = 8 ∧
        E ≤ F ∧ normalizer (E : Set G) ≤ normalizer (F : Set G))
    (height : ∀ E : Subgroup G, IsElementaryAbelian 2 E → Nat.card E = 8 →
      ∃ g : G, E = elementary.map (MulAut.conj g).toMonoidHom ∨
        E = CayleyEight.elementary.map (MulAut.conj g).toMonoidHom)
    {M : Subgroup G} (hM : IsMaximalTwoLocal M) :
    ∃ (i : Fin 3) (g : G),
      M ≤ (CayleyEight.localFamily i).map (MulAut.conj g).toMonoidHom := by
  apply maximalTwoLocal_threeFamily_cover_of_elementary_geometry
    (fun E hE => ?_) hline hfour height hM
  let _ := hE
  exact CharacterGeometry.elementary_card_dvd_eight E

end CFSG.Quasithin.MainConverse.ExceptionalLocal.TernaryCover
