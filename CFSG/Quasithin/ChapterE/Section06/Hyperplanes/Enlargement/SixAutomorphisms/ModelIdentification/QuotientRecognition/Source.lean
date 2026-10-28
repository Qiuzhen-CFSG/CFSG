module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.Inputs
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent

/-!
# Smaller fixed centralizers retain the source component alternatives

Normality of Y inside C_G(A₁) makes C_Y(B) normal inside C_G(B) for
A₁ ≤ B. Its components therefore ascend to the ambient centralizer.
For an escaping B of corank at most two, the source m > 2 places B in Γ,
so every clause of E.6.8 and the seven-exclusion applies with the original
Q = C_T(V). Separately, the whole V-action fixes a Sylow subgroup of X.

Source: Aschbacher–Smith, E.6.5, E.6.8, E.6.18 and the further enlargement
in E.6.23, printed pp.246–254 (PDF pp.257–265).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen
open ComponentBalance
variable {G : Type*} [Group G] [Finite G] {M V U A L X Y : Subgroup G} {g : G}

omit [Finite G] in
/-- Relative normality, rather than ambient normality, suffices for component ascent. -/
theorem fixed_component_ascends
    (hY : NormalComponentExtension U A X g Y)
    {B Z : Subgroup G} (hB : intersection A U g ≤ B)
    (hZ : IsComponentIn Z (Y ⊓ centralizer (B : Set G))) :
    CentralizerComponent B Z := by
  have hCB : centralizer (B : Set G) ≤ centralizer (intersection A U g : Set G) :=
    Subgroup.centralizer_le hB
  have hnY : centralizer (B : Set G) ≤ normalizer (Y : Set G) :=
    hCB.trans ((normal_subgroupOf_iff_le_normalizer hY.component.1).mp hY.normal)
  have hN : ((Y ⊓ centralizer (B : Set G)).subgroupOf (centralizer (B : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer inf_le_right).mpr
      ((le_inf hnY (centralizer (B : Set G)).le_normalizer).trans
        inf_normalizer_le_normalizer_inf)
  exact hZ.of_subnormal inf_le_right hN.isSubnormal

/-- Apply the full earlier source list inside a smaller escaping centralizer. -/
theorem fixed_component_alternatives [IsElementaryAbelian 2 V]
    {T : Sylow 2 G} (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    (h15 : HypothesisE615 V) (earlier : EarlierResults T M V)
    (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y)
    {B Z : Subgroup G} (hB : intersection A U g ≤ B) (hBV : B ≤ V)
    (hcorank : subgroupCorank V B ≤ 2) (he : ¬ centralizer (B : Set G) ≤ M)
    (hZ : IsComponentIn Z (Y ⊓ centralizer (B : Set G))) :
    (¬ Z ≤ M ∧ Components.ComponentAlternatives M V B
      (sylowCentralizer (T : Subgroup G) V) Z) ∧ ¬ IsSeven Z := by
  have hm := (lemma_E_6_16_1 h h15 d.hyperplane d.hyperplane_mem.2.2.1).2.1
  have hmem := small_escape_mem h hBV (hcorank.trans_lt hm) he
  have hz := fixed_component_ascends hY hB hZ
  exact ⟨earlier.component_alternatives B hmem Z hz,
    earlier.seven_excluded B hmem hcorank Z hz⟩

/-- The full action fixes the original common Sylow intersection pointwise. -/
theorem whole_action_fixes_component_sylow [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y) :
    ∃ P : Sylow 2 X, (P : Subgroup X).map X.subtype =
      sylowCentralizer (T : Subgroup G) V ⊓ X ∧
      ∀ a ∈ actionImage V Y, ∀ x ∈ (P : Subgroup X),
        a (inclusion hY.proper.le x) = inclusion hY.proper.le x := by
  obtain ⟨P, hP⟩ := component_sylow h d
  refine ⟨P, hP, ?_⟩
  rintro a ⟨v, hv, rfl⟩ x hx
  apply Subtype.ext
  change (v : G) * (x : G) * (v : G)⁻¹ = (x : G)
  have hxp : (x : G) ∈ sylowCentralizer (T : Subgroup G) V := by
    have hh : (x : G) ∈ (P : Subgroup X).map X.subtype := mem_map_of_mem _ hx
    rw [hP] at hh
    exact hh.1
  exact mul_inv_eq_iff_eq_mul.mpr (((common_sylow h d).2.2 hv) _ hxp).symm

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen
