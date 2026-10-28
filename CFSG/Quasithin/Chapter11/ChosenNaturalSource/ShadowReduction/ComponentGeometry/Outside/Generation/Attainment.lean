module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Witness.Equal
public import CFSG.Quasithin.ChapterE.GenerationKnownSimple

/-!
# Positive attained generation for the actual outside subgroups

Every subgroup of Gz containing the source involution has even order and
inherits the full KnownSimple SQTK hypothesis from this two-local group.
The proved E-generation existence theorem therefore supplies a positive
attained minimum, both for each H-star choice and for the explicit
R₁ O²(H) subgroup in the equal-component construction.

This removes the positive-lower-bound obligation in 11.4.4; it does not
assert its upper bound. The Hall generation argument, the upper bound for
the smaller subgroup, and the odd-extension construction remain with
qt-d-1222-shadow-component-witness. The preceding geometry and 11.3.2
premises retain the source producers named in Witness.Equal and their
final discharge owner qt-d-1222-shadow-components.

Source: Aschbacher--Smith, E.1.11--12 and 11.4.4--11.5.1,
printed pp.212--214 and778--779.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- A subgroup of the original point centralizer containing the involution
has a positive attained generation parameter. No attainment assumption is used. -/
theorem point_overgroup_generation_spec (h : Comparison.EarlierGeometry E)
    (J : Subgroup G) (hJz : J ≤ Gz E) (hzJ : E.z ∈ J) :
    0 < ChapterE.generationParameter J ∧
      ChapterE.IsEGenerated (ChapterE.generationParameter J) J := by
  have hlocal := E.input.source.simpleQTKE.twoLocal_sqtk
    (point_twoLocal E h.point_mem h.point_fixed h.point_ne_one)
  have hQ : IsSQTK KnownSimple.IsKnownSimple J :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hJz)).mp
      (hlocal.subgroup (J.subgroupOf (Gz E)))
  have heven : ¬ Odd (Nat.card J) := by
    apply Nat.not_odd_iff_even.mpr
    apply even_iff_two_dvd.mpr
    have hd := J.orderOf_dvd_natCard hzJ
    rwa [(point_involution E h.point_mem h.point_fixed h.point_ne_one).1] at hd
  exact ChapterE.source_generation_spec_knownSimple hQ (Classical.arbitrary _) heven

/-- The positive lower bound in 11.4.4 holds for every source-selected H. -/
theorem selected_generation_spec (h : Comparison.EarlierGeometry E)
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M) (hHz : E.H ≤ Gz E) :
    0 < ChapterE.generationParameter E.H ∧
      ChapterE.IsEGenerated (ChapterE.generationParameter E.H) E.H :=
  point_overgroup_generation_spec E h E.H hHz
    (hH.1.1.2 (D.le_sylow (E.V₁_le h.point_mem)))

variable (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H₀ : Subgroup G)

/-- The actual equal-component construction has attained positive parameters on
both H and R₁ O²(H). Their upper bound of one remains to be proved. -/
theorem ofFlag_equal_selected_positive_carrier
    (h : Comparison.EarlierGeometry (ofFlag S f X z H₀))
    (he : (ofFlag S f X z H₀).Kz = (ofFlag S f X z H₀).K)
    (hK : (ofFlag S f X z H₀).K = (ofFlag S f X z H₀).L₁)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H₀).point J →
      Proposition1132At D S (ofFlag S f X z H₀).point J) :
    ∃ H, H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      H ≤ Gz (ofFlag S f X z H₀) ∧ SelectedResidualAlternative (ofFlag S f X z H) ∧
      let J := (ofFlag S f X z H).R₁ ⊔ (pResidual 2 H).map H.subtype
      J ≤ H ∧ ¬ J ≤ normalizer (L : Set G) ∧
        Chapter1.IsSylowIn 2 (ofFlag S f X z H).R₁ J ∧
        (J.subgroupOf H).Normal ∧
        (pResidual 2 J).map J.subtype = (pResidual 2 H).map H.subtype ∧
        (0 < ChapterE.generationParameter H ∧
          ChapterE.IsEGenerated (ChapterE.generationParameter H) H) ∧
        (0 < ChapterE.generationParameter J ∧
          ChapterE.IsEGenerated (ChapterE.generationParameter J) J) := by
  obtain ⟨H,hH,hHz,hs,hJH,hJM,hSyl,hJY⟩ :=
    ofFlag_equal_selected_radical_carrier S f X z H₀ h he hK hNT h1132
  have h' : Comparison.EarlierGeometry (ofFlag S f X z H) :=
    ⟨h.point_mem,h.point_fixed,h.point_ne_one,h.seed_centralizes,
      h.line_component,h.point_component,h.normalizer_split⟩
  refine ⟨H,hH,hHz,hs,hJH,hJM,hSyl,
    radical_carrier_normal _ hH.1.1.2,radical_carrier_residual _ hH.1.1.2,
    selected_generation_spec _ h' hH hHz,?_⟩
  apply point_overgroup_generation_spec (ofFlag S f X z H₀) h _ (hJY.trans inf_le_left)
  exact mem_sup_left (f.seed_le_Ri S 0 ((ofFlag S f X z H₀).V₁_le h.point_mem))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside
