module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalSource.Sylow.Actor
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalSource.Sylow.RankOne
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalSource.Models

/-!
# The selected star image is Sylow in the actual residual

For the original active conjugate A = V^g ≤ T, the E.3.6 fixed-space family
has parameter n and gives |A*| ≥ 2ⁿ. An actor outside the normal rank-one
residual would act nontrivially on a normalized odd subgroup, contradicting
E.3.40. Thus A* ≤ K*, and the order of a Sylow two-subgroup of SL₂(2ⁿ)
forces equality with a Sylow subgroup of K*. The final equality uses the
literal star projection and residual inclusion, retaining the original g.
The source-flag application selects that same active conjugate using 11.3.3.

Source: Aschbacher--Smith 11.3.7, first proof paragraph, printed p.773
(combined manuscript, 1 March 2004). The explicit preceding-source inputs are
s(G,V) = n and K/O₂(K) ≅ PSL₂(2ⁿ), supplied by 11.2.2 and 11.3.5--6.
No natural-summand marking, A = V, or fixed-space vanishing is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- The original selected A* lies in K*, including the degree-two outer case. -/
theorem selected_star_le_residual
    (s : Hypothesis1131At D S U₁ H) (g : G)
    (hg : V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G))
    (ha : ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (omegaClosure T H : Set G))
    (hs : @ChapterE.globalS G _ V D.elementary = (S.field.degree : ℕ∞))
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree)) :
    ((V.map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H) ≤
      residualStar T H := by
  by_contra hnot
  let := ParameterComponent.omegaOrbit_elementary s
  have hf := selected_star_family s g hg ha hs
  obtain ⟨_,e,_⟩ := source_compatible_matrix_equivs s hmodel
  let : IsElementaryAbelian 2
      (((V.map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H)) := hf.2.1.2
  obtain ⟨R,_,hR,hn,hc⟩ := SylowPlacement.rankOne_odd_witness
    S.nonbinary S.field.card_eq (residualStar T H) e
    (source_star_core s) (source_star_residual_quotient_two s.outside.1.1.2)
    _ (selected_star_card_lower s g hg ha hs) hnot
  exact hc (selected_star_centralizes_odd s g hg ha hs R hR hn)

/-- Once placed in K*, the same image fills a Sylow subgroup by its order bound. -/
theorem selected_star_sylow_of_containment
    (s : Hypothesis1131At D S U₁ H) (g : G)
    (hg : V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G))
    (ha : ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (omegaClosure T H : Set G))
    (hs : @ChapterE.globalS G _ V D.elementary = (S.field.degree : ℕ∞))
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree))
    (hAK : ((V.map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H) ≤
      residualStar T H) :
    ∃ R : Sylow 2 (residualStar T H),
      (R : Subgroup (residualStar T H)).map (residualStar T H).subtype =
        ((V.map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H) := by
  let := ParameterComponent.omegaOrbit_elementary s
  let A := ((V.map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H)
  let : IsElementaryAbelian 2 A := (selected_star_family s g hg ha hs).2.1.2
  obtain ⟨R,hR⟩ := ((IsElementaryAbelian.isPGroup 2 A).comap_subtype
    (K := residualStar T H)).exists_le_sylow
  have hle : A ≤ (R : Subgroup (residualStar T H)).map (residualStar T H).subtype := by
    intro a ha
    exact ⟨⟨a,hAK ha⟩,hR ha,rfl⟩
  obtain ⟨_,e,_⟩ := source_compatible_matrix_equivs s hmodel
  let P := R.mapSurjective (f := e.toMonoidHom) e.surjective
  have hcard : Nat.card ((R : Subgroup (residualStar T H)).map (residualStar T H).subtype) =
      Nat.card S.field.Carrier := calc
    _ = Nat.card R := card_map_of_injective (residualStar T H).subtype_injective
    _ = Nat.card P := Nat.card_congr
      ((R : Subgroup (residualStar T H)).equivMapOfInjective e.toMonoidHom e.injective).toEquiv
    _ = Nat.card S.field.Carrier := (Nat.card_congr
      (Matrix.SpecialLinearGroup.sylowEquivAdditive S.field.Carrier 2 P).toEquiv).symm
  refine ⟨R,(eq_of_le_of_card_ge hle ?_).symm⟩
  rw [hcard]
  exact selected_star_card_lower s g hg ha hs

/-- The selected image is a Sylow subgroup of the actual residual image.
Only the preceding parameter equality and residual recognition remain inputs. -/
theorem selected_star_sylow
    (s : Hypothesis1131At D S U₁ H) (g : G)
    (hg : V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G))
    (ha : ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (omegaClosure T H : Set G))
    (hs : @ChapterE.globalS G _ V D.elementary = (S.field.degree : ℕ∞))
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree)) :
    ∃ R : Sylow 2 (residualStar T H),
      (R : Subgroup (residualStar T H)).map (residualStar T H).subtype =
        ((V.map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H) :=
  selected_star_sylow_of_containment s g hg ha hs hmodel
    (selected_star_le_residual s g hg ha hs hmodel)

/-- Select the original active conjugate on the actual source flag, retaining
both its activity and its literal Sylow placement. -/
theorem exists_selected_star_sylow
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (s : Hypothesis1131At D S (c.binarySubspace (f.space 0)) H)
    (p : Preceding1133 D S (c.binarySubspace (f.space 0)) H)
    (hcounter : ¬ Proposition1132At D S (c.binarySubspace (f.space 0)) H)
    (hs : @ChapterE.globalS G _ V D.elementary = (S.field.degree : ℕ∞))
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree)) :
    ∃ g : G, V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
      ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (omegaClosure T H : Set G) ∧
      ∃ R : Sylow 2 (residualStar T H),
        (R : Subgroup (residualStar T H)).map (residualStar T H).subtype =
          ((V.map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H) := by
  obtain ⟨g,hg,ha⟩ := ParameterComponent.exists_active_conjugate s p hcounter
  have ha' : ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (omegaClosure T H : Set G) := by
    simpa only [omegaClosure_eq_parameterOrbit] using ha
  exact ⟨g,hg,ha',selected_star_sylow s g hg ha' hs hmodel⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
